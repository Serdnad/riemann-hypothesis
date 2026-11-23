module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelChainSharpColumnValuationOwnChainIff
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
public import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle058
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Proof.SelfDualStabilizer

open scoped TensorProduct Pointwise
open NumberField IsDedekindDomain
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

theorem unramifiedAtFinite_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.UnramifiedAtFinite F E ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.UnramifiedAtFinite F E := by
  constructor
  · intro h P hP hne
    exact h ⟨P, hP, hne⟩
  · intro h P
    exact @h P.asIdeal P.isPrime P.ne_bot

section Clauses

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)


omit [NumberField F] [NumberField E] in
theorem isSelfDualLattice_iff (L : Submodule (𝓞 E) (Fin M → E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.IsSelfDualLattice σ J L ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.IsSelfDualLat σ J L := Iff.rfl


omit [NumberField F] [NumberField E] in
theorem perpPart_eq (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.perpPart σ J (L : Set (Fin M → E)) x = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.perpIn σ J L x := rfl


omit [NumberField E] in
theorem stabHat_eq (S : Set (Fin M → E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.stabHat σ J S = GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.stabLat (Af F) σ J (latHat F E S) :=
  Subgroup.ext fun _ => Iff.rfl


omit [NumberField E] in
theorem orbitClaims_iff (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) (β : F) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.OrbitClaims σ J (L : Set (Fin M → E)) x β ↔
      GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.OrbitConcl F E σ J L x β := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.OrbitClaims GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.OrbitConcl
  rw [stabHat_eq, stabHat_eq, perpPart_eq]
  exact Iff.rfl

end Clauses

theorem stabTransitive_iff :
    GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.StabTransitive ↔ GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeOrthogonalParts.StabTransitive GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive
  refine forall_congr' fun F => forall_congr' fun E => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun σ => imp_congr_right fun _ => ?_
  refine imp_congr (unramifiedAtFinite_iff F E) ?_
  refine forall_congr' fun M => forall_congr' fun J => imp_congr_right fun _ =>
    forall_congr' fun L => imp_congr (isSelfDualLattice_iff σ J L) ?_
  exact forall_congr' fun β => imp_congr_right fun _ => forall_congr' fun x =>
    imp_congr_right fun _ => imp_congr_right fun _ => orbitClaims_iff σ J L x β

end GlobalTheory.Proof.SelfDualStabilizer
end
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.SecondFunctional

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}

theorem mem_primeOf_prPbar {σ : E →ₐ[F] E}
    {φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F}
    (hφ : IsSplitting σ v φ) (a : intV E v) :
    a ∈ primeOf (prPbar φ) ↔ Valued.v (prPbar φ a) < 1 := by
  refine ⟨fun h => ?_, fun h => Ideal.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    have hc : Valued.v (prPbar φ c) ≤ 1 := ((hφ.2.2 c).1 c.2).2
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hc zero_le' hx

theorem exists_max {ι : Type} (g : ι → WithZero (Multiplicative ℤ)) (t : WithZero (Multiplicative ℤ))
    (ht : t ≠ 0) (hb : ∀ y, t * g y ≤ 1) (y₁ : ι) (h₁ : g y₁ ≠ 0) : ∃ y₀, ∀ y, g y ≤ g y₀ := by
  obtain ⟨n, ⟨y₀, hy₀⟩, hn⟩ := Int.exists_greatest_of_bdd (P := fun n => ∃ y, g y = WithZero.exp n)
    ⟨-WithZero.log t, fun z ⟨y, hy⟩ => by
      have := hb y
      rw [hy, ← WithZero.exp_log ht, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
      omega⟩ ⟨_, y₁, (WithZero.exp_log h₁).symm⟩
  refine ⟨y₀, fun y => ?_⟩
  by_cases hy : g y = 0
  · rw [hy]; exact zero_le'
  · rw [hy₀, ← WithZero.exp_log hy, WithZero.exp_le_exp]
    exact hn _ ⟨y, (WithZero.exp_log hy).symm⟩

theorem hform_add_right {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y z : n → A) : hform σ J x (y + z) = hform σ J x y + hform σ J x z := by
  simp [hform, mul_add, Finset.sum_add_distrib]

theorem hform_smul_right {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y : n → A) (a : A) : hform σ J x (a • y) = a * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_nsmul_left {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y : n → A) (T : ℕ) : hform σ J (T • x) y = T * hform σ J x y := by
  simp only [hform, Finset.mul_sum, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring



theorem exists_second_functional :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), IsSplitting σ v s → ∀ (k : ℕ) (J : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) (L₁ L₂ : Submodule (intV E v) (Fin k → E ⊗[F] v.adicCompletion F)), (∀ y ∈ L₁, ∀ x ∈ L₂, hform (sigR σ (v.adicCompletion F)) J x y ∈ intV E v) → (∀ x, x ∈ L₁ ↔ ∀ y ∈ L₂, hform (sigR σ (v.adicCompletion F)) J x y ∈ intV E v) → ∀ (T : ℕ), T ≠ 0 → (∀ x ∈ L₂, T • x ∈ L₁) → (∃ x ∈ L₂, x ∉ L₁ ∧ ∀ i, prPbar s (x i) = 0) → ∃ f : L₂ →ₗ[intV E v] (intV E v ⧸ primeOf (prPbar s)), Function.Surjective f ∧ (∀ x : L₂, x.1 ∈ L₁ → f x = 0) ∧ ∀ x : L₂, (∀ i, prPbar s (x.1 i) = 0) → f x = 0 := by
  intro F E _ _ _ _ _ σ v s hs k J L₁ L₂ h1 h2 T hT hTL ⟨x, hx2, hx1, hx0⟩
  obtain ⟨H, hH⟩ : ∃ H : (Fin k → E ⊗[F] v.adicCompletion F) → E ⊗[F] v.adicCompletion F,
    ∀ y, H y = hform (sigR σ (v.adicCompletion F)) J x y := ⟨_, fun _ => rfl⟩
  have e2 : ∀ a, prPbar s a = (s a).2 := fun _ => rfl
  have hfst : ∀ y, (s (H y)).1 = 0 := by
    intro y
    have : ∀ i, prP s (sigR σ (v.adicCompletion F) (x i)) = 0 := fun i =>
      (congrArg Prod.fst (hs.2.1 (x i))).trans (hx0 i)
    show prP s (H y) = 0

    simp only [hH, hform, map_sum, map_mul, this, zero_mul, Finset.sum_const_zero]
  have hTK : (T : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hT)
  obtain ⟨y₁, hy₁, hy₁'⟩ : ∃ y ∈ L₂, H y ∉ intV E v := by
    by_contra hc
    push_neg at hc
    exact hx1 ((h2 x).2 fun y hy => hH y ▸ hc y hy)
  have hgt : 1 < Valued.v (prPbar s (H y₁)) := by
    by_contra hc
    exact hy₁' ((hs.2.2 _).2 ⟨by rw [hfst]; exact zero_mem _, not_lt.1 hc⟩)
  obtain ⟨y₀, hy₀⟩ := exists_max (fun y : L₂ => Valued.v (prPbar s (H y))) (Valued.v (T : v.adicCompletion F))
    (by simpa using hTK) (fun y => by
      have h := ((hs.2.2 _).1 ((h2 _).1 (hTL x hx2) y y.2)).2
      rw [hform_nsmul_left, ← e2, map_mul, map_natCast, ← hH] at h
      rw [← map_mul]; exact h) ⟨y₁, hy₁⟩ (ne_of_gt (lt_trans zero_lt_one hgt))
  obtain ⟨c, hc⟩ : ∃ c, c = prPbar s (H y₀) := ⟨_, rfl⟩
  replace hy₀ : ∀ y : L₂, Valued.v (prPbar s (H y)) ≤ Valued.v c := hc ▸ hy₀
  have hc1 : 1 < Valued.v c := lt_of_lt_of_le hgt (hy₀ ⟨y₁, hy₁⟩)
  have hcv : 0 < Valued.v c := lt_trans zero_lt_one hc1
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hcv; exact lt_irrefl _ hcv
  obtain ⟨d, hd⟩ : ∃ d, d = s.symm (0, c⁻¹) := ⟨_, rfl⟩
  have hd2 : ∀ y, prPbar s (H y * d) = prPbar s (H y) / c := fun y => by
    rw [map_mul, e2 d, hd, s.apply_symm_apply, div_eq_mul_inv]
  have hmem : ∀ y : L₂, H y * d ∈ intV E v := fun y => by
    refine (hs.2.2 _).2 ⟨?_, ?_⟩
    · rw [map_mul, Prod.fst_mul, hfst, zero_mul]; exact zero_mem _
    · show Valued.v (prPbar s (H y * d)) ≤ 1
      rw [hd2, map_div₀, div_le_one₀ hcv]
      exact hy₀ y
  let g : L₂ →ₗ[intV E v] intV E v :=
    { toFun := fun y => ⟨H y * d, hmem y⟩
      map_add' := fun y z => Subtype.ext (by
        show H (y.1 + z.1) * d = H y * d + H z * d
        simp only [hH, hform_add_right, add_mul])
      map_smul' := fun a y => Subtype.ext (by
        show H ((a : E ⊗[F] v.adicCompletion F) • y.1) * d = a * (H y * d)
        simp only [hH, hform_smul_right, mul_assoc]) }
  have hg : ∀ y : L₂, prPbar s (g y) = prPbar s (H y) / c := fun y => hd2 y
  have hz : ∀ y : L₂, Valued.v (prPbar s (H y)) ≤ 1 → (primeOf (prPbar s)).mkQ (g y) = 0 := by
    intro y hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_primeOf_prPbar hs, hg, map_div₀,
      div_lt_one₀ hcv]
    exact lt_of_le_of_lt hy hc1
  refine ⟨(primeOf (prPbar s)).mkQ ∘ₗ g, fun b => ?_, fun y hy => hz y ?_, fun y hy => hz y ?_⟩
  · obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    refine ⟨a • y₀, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_primeOf_prPbar hs, map_smul,
      smul_eq_mul, AddSubgroupClass.coe_sub, Subring.coe_mul, map_sub, map_mul, hg, ← hc, div_self hc0]
    simp
  · rw [hH]; exact ((hs.2.2 _).1 (h1 y hy x hx2)).2
  · have : prPbar s (H y) = 0 := by

      simp only [hH, hform, map_sum, map_mul, hy, mul_zero, Finset.sum_const_zero]
    rw [this]; simp

end GlobalTheory.SecondFunctional
end

section

noncomputable section

namespace GlobalTheory.VolIndepCompare

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

theorem isFundamentalDomain_iff_image {G₁ G₂ : Type} [Group G₁] [Group G₂] [MeasurableSpace G₁]
    [MeasurableSpace G₂] (φ : G₁ ≃* G₂) (hφ : Measurable φ) (hφ' : Measurable φ.symm)
    (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) (hΓ : ∀ h, h ∈ Γ₁ ↔ φ h ∈ Γ₂) (μ : Measure G₁) (𝓕 : Set G₁) :
    IsFundamentalDomain Γ₁ 𝓕 μ ↔ IsFundamentalDomain Γ₂ (φ '' 𝓕) (μ.map φ) := by
  let e : Γ₁ ≃ Γ₂ :=
    { toFun := fun g => ⟨φ g, (hΓ g).1 g.2⟩
      invFun := fun g => ⟨φ.symm g, (hΓ _).2 (by simp)⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun g => Subtype.ext (by simp) }
  have hq : Measure.QuasiMeasurePreserving φ μ (μ.map φ) := ⟨hφ.aemeasurable, Measure.AbsolutelyContinuous.rfl⟩
  have hq' : Measure.QuasiMeasurePreserving φ.symm (μ.map φ) μ := by
    refine ⟨hφ'.aemeasurable, ?_⟩
    rw [Measure.map_map hφ' hφ]
    have : (φ.symm : G₂ → G₁) ∘ φ = id := by ext x; simp
    rw [this, Measure.map_id]
  constructor
  · intro h
    exact h.image_of_equiv φ.toEquiv hq' e.symm (fun g x => by
      change φ (φ.symm g * x) = (g : G₂) * φ x
      simp)
  · intro h
    have h2 := h.image_of_equiv φ.symm.toEquiv (ν := μ) hq e (fun g x => by
      change φ.symm (φ g * x) = (g : G₁) * φ.symm x
      simp)
    have h3 : φ.symm.toEquiv '' (φ '' 𝓕) = 𝓕 := by
      rw [Set.image_image]; simp
    rwa [h3] at h2

theorem isFundamentalDomain_iff_image_HA {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M₁ M₂ : ℕ} (J₁ : Matrix (Fin M₁) (Fin M₁) E)
    (J₂ : Matrix (Fin M₂) (Fin M₂) E) (φ : HA R σ J₁ ≃ₜ* HA R σ J₂)
    (hΓ : ∀ h, h ∈ HFinIn R σ J₁ ↔ φ h ∈ HFinIn R σ J₂) (μ : Measure (HA R σ J₁)) (𝓕 : Set (HA R σ J₁)) :
    IsFundamentalDomain (HFinIn R σ J₁) 𝓕 μ ↔ IsFundamentalDomain (HFinIn R σ J₂) (φ '' 𝓕) (μ.map φ) := by
  have : BorelSpace (HA R σ J₁) := ⟨rfl⟩
  have : BorelSpace (HA R σ J₂) := ⟨rfl⟩
  exact isFundamentalDomain_iff_image (G₁ := HA R σ J₁) (G₂ := HA R σ J₂) φ.toMulEquiv
    φ.continuous.measurable φ.symm.continuous.measurable (HFinIn R σ J₁) (HFinIn R σ J₂) hΓ μ 𝓕

theorem conj_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M₁ M₂ : ℕ}
    (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E) (C : Matrix (Fin M₂) (Fin M₁) E)
    (φ : HA (AF F) σ J₁ → HA (AF F) σ J₂) :
    GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence.IsConjugationBy (AF F) σ J₁ J₂ C φ ↔ GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.IsConjBy σ J₁ J₂ C φ := Iff.rfl

theorem conclusion_iff {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M₁ M₂ : ℕ}
    (J₁ : Matrix (Fin M₁) (Fin M₁) E) (J₂ : Matrix (Fin M₂) (Fin M₂) E) (C : Matrix (Fin M₂) (Fin M₁) E)
    (V₁ : Measure (HA (AF F) σ J₁) → Prop) (V₂ : Measure (HA (AF F) σ J₂) → Prop) :
    (∃ Φ : HA (AF F) σ J₁ ≃ₜ* HA (AF F) σ J₂,
        GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence.IsConjugationBy (AF F) σ J₁ J₂ C Φ ∧
        (∀ h : HA (AF F) σ J₁, HA.mat (AF F) σ J₁ h ∈ HFin (AF F) σ J₁ ↔
            HA.mat (AF F) σ J₂ (Φ h) ∈ HFin (AF F) σ J₂) ∧
        (∀ μ : Measure (HA (AF F) σ J₁), V₁ μ ↔ V₂ (μ.map Φ)) ∧
        ∀ μ : Measure (HA (AF F) σ J₁), V₁ μ → ∀ 𝓕 : Set (HA (AF F) σ J₁),
            IsFundamentalDomain (HFinIn (AF F) σ J₁) 𝓕 μ ↔
              IsFundamentalDomain (HFinIn (AF F) σ J₂) (Φ '' 𝓕) (μ.map Φ)) ↔
    (∃ φ : HA (AF F) σ J₁ ≃ₜ* HA (AF F) σ J₂,
        GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.IsConjBy σ J₁ J₂ C φ ∧
        (∀ h, h ∈ HFinIn (AF F) σ J₁ ↔ φ h ∈ HFinIn (AF F) σ J₂) ∧
        (∀ μ : Measure (HA (AF F) σ J₁), V₁ μ ↔ V₂ (μ.map φ)) ∧
        (∀ (μ : Measure (HA (AF F) σ J₁)) (𝓕 : Set (HA (AF F) σ J₁)),
          IsFundamentalDomain (HFinIn (AF F) σ J₁) 𝓕 μ ↔
            IsFundamentalDomain (HFinIn (AF F) σ J₂) (φ '' 𝓕) (μ.map φ))) := by
  constructor
  · rintro ⟨Φ, a, b, c, -⟩
    exact ⟨Φ, (conj_iff σ J₁ J₂ C Φ).1 a, b, c, isFundamentalDomain_iff_image_HA (AF F) σ J₁ J₂ Φ b⟩
  · rintro ⟨Φ, a, b, c, d⟩
    exact ⟨Φ, (conj_iff σ J₁ J₂ C Φ).2 a, b, c, fun μ _ => d μ⟩

theorem lattice_iff (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence.LatticeIndependence D ↔ GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.LatticeIndep D := by
  constructor
  · intro h W P Q hs L hL hU μ
    exact h W P Q hs _ L _ _ hL hU μ
  · intro h W P Q hs L L' hL hU hL' hU' μ
    exact (h W P Q hs L hL hU μ).symm.trans (h W P Q hs L' hL' hU' μ)

theorem transport_iff (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence.IsometryTransport D ↔ GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.IsometryTransport D := by
  let _ := D.host.cmStar
  constructor
  · intro h W₁ W₂ P Q h₁ h₂ e he hc
    exact (conclusion_iff D.sp.cm.sig W₁.gram W₂.gram _ (IsVolMeas D W₁ P Q) (IsVolMeas D W₂ P Q)).1
      (h W₁ W₂ P Q h₁ h₂ e he hc)
  · intro h W₁ W₂ P Q h₁ h₂ e he hc
    exact (conclusion_iff D.sp.cm.sig W₁.gram W₂.gram _ (IsVolMeas D W₁ P Q) (IsVolMeas D W₂ P Q)).2
      (h W₁ W₂ P Q h₁ h₂ e he hc)

theorem volume_iff (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence.VolumeInvariance D ↔ GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.VolEqOfIsometric D := by
  constructor
  · intro h hV W₁ W₂ P Q h₁ h₂ e he
    exact h hV W₁ W₂ P Q h₁ h₂ ⟨e, he⟩
  · rintro h hV W₁ W₂ P Q h₁ h₂ ⟨e, he⟩
    exact h hV W₁ W₂ P Q h₁ h₂ e he

theorem volumeIndependence_iff (D : D7) :
    GlobalTheory.IndefiniteRowSideFullHecke.SignatureLatticeIndependence.VolumeIndependence D ↔ GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.VolIndep D :=
  and_congr (lattice_iff D) (and_congr (transport_iff D) (volume_iff D))

end GlobalTheory.VolIndepCompare
end
end

section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeLevel

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.MainNotions.StandardLattice

theorem isSelfDualLat_iff {E : Type} [Field E] [NumberField E] {n : Type} [Fintype n]
    (σ : E →+* E) (J : Matrix n n E) (N : Submodule (𝓞 E) (n → E)) :
    SelfDualStabiliserIndex.IsSelfDualLat σ J N ↔ SelfDualLatticeIndex.IsSelfDualLat σ J N :=
  and_congr_right fun _ => and_congr_right fun _ => eq_comm

theorem self_dual_lattice_iff_x0 (D : D7) (N : Submodule (𝓞 D.host.E) (Fin D.R.k → D.host.E)) :
    (letI := D.host.cmStar
     SelfDualStabiliserIndex.IsSelfDualLat (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 N) ↔
      SelfDualLatticeIndex.IsSelfDualDefiniteLattice D N :=
  isSelfDualLat_iff _ _ _

theorem indexAt_iff (D : D7) (Lv : LevelData D) (u : D.what₂.Word) :
    SelfDualStabiliserIndex.IndexAt D Lv u ↔ SelfDualLatticeIndex.IndexAt D Lv u :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun N =>
    imp_congr (self_dual_lattice_iff_x0 D N) Iff.rfl

theorem indexKU_iff : SelfDualStabiliserIndex.IndexKU ↔ SelfDualLatticeIndex.StabiliserLevelIndexFormula :=
  forall_congr' fun D => forall_congr' fun Lv => forall_congr' fun u => indexAt_iff D Lv u

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeLevel
end
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwColumn

variable {D : D7} {u : D.what₂.Word}

def WtSigns (X : Ch D u) : Prop :=
  (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) ∧ ∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ

end GlobalTheory.LvT.TwColumn
end
end

section

open Formalism.BasicNotions GlobalTheory.LvT

namespace GlobalTheory.Proof.ColumnWeightTwisted

theorem exists_int_m_mul_EatT (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    ∃ k : ℤ, (D.R.m : ℝ) * EatT D u w = (k : ℝ) := by
  unfold EatT
  split_ifs
  · obtain ⟨a, ha⟩ := D.R.m_even
    obtain ⟨b, hb⟩ := D.R.t_odd
    refine ⟨(D.R.m : ℤ) * (2 * (∑ τ : D.what₂.Tau, (Wtau D u τ : ℤ)) + (D.R.f : ℤ) * (D.R.N D.R.m : ℤ)) +
      ((topsOf D.host D.eTau).card : ℤ) * ((b : ℤ) + 1) * ((D.R.m : ℤ) + 1) * a, ?_⟩
    have ha' : (D.R.m : ℝ) = a + a := by exact_mod_cast ha
    have hb' : (D.R.t : ℝ) = 2 * b + 1 := by exact_mod_cast hb
    unfold Formalism.MainNotions.G.Nm
    push_cast
    rw [hb', ha']
    ring
  · exact ⟨0, by simp⟩

theorem colGeTw_of_tupleChainSharpColumnValuation : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup), TupleChainSharpColumnValuation T u μ → ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T → ∀ x ∈ LT.Nlam D u w, Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw T u μ w x (-((D.R.m : ℝ) * EatT D u w)) := by
  intro D T u μ h w hw x hx
  obtain ⟨k, hk⟩ := exists_int_m_mul_EatT D u w
  obtain ⟨c, hc⟩ := D.what₂.places.val_surj w ((D.what₂.places.ramIdx w : ℤ) * k)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hc
    exact WithTop.top_ne_coe hc
  obtain ⟨y, hy, e⟩ := h w hw c _ hc (by rw [hk]; push_cast; exact le_rfl) x hx
  have hv : vAdd (D.plEq w) c = (D.what₂.places.ramIdx w : ℤ) * k := by
    rw [D.val_eq w _ hc0] at hc
    exact_mod_cast hc
  have hvi : vAdd (D.plEq w) c⁻¹ = - vAdd (D.plEq w) c := by
    unfold vAdd
    rw [map_inv₀, WithZero.log_inv]
  refine ⟨c⁻¹ • y, ?_, c⁻¹, y, hy, rfl, Or.inr ?_⟩
  · rw [LinearMap.map_smulₛₗ, e, smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
  · rw [hvi, hv, hk]
    unfold DV.ur
    push_cast
    exact le_of_eq (by ring)

end GlobalTheory.Proof.ColumnWeightTwisted
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix

namespace GlobalTheory.NegSpace

theorem hasSignature_neg_swap {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : Formalism.UG.HasSignature (-J) q p := by
  obtain ⟨e, P, hP⟩ := h
  let s := Equiv.sumComm (Fin p) (Fin q)
  refine ⟨e.trans s, Units.map (Matrix.reindexAlgEquiv ℂ ℂ s).toRingHom.toMonoidHom P, ?_⟩
  have e1 : Formalism.UG.Jpq q p = -(Formalism.UG.Jpq p q).submatrix s.symm s.symm := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Formalism.UG.Jpq, s]
  rw [e1, ← hP, ← submatrix_mul_equiv _ _ _ s.symm, ← submatrix_mul_equiv _ _ _ s.symm, ← Matrix.neg_mul, ← Matrix.mul_neg]
  rfl

theorem sigOK_neg : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), W.SigOK → (GlobalTheory.NegSpace.neg W).SigOK := by
  intro E _ _ _ W h τ
  have e : (neg W).gram.map τ = -W.gram.map τ := Matrix.ext fun i j => map_neg τ (W.gram i j)
  rw [e]
  exact hasSignature_neg_swap (h τ)

end GlobalTheory.NegSpace
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

theorem _root_.GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts : ∀ (D : D7), D.host.d.Prime ∧ D.host.d % 16 = 7 ∧ (∀ z : ℂ, GlobalTheory.MomOne.InOK D.host.d z ↔ ∃ x : 𝓞 D.host.K, z = D.host.φ₀ ((x : D.host.K) : D.host.E)) ∧ (∀ x : D.host.K, D.host.φ₀ (D.host.conj (x : D.host.E)) = (starRingEnd ℂ) (D.host.φ₀ (x : D.host.E))) ∧ ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → area (lamOf D cc δ) = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 ∧ ∀ z : ℂ, z ∈ lamOf D cc δ ↔ ∃ x ∈ cc, z = δ * D.host.φ₀ ((x : D.host.K) : D.host.E) := by
  first | exact @GlobalTheory.MomDict.main | exact GlobalTheory.MomDict.main | (intros; apply GlobalTheory.MomDict.main <;> assumption)
end
