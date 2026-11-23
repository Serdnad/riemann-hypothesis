module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle038
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle066
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle014
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle076
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.EiBound

theorem prod_sum_bound {S R : Type} (h : S × R → ℝ) (a : S → ℝ) (K : ℝ) (h0 : ∀ p, 0 ≤ h p)
    (ha : Summable a)
    (hin : ∀ s, Summable (fun r => h (s, r)) ∧ ∑' r, h (s, r) ≤ a s * K) :
    Summable h ∧ ∑' p, h p ≤ (∑' s, a s) * K := by
  have hout : Summable (fun s => ∑' r, h (s, r)) :=
    Summable.of_nonneg_of_le (fun s => tsum_nonneg fun r => h0 _) (fun s => (hin s).2)
      (ha.mul_right K)
  have hs : Summable h := (summable_prod_of_nonneg (fun p => h0 p)).2 ⟨fun s => (hin s).1, hout⟩
  refine ⟨hs, ?_⟩
  rw [hs.tsum_prod, ← tsum_mul_right]
  exact Summable.tsum_le_tsum (fun s => (hin s).2) hout (ha.mul_right K)

theorem exists_decomp (F : Type) [Field F] [NumberField F] :
    ∃ (Q : Type) (out : Q → F), Function.Injective out ∧
      (∀ q q', (∃ r : 𝓞 F, out q - out q' = (r : F)) → q = q') ∧
      Function.Bijective (fun p : Q × 𝓞 F => out p.1 + (p.2 : F)) := by
  let L : AddSubgroup F := (algebraMap (𝓞 F) F).toAddMonoidHom.range
  have hL : ∀ x : F, x ∈ L ↔ ∃ r : 𝓞 F, (r : F) = x := fun x => by
    simp [L, AddMonoidHom.mem_range]
  have hsep : ∀ q q' : F ⧸ L, (∃ r : 𝓞 F, (Quotient.out q : F) - Quotient.out q' = (r : F)) →
      q = q' := by
    rintro q q' ⟨r, hr⟩
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
    refine (QuotientAddGroup.eq).2 ?_
    have : -(Quotient.out q : F) + Quotient.out q' = ((-r : 𝓞 F) : F) := by
      push_cast
      linear_combination -hr
    exact (hL _).2 ⟨-r, this.symm⟩
  refine ⟨F ⧸ L, Quotient.out, ?_, hsep, ?_, ?_⟩
  · intro q q' h
    exact hsep q q' ⟨0, by simp [h]⟩
  · rintro ⟨q, r⟩ ⟨q', r'⟩ h
    simp only at h
    have hq : q = q' := hsep q q' ⟨r' - r, by push_cast; linear_combination h⟩
    subst hq
    have : (r : F) = r' := add_left_cancel h
    have : r = r' := RingOfIntegers.ext this
    rw [this]
  · intro b
    have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk b : F ⧸ L)) : F ⧸ L) =
        QuotientAddGroup.mk b := QuotientAddGroup.out_eq' _
    obtain ⟨r, hr⟩ := (hL _).1 ((QuotientAddGroup.eq).1 h1)
    refine ⟨⟨QuotientAddGroup.mk b, r⟩, ?_⟩
    simp only
    rw [hr]; ring

theorem place_bound (M : ℕ) (hM : 2 ≤ M) (t y : ℝ) (ht : 0 < t) (hy : t ≤ y) :
    Real.sqrt y ^ M * (y * (y ^ M)⁻¹) ≤ ((Real.sqrt t) ^ (M - 2))⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 2 := ⟨M - 2, by omega⟩
  have hy0 : 0 < y := ht.trans_le hy
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hyy : y = Real.sqrt y ^ 2 := (Real.sq_sqrt hy0.le).symm
  have e : Real.sqrt y ^ (k + 2) * (y * (y ^ (k + 2))⁻¹) = (Real.sqrt y ^ k)⁻¹ := by
    generalize Real.sqrt y = s at hs hyy
    subst hyy
    field_simp
    ring
  rw [e, Nat.add_sub_cancel]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hst.le (Real.sqrt_le_sqrt hy) k)

theorem ei_bound : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)]
    (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M →
    ∀ φ : (ι → A F) → ℂ, SB φ → ∀ t : ℝ, 0 < t → ∃ C : ℝ, ∀ τ : InfinitePlace F → ℂ,
    (∀ w, t ≤ (τ w).im) → Summable (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖) ∧
      wt M τ * ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ ≤ C := by
  intro F _ _ _ _ lf hlf hO ψ hψ ι _ _ M B ρ P hQ hM φ hφ t ht
  have hTR : IsTotallyReal F := hQ.1
  have hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x := hQ.2.2.2.2.1
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.fourier_coefficient_growth_bound F lf hlf hO ψ hψ ι M B ρ P hQ φ hφ
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.eisenstein_lattice_sum_bound F hTR ρ hρ M (by omega) t ht
  obtain ⟨Q, out, hinj, hsep, hbij⟩ := exists_decomp F
  obtain ⟨hd1, hd2, hd3⟩ := GlobalTheory.T.denominator_power_summable F M hM 1 one_pos
  let a : Q → ℝ := fun q => ((den (out q) : ℝ) ^ M)⁻¹
  have ha0 : ∀ q, 0 ≤ a q := fun q => by positivity
  have ha : Summable a := by
    have h := hd3 (Set.range out) (by
      rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩ ⟨r, hr⟩
      rw [hsep q q' ⟨r, by simpa using hr⟩])
    exact (Equiv.ofInjective out hinj).summable_iff.2 h
  have hterm : ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → ∀ b : F,
      ‖eiTerm ψ lf B ρ P φ τ b‖ ≤
        |C1| * ((den b : ℝ) ^ M)⁻¹ * (∏ w, ‖τ w + (ρ w b : ℝ)‖ ^ M)⁻¹ := by
    intro τ hτ b
    have hc := (GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P hQ (fun w => τ w + (ρ w b : ℝ))
      (fun w => by simpa using hτ w)).2.1
    unfold eiTerm
    rw [norm_mul, hc]
    refine mul_le_mul_of_nonneg_right ((hC1 b).trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  refine ⟨(∑' q, a q) * |C1| * |C2| * ∏ _w : InfinitePlace F, ((Real.sqrt t) ^ (M - 2))⁻¹, ?_⟩
  intro τ hτ
  have hτ0 : ∀ w, 0 < (τ w).im := fun w => ht.trans_le (hτ w)
  set Y : ℝ := ∏ w, (τ w).im * ((τ w).im ^ M)⁻¹ with hYdef
  have hY0 : 0 ≤ Y := Finset.prod_nonneg fun w _ => by
    have := hτ0 w
    positivity
  let e : Q × 𝓞 F ≃ F := Equiv.ofBijective _ hbij
  let h' : Q × 𝓞 F → ℝ := fun p =>
    |C1| * a p.1 * (∏ w, ‖(τ w + (ρ w (out p.1) : ℝ)) + (ρ w (p.2 : F) : ℝ)‖ ^ M)⁻¹
  have hh'0 : ∀ p, 0 ≤ h' p := fun p => by
    have := ha0 p.1
    positivity
  have hle : ∀ p, ‖eiTerm ψ lf B ρ P φ τ (e p)‖ ≤ h' p := by
    rintro ⟨q, r⟩
    have h1 := hterm τ hτ0 (out q + (r : F))
    have h2 : den (out q + (r : F)) = den (out q) := hd1 _ _
    rw [h2] at h1
    have h3 : ∀ w, τ w + ((ρ w (out q + (r : F)) : ℝ) : ℂ) =
        (τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ) := fun w => by
      rw [map_add (f := _)]; push_cast; ring
    simp only [h3] at h1
    exact h1
  have hin : ∀ q, Summable (fun r => h' (q, r)) ∧
      ∑' r, h' (q, r) ≤ a q * (|C1| * (|C2| * Y)) := by
    intro q
    obtain ⟨hs, hb⟩ := hC2 (fun w => τ w + (ρ w (out q) : ℝ)) (fun w => by simpa using hτ w)
    have him : ∀ w, (τ w + ((ρ w (out q) : ℝ) : ℂ)).im = (τ w).im := fun w => by simp
    simp only [him] at hb
    have hs' : Summable (fun r : 𝓞 F => |C1| * a q *
        (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹) := hs.mul_left _
    refine ⟨hs', ?_⟩
    change ∑' r : 𝓞 F, |C1| * a q *
        (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹ ≤ _
    rw [tsum_mul_left]
    calc |C1| * a q * ∑' r : 𝓞 F, (∏ w, ‖(τ w + (ρ w (out q) : ℝ)) + (ρ w (r : F) : ℝ)‖ ^ M)⁻¹
        ≤ |C1| * a q * (|C2| * Y) :=
          mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hY0))
            (by positivity)
      _ = a q * (|C1| * (|C2| * Y)) := by ring
  obtain ⟨hsum', hbd'⟩ := prod_sum_bound h' a (|C1| * (|C2| * Y)) hh'0 ha hin
  have hsumc : Summable (fun p => ‖eiTerm ψ lf B ρ P φ τ (e p)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hsum'
  have hsum : Summable (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖) := e.summable_iff.1 hsumc
  refine ⟨hsum, ?_⟩
  have htot : ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖ ≤ (∑' q, a q) * (|C1| * (|C2| * Y)) := by
    rw [← e.tsum_eq (fun b => ‖eiTerm ψ lf B ρ P φ τ b‖)]
    exact (Summable.tsum_le_tsum hle hsumc hsum').trans hbd'
  have hwt0 : 0 ≤ wt M τ := Finset.prod_nonneg fun w _ => by positivity
  have hwY : wt M τ * Y ≤ ∏ _w : InfinitePlace F, ((Real.sqrt t) ^ (M - 2))⁻¹ := by
    rw [hYdef]
    unfold wt
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun w _ => ?_) (fun w _ => place_bound M (by omega) t _ ht (hτ w))
    have := hτ0 w
    positivity
  calc wt M τ * ∑' b, ‖eiTerm ψ lf B ρ P φ τ b‖
      ≤ wt M τ * ((∑' q, a q) * (|C1| * (|C2| * Y))) :=
        mul_le_mul_of_nonneg_left htot hwt0
    _ = (∑' q, a q) * |C1| * |C2| * (wt M τ * Y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwY (by positivity)

end GlobalTheory.CompanionTheory.SW.Core.EiBound
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.IsoBox

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hform_eq_dot {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (J : Matrix n n A) (x y : n → A) :
    hform s J x y = (fun i => s (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (J g : Matrix n n A) (x y : n → A) :
    hform s J (g *ᵥ x) (g *ᵥ y) = hform s (cT s g * J * g) x y := by
  rw [hform_eq_dot, hform_eq_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec (fun i => s (x i)) (cT s g)]
  congr 1
  ext i
  simp [cT, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]

theorem gramE_mulVec (σ : E →ₐ[F] E) {M n : ℕ} (J g : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → E) :
    gramE σ J (fun a => g *ᵥ X a) = gramE σ (cT (σ : E →+* E) g * J * g) X := by
  funext a c
  exact hform_mulVec (σ : E →+* E) J g (X a) (X c)

theorem isotropic_preimage (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : GL (Fin M) E) :
    {X : Fin 1 → Fin M → E | (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ X a) ∈
        {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0}} =
      {X : Fin 1 → Fin M → E | X ≠ 0 ∧
        gramE σ (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
          (g : Matrix (Fin M) (Fin M) E)) X = 0} := by
  ext X
  simp only [Set.mem_ofPred_eq, gramE_mulVec]
  refine and_congr_left fun _ => not_congr ?_
  constructor
  · intro h
    funext a
    have h1 := congrFun h a
    have h2 : ((g⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ
        ((g : Matrix (Fin M) (Fin M) E) *ᵥ X a) = X a := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel]
      simp
    rw [← h2]
    simp only [Pi.zero_apply] at h1 ⊢
    rw [h1, Matrix.mulVec_zero]
  · intro h
    funext a
    simp [h]

theorem actTup_smul (R : Type) [CommRing R] [Algebra F R] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E))
    (c : R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E) :
    actTup R g (c • Y) = c • actTup R g Y := by
  funext a
  simp [actTup, Matrix.mulVec_smul]

theorem continuous_actTup (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing (R ⊗[F] E)] {M n : ℕ} (g : GL (Fin M) (R ⊗[F] E)) :
    Continuous (actTup R g : (Fin n → Fin M → R ⊗[F] E) → _) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  simp only [actTup, Matrix.mulVec, dotProduct]
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul ((continuous_apply j).comp (continuous_apply a))

end GlobalTheory.CompanionTheory.SW.IsoBox

namespace GlobalTheory.CompanionTheory.SW

theorem mean_isotropic_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ), 0 < N → ∃ C : ℝ, ∀ r : ℝ, 0 < r → cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * (M - 1))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM μ 𝓕 hH hF d b N hN
  by_cases hiso : ∃ x : Fin M → E, x ≠ 0 ∧ hE σ J x x = 0
  · obtain ⟨x, hx, hxx⟩ := hiso
    obtain ⟨M₁, hM₁, g, J₁, hJ₁, hg⟩ := GlobalTheory.T.isotropic_vector_splits_hyperbolic_plane F E σ hCM M J hJ x hx hxx
    subst hM₁
    obtain ⟨μ', 𝓕', hH', hF', -, hT⟩ :=
      GlobalTheory.T.fundamental_domain_transport_congruent_form F E σ hCM (M₁ + 2) J hJ g (hypJ J₁) hg μ 𝓕 hH hF
    obtain ⟨τ, hτ⟩ := GlobalTheory.T.exists_real_flow_adelic_units F E σ hCM
    obtain ⟨hbc, -, hsc⟩ := GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hCM d b 1 (M₁ + 2)
    obtain ⟨⟨hA1, hA2, hA3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
    have := hA1
    have := hA2
    have := hA3
    have : IsTopologicalRing (AF F ⊗[F] E) :=
      (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)).1
    set G : GL (Fin (M₁ + 2)) (AF F ⊗[F] E) := bc (inclR (AF F)) g with hG
    have hΩ : IsCompact (actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E))) := by
      have himg : actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) =
          actTup (AF F) G⁻¹ '' box b N 1 := by
        ext Y
        constructor
        · intro hY
          refine ⟨_, hY, ?_⟩
          funext a
          simp [actTup, Matrix.mulVec_mulVec]
        · rintro ⟨Z, hZ, rfl⟩
          have : actTup (AF F) G (actTup (AF F) G⁻¹ Z) = Z := by
            funext a
            simp [actTup, Matrix.mulVec_mulVec]
          simpa [Set.mem_preimage, this] using hZ
      rw [himg]
      exact (hbc N 1 hN).image (IsoBox.continuous_actTup (AF F) G⁻¹)
    obtain ⟨C, hC⟩ := GlobalTheory.T.hyperbolic_finite_volume_integral_bound F E σ hCM M₁ J₁ hJ₁ (by omega)
      (GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM M₁ J₁ hJ₁) τ hτ μ' 𝓕' hH' hF' _ hΩ
    refine ⟨C, fun r hr => ?_⟩
    have hfun : (fun Y : Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E =>
          Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)) (actTup (AF F) G Y)) =
        fun Y => (Set.indicator (actTup (AF F) G ⁻¹' box b N 1) (fun _ => (1 : ℝ≥0∞)))
          (((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y) := by
      funext Y
      have hmem : actTup (AF F) G Y ∈ (box b N r : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) ↔
          ((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y ∈
            actTup (AF F) G ⁻¹' (box b N 1 : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E)) := by
        have h := hsc τ hτ N r (-Real.log r) (actTup (AF F) G Y)
        have h1 : Real.exp (-Real.log r) * r = 1 := by
          rw [Real.exp_neg, Real.exp_log hr]
          exact inv_mul_cancel₀ hr.ne'
        rw [h1] at h
        rw [Set.mem_preimage, IsoBox.actTup_smul]
        exact h.symm
      by_cases hY : actTup (AF F) G Y ∈ (box b N r : Set (Fin 1 → Fin (M₁ + 2) → AF F ⊗[F] E))
      · rw [Set.indicator_of_mem hY, Set.indicator_of_mem (hmem.1 hY)]
      · rw [Set.indicator_of_notMem hY, Set.indicator_of_notMem (fun h => hY (hmem.2 h))]
    have hset := IsoBox.isotropic_preimage σ J g
    rw [← hg] at hset
    rw [hT 1, hset, hfun]
    simpa using hC r hr
  · refine ⟨0, fun r _ => ?_⟩
    have hempty : {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} = ∅ := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hX hgr
      apply hiso
      refine ⟨X 0, fun h0 => hX ?_, congrFun (congrFun hgr 0) 0⟩
      funext a
      rw [Subsingleton.elim a 0, h0]
      rfl
    simp [cntI, hempty]

end GlobalTheory.CompanionTheory.SW
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.exists_isEulerProd_of_invariant_of_fiber_supported : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ), n = 0 ∨ n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf → ∀ (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v)) → ∀ I : Measure (Fin n → Fin M → AF F ⊗[F] E), IsLocallyFiniteMeasure I → (∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I) → I {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0 → ∃ c : ℝ≥0, IsEulerProd b I c (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Fact.exists_isEulerProd | exact GlobalTheory.CompanionTheory.SW.Fact.exists_isEulerProd | (intros; apply GlobalTheory.CompanionTheory.SW.Fact.exists_isEulerProd <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SdUniq

theorem not_selfDual_one (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [LocallyCompactSpace V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
    (k : Measure V) : ¬ SelfDual k (fun _ _ => (1 : ℂ)) := by
  intro hk
  haveI := hk.1
  obtain ⟨h, hh⟩ := exists_ne (0 : V)
  obtain ⟨g, hg1, hg0, hgc, -⟩ := exists_continuous_one_zero_of_isCompact (X := V)
    (s := {0}) (t := {-h}) isCompact_singleton isClosed_singleton
    (by simpa [eq_comm] using hh)
  let g' : V → ℂ := fun x => ((g x : ℝ) : ℂ)
  have hc' : Continuous g' := Complex.continuous_ofReal.comp g.continuous
  have hs' : HasCompactSupport g' := hgc.comp_left (g := Complex.ofReal) (by simp)
  let Φ : V → ℂ := fun x => g' x - g' (x - h)
  have hc2 : Continuous fun x => g' (x - h) := hc'.comp (by fun_prop)
  have hs2 : HasCompactSupport fun x => g' (x - h) :=
    hs'.comp_homeomorph (Homeomorph.subRight h)
  have hΦc : Continuous Φ := hc'.sub hc2
  have hΦs : HasCompactSupport Φ := hs'.sub hs2
  have e : ∫ x, Φ x * (1 : ℂ) ∂k = 0 := by
    simp only [mul_one, Φ]
    rw [integral_sub (hc'.integrable_of_hasCompactSupport hs')
      (hc2.integrable_of_hasCompactSupport hs2), integral_sub_right_eq_self g' h, sub_self]
  have hI : Integrable (fun _ : V => ∫ x, Φ x * (1 : ℂ) ∂k) k := by
    rw [e]
    exact integrable_zero V ℂ k
  have key : ∫ _ : V, (∫ x, Φ x * (1 : ℂ) ∂k) * (1 : ℂ) ∂k = Φ (-0) := hk.2 Φ hΦc hΦs hI 0
  rw [e, zero_mul, integral_zero, neg_zero] at key
  have h1 : g 0 = 1 := hg1 rfl
  have h2 : g (-h) = 0 := hg0 rfl
  have h3 : Φ 0 = 1 := by simp [Φ, g', h1, h2]
  rw [h3] at key
  exact zero_ne_one key

variable (F : Type) [Field F] [NumberField F]

noncomputable def chiV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom ((AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom)

theorem chiV_apply (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    chiV F ψ v t = psiV F ψ v t := rfl

theorem selfDual_unique_coord : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Measure (Fv F v)), SelfDual k (fun s t => psiV F ψ v (s * t)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.IsSymm → A.det ≠ 0 → ∀ μ ν : Measure (ι → Fv F v), SelfDual μ (fun x y => psiV F ψ v (x ⬝ᵥ (A.map (algebraMap F (Fv F v)) *ᵥ y))) → SelfDual ν (fun x y => psiV F ψ v (x ⬝ᵥ (A.map (algebraMap F (Fv F v)) *ᵥ y))) → μ = ν := by
  intro F _ _ ψ hψ v k hk ι _ _ A hA hdet μ ν hμ hν
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hc : Continuous (chiV F ψ v) :=
    hψ.1.comp (Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v))
  have hu : ∀ t, ‖chiV F ψ v t‖ = 1 := fun t => hψ.2.1 _
  have hne : ∃ t, chiV F ψ v t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine not_selfDual_one (Fv F v) k ?_
    have e : (fun s t : Fv F v => psiV F ψ v (s * t)) = fun _ _ => (1 : ℂ) := by
      funext s t
      exact hcon _
    rwa [e] at hk
  set M : Matrix ι ι (Fv F v) := A.map (algebraMap F (Fv F v)) with hM
  have hMs : Mᵀ = M := by
    rw [hM, ← Matrix.transpose_map, hA.eq]
  have hMd : M.det ≠ 0 := by
    have : M.det = algebraMap F (Fv F v) A.det := by
      rw [hM]; exact (RingHom.map_det (algebraMap F (Fv F v)) A).symm
    rw [this]
    exact (map_ne_zero _).2 hdet
  have hs : ∀ x y, Matrix.toBilin' M x y = Matrix.toBilin' M y x := by
    intro x y
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec, dotProduct_comm,
      ← Matrix.mulVec_transpose, hMs]
  have hn : ∀ x, (∀ y, Matrix.toBilin' M x y = 0) → x = 0 := by
    intro x hx
    refine Matrix.eq_zero_of_vecMul_eq_zero hMd ?_
    refine dotProduct_eq_zero _ fun w => ?_
    rw [← Matrix.dotProduct_mulVec, ← Matrix.toBilin'_apply']
    exact hx w
  have huniq := GlobalTheory.SelfDualFinite.existsUnique_of_bilin v (chiV F ψ v) hc hu hne (ι → Fv F v)
    (Matrix.toBilin' M) hs hn
  have e : (fun x y : ι → Fv F v => chiV F ψ v (Matrix.toBilin' M x y)) =
      fun x y => psiV F ψ v (x ⬝ᵥ (M *ᵥ y)) := by
    funext x y
    rw [Matrix.toBilin'_apply', chiV_apply]
  rw [e] at huniq
  exact huniq.unique ⟨hμ.1, hμ.2⟩ ⟨hν.1, hν.2⟩

end GlobalTheory.CompanionTheory.SW.SdUniq
end
