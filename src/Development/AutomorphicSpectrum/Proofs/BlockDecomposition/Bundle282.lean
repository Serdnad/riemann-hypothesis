module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
import GroundTheory.LocalFields.LocalFourierHaar
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.ColMatMulGlEmbMat
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle184
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHolds
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeStable

theorem secondCountable_field (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact secondCountable_of_proper

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem unif_ne_zero : (uniformizer F : F) ≠ 0 := by
  intro h0
  exact (irreducible_uniformizer F).ne_zero (Subtype.ext h0)


variable (F) in
def scal (m M : ℕ) : GL (Fin m) F where
  val := ((uniformizer F : F)⁻¹ ^ M) • (1 : Matrix (Fin m) (Fin m) F)
  inv := ((uniformizer F : F) ^ M) • (1 : Matrix (Fin m) (Fin m) F)
  val_inv := by
    have h := unif_ne_zero (F := F)
    rw [smul_mul_smul_comm, one_mul, ← mul_pow, inv_mul_cancel₀ h, one_pow, one_smul]
  inv_val := by
    have h := unif_ne_zero (F := F)
    rw [smul_mul_smul_comm, one_mul, ← mul_pow, mul_inv_cancel₀ h, one_pow, one_smul]

theorem scal_mulVec (m M : ℕ) (x : Fin m → F) :
    ((scal F m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x = ((uniformizer F : F)⁻¹ ^ M) • x := by
  change (((uniformizer F : F)⁻¹ ^ M) • (1 : Matrix (Fin m) (Fin m) F)) *ᵥ x = _
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

theorem image_scal (m M : ℕ) :
    (fun x => ((scal F m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x) '' lat F m 0 = lat F m M := by
  have h := unif_ne_zero (F := F)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    have hxi := hx i
    rw [pow_zero, one_mul] at hxi
    simp only [scal_mulVec m M x, Pi.smul_apply, smul_eq_mul]
    rwa [← mul_assoc, ← mul_pow, mul_inv_cancel₀ h, one_pow, one_mul]
  · intro hy
    refine ⟨fun i => (uniformizer F : F) ^ M * y i, fun i => ?_, ?_⟩
    · rw [pow_zero, one_mul]; exact hy i
    · funext i
      simp only [scal_mulVec m M _, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ h, one_pow, one_mul]

theorem div_scal_inv {m c M : ℕ} (hM : c ≤ M) :
    Div c (((scal F m M)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) := by
  intro i j
  refine ⟨(uniformizer F : F) ^ (M - c) * (1 : Matrix (Fin m) (Fin m) F) i j, ?_, ?_⟩
  · refine mul_mem (pow_mem (uniformizer F).2 _) ?_
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne hij]; exact zero_mem _
  · change (((uniformizer F : F) ^ M) • (1 : Matrix (Fin m) (Fin m) F)) i j = _
    rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hM]

variable [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
  (ψ : AddChar F ℂ) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GL (Fin n) F) V) (k : ℕ) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)

def avg (M : ℕ) (u' u : V) : ℂ :=
  ∫ x in lat F (k + 1) M, ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u) ∂(Measure.pi fun _ => μ)

theorem exists_char (hψ : Continuous ψ) (hlat : ∀ M, IsCompact (lat F (k + 1) M))
    (hcont : ∀ u u', Continuous (fun x : Fin (k + 1) → F => B u' (ρ (col n k x) u)))
    (hst : ∀ u u', ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → avg μ ψ ρ k B M u' u = avg μ ψ ρ k B M₀ u' u) :
    ∃ B', Char μ ρ ψ k B B' := by
  haveI := secondCountable_field F
  choose m hm using hst
  have hint : ∀ M u' u, IntegrableOn
      (fun x : Fin (k + 1) → F => ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u)) (lat F (k + 1) M)
      (Measure.pi fun _ => μ) := by
    intro M u' u
    refine ContinuousOn.integrableOn_compact (hlat M) (Continuous.continuousOn ?_)
    exact (hψ.comp (continuous_apply _).neg).mul (hcont u u')
  let f : V → V → ℂ := fun u' u => avg μ ψ ρ k B (m u u') u' u
  have hf : ∀ u' u M, m u u' ≤ M → f u' u = avg μ ψ ρ k B M u' u :=
    fun u' u M h => (hm u u' M h).symm
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) f ?_ ?_ ?_ ?_, ?_⟩
  · intro a b w
    let M := max (m w (a + b)) (max (m w a) (m w b))
    rw [hf _ _ M (le_max_left _ _), hf _ _ M ((le_max_left _ _).trans (le_max_right _ _)),
      hf _ _ M ((le_max_right _ _).trans (le_max_right _ _))]
    simp only [avg]
    rw [← integral_add (hint M a w) (hint M b w)]
    congr 1
    funext x
    simp [mul_add]
  · intro c a w
    let M := max (m w (c • a)) (m w a)
    rw [hf _ _ M (le_max_left _ _), hf _ _ M (le_max_right _ _)]
    simp only [avg]
    rw [smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    simp
    ring
  · intro a v w
    let M := max (m (v + w) a) (max (m v a) (m w a))
    rw [hf _ _ M (le_max_left _ _), hf _ _ M ((le_max_left _ _).trans (le_max_right _ _)),
      hf _ _ M ((le_max_right _ _).trans (le_max_right _ _))]
    simp only [avg]
    rw [← integral_add (hint M a v) (hint M a w)]
    congr 1
    funext x
    simp [mul_add]
  · intro c a v
    let M := max (m (c • v) a) (m v a)
    rw [hf _ _ M (le_max_left _ _), hf _ _ M (le_max_right _ _)]
    simp only [avg]
    rw [smul_eq_mul, ← integral_const_mul]
    congr 1
    funext x
    simp
    ring
  · intro u u'
    exact ⟨m u u', fun M hM => hf u' u M hM⟩

theorem stable_average : L0 → FormCoefficientStability → StableAverageExists := by
  intro h0 h4 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B hk hInv
  obtain ⟨hψc, hL⟩ := h0 F μ ψ hψ
  have h4' := h4 F μ ψ hψ n V ρ hρ l k B hk hInv
  refine exists_char μ ψ ρ k B hψc (fun M => ((hL (k + 1)).1 M).1) (fun u u' => (h4' u u').1) ?_
  intro u u'
  obtain ⟨c, hc⟩ := (h4' u u').2
  refine ⟨c + 1, fun M hM => ?_⟩
  have := hc (scal F (k + 1) M) (div_scal_inv hM)
  rw [image_scal] at this
  exact this

end GlobalTheory.CompanionTheory.SatakeStable

end
end

section

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.JSBound

section Lattice

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem unif_ne_zero : (uniformizer F : F) ≠ 0 := fun h =>
  valuation_uniformizer_ne_zero F (by rw [h, map_zero])

theorem unif_pow_ne_zero (M : ℕ) : (uniformizer F : F) ^ M ≠ 0 := pow_ne_zero _ unif_ne_zero

theorem exists_unif_pow_mul_mem (x : F) : ∃ m : ℕ, (uniformizer F : F) ^ m * x ∈ 𝒪[F] := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hvx : ValuativeRel.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (valuation_uniformizer_lt_one F) (Units.mk0 _ hvx)⁻¹
  refine ⟨m, ?_⟩
  have h1 : ValuativeRel.valuation F (uniformizer F : F) ^ m * ValuativeRel.valuation F x < 1 := by
    have := mul_lt_mul_of_pos_right hm (zero_lt_iff.mpr hvx)
    simpa [hvx] using this
  rw [Valuation.mem_integer_iff, map_mul, map_pow]
  exact h1.le

theorem unif_pow_mul_mem_of_le {m m' : ℕ} (h : m ≤ m') {y : F}
    (hy : (uniformizer F : F) ^ m * y ∈ 𝒪[F]) : (uniformizer F : F) ^ m' * y ∈ 𝒪[F] := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : (uniformizer F : F) ^ d ∈ 𝒪[F] := pow_mem (uniformizer F).2 d
  have := mul_mem h1 hy
  rwa [← mul_assoc, ← pow_add, add_comm d m] at this

theorem exists_div_unif_pow_smul {ι : Type} [Finite ι] (A : Matrix ι ι F) (c : ℕ) :
    ∃ N : ℕ, ∀ M, N ≤ M → Div c ((uniformizer F : F) ^ M • A) := by
  classical
  cases nonempty_fintype ι
  choose f hf using fun p : ι × ι => exists_unif_pow_mul_mem (A p.1 p.2)
  refine ⟨c + Finset.univ.sup f, fun M hM i j => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  have hle : f (i, j) ≤ Finset.univ.sup f + d :=
    (Finset.le_sup (f := f) (Finset.mem_univ (i, j))).trans (Nat.le_add_right _ _)
  refine ⟨_, unif_pow_mul_mem_of_le hle (hf (i, j)), ?_⟩
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_add, add_assoc]

def scG (m M : ℕ) : GL (Fin m) F where
  val := ((uniformizer F : F) ^ M)⁻¹ • (1 : Matrix (Fin m) (Fin m) F)
  inv := ((uniformizer F : F) ^ M) • (1 : Matrix (Fin m) (Fin m) F)
  val_inv := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ (unif_pow_ne_zero M), one_mul, one_smul]
  inv_val := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ (unif_pow_ne_zero M), one_mul, one_smul]

theorem image_scG_lat (m M : ℕ) :
    (fun x => ((scG m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x) '' lat F m 0 =
      lat F m M := by
  have hval : ((scG m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      ((uniformizer F : F) ^ M)⁻¹ • (1 : Matrix (Fin m) (Fin m) F) := rfl
  ext x
  simp only [Set.mem_image, hval, Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    have := hy i
    simp only [pow_zero, one_mul] at this
    simpa [unif_pow_ne_zero M] using this
  · intro hx
    refine ⟨(uniformizer F : F) ^ M • x, fun i => ?_, ?_⟩
    · simpa using hx i
    · rw [smul_smul, inv_mul_cancel₀ (unif_pow_ne_zero M), one_smul]

end Lattice

theorem column_average_quasi_invariant : L0 → ColumnsMirabolic → FormCoefficientStability → FormQuasiInvariantMirabolic := by
  intro h0 h3 h4 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B B' hk hI hC g hg u' u
  have H0 := h0 F μ ψ hψ
  obtain ⟨-, -, -, hPP, hT, -⟩ := h3 F μ ψ hψ n k hk
  have hg1 := hPP g hg
  obtain ⟨t, hdet, hcomm, hlast⟩ := hT g hg1
  have hlast' := hlast hg
  have := Measures.metrizableSpace F
  obtain ⟨T, hTdef⟩ : ∃ T, T = (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) := ⟨_, rfl⟩
  obtain ⟨Ti, hTidef⟩ : ∃ Ti, Ti = ((t⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) :=
    ⟨_, rfl⟩
  rw [← hTdef] at hdet hcomm hlast'
  have hTTi : ∀ x, T *ᵥ (Ti *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hTdef, hTidef, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hTiT : ∀ x, Ti *ᵥ (T *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hTdef, hTidef, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  let h : (Fin (k + 1) → F) → ℂ := fun x => ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u)
  have hpt : ∀ x, ψ (-x (Fin.last k)) * B (ρ g u') (ρ (col n k x) (ρ g u)) =
      (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) *
        h (Ti *ᵥ x) := by
    intro x
    have e1 : col n k x * g = g * col n k (Ti *ᵥ x) := by rw [hcomm, hTTi]
    have e2 : ρ (col n k x) (ρ g u) = ρ g (ρ (col n k (Ti *ᵥ x)) u) := by
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply]
    have e3 : (Ti *ᵥ x) (Fin.last k) = x (Fin.last k) := by
      have := hlast' (Ti *ᵥ x)
      rw [hTTi] at this
      exact this.symm
    rw [e2, hI.quasi g hg1]
    simp only [h, e3]
    ring
  obtain ⟨M₁, hM₁⟩ := hC (ρ g u) (ρ g u')
  obtain ⟨M₂, hM₂⟩ := hC u u'
  obtain ⟨-, c, hc⟩ := h4 F μ ψ hψ n V ρ hρ l k B hk hI u u'
  obtain ⟨N, hN⟩ := exists_div_unif_pow_smul T (c + 1)
  obtain ⟨N', hN'⟩ := exists_div_unif_pow_smul (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (c + 1)

  obtain ⟨M, hMM₁, hMN⟩ : ∃ M, M₁ ≤ M ∧ N ≤ M := ⟨max M₁ N, le_max_left _ _, le_max_right _ _⟩
  have step1 : B' (ρ g u') (ρ g u) =
      (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) *
        ∫ x in lat F (k + 1) M, h (Ti *ᵥ x) ∂(Measure.pi fun _ => μ) := by
    rw [hM₁ M hMM₁, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hcont : Continuous fun x : Fin (k + 1) → F => Ti *ᵥ x :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hmeas : MeasurableSet ((fun x => Ti *ᵥ x) '' lat F (k + 1) M) :=
    (((H0.2 (k + 1)).1 M).1.image hcont).measurableSet
  have step2 := (H0.2 (k + 1)).2 t ((fun x => Ti *ᵥ x) '' lat F (k + 1) M)
    (fun x => h (Ti *ᵥ x)) hmeas
  rw [← hTdef, Set.image_image] at step2
  simp only [hTTi, hTiT, Set.image_id'] at step2

  have hG : (fun x => (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F) : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) '' lat F (k + 1) 0 =
      (fun x => Ti *ᵥ x) '' lat F (k + 1) M := by
    rw [← image_scG_lat (k + 1) M, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [Units.val_mul, ← hTidef, Matrix.mulVec_mulVec]
  have hGdiv : Div (c + 1) (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) := by
    have : (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) F) = (uniformizer F : F) ^ M • T := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hTdef]
      change ((uniformizer F : F) ^ M • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F)) * _ = _
      rw [Matrix.smul_mul, Matrix.one_mul]
    rw [this]
    exact hN M hMN
  have step3 := hc _ hGdiv
  rw [hG] at step3

  obtain ⟨M', hM'₂, hM'N⟩ : ∃ M', M₂ ≤ M' ∧ N' ≤ M' :=
    ⟨max M₂ N', le_max_left _ _, le_max_right _ _⟩
  have hSdiv : Div (c + 1) (((scG (k + 1) M' : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) := hN' M' hM'N
  have step4 := hc _ hSdiv
  rw [image_scG_lat] at step4
  have step5 := hM₂ M' hM'₂
  have hmod : (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - k) =
      (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) *
        ((Measures.modulus T.det : ℝ) : ℂ) := by
    rw [hdet, ← pow_succ]
    congr 1
    omega
  rw [step1, step2, hmod, mul_assoc]
  congr 2
  rw [step5, step4]
  exact step3

end GlobalTheory.CompanionTheory.JSBound

end
end

section

open PositivityTheory.JacquetShalikaLocal
open MeasureTheory ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_integer_psi_mul_ne_one {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {b : F}
    (hb : b ∉ (valuation F).integer) :
    ∃ t ∈ (valuation F).integer, ψ (t * b) ≠ 1 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (zero_mem _)
  have hvb : 1 < valuation F b := by
    rw [Valuation.mem_integer_iff, not_le] at hb
    exact hb
  have hvinv : valuation F b⁻¹ < 1 := ((valuation F).one_lt_val_iff hb0).mp hvb
  have hinvO : b⁻¹ ∈ (valuation F).integer := by
    rw [Valuation.mem_integer_iff]
    exact hvinv.le
  have hynu : (⟨b⁻¹, hinvO⟩ : (valuation F).integer) ∈ IsLocalRing.maximalIdeal (valuation F).integer := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (ne_of_lt hvinv) ((Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.mp hu)
  have hmax := GroundTheory.Automorphic.GLnLocal.maximalIdeal_pow_eq F 1
  rw [pow_one, pow_one] at hmax
  rw [hmax, Ideal.mem_span_singleton] at hynu
  obtain ⟨u, hu⟩ := hynu
  obtain ⟨x, hx, hψx⟩ := hψ.2.1
  refine ⟨(↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F), mul_mem hx u.2, ?_⟩
  have hu' : b⁻¹ = (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) * (u : F) := by
    have h := congrArg Subtype.val hu
    simpa using h
  have hx' : (↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F) * b = x := by
    calc (↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F) * b
        = x * ((GroundTheory.Automorphic.GLnLocal.uniformizer F : F) * u) * b := by ring
      _ = x * b⁻¹ * b := by rw [hu']
      _ = x := by rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  rw [hx']
  exact hψx

theorem mem_lat_zero {m : ℕ} {x : Fin m → F} :
    x ∈ lat F m 0 ↔ ∀ i, x i ∈ (valuation F).integer := by
  simp only [lat, Set.mem_ofPred_eq, pow_zero, one_mul]

theorem orthogonality_of_lattice_character : L0 → L1 := by
  unfold L0 L1 ForF
  intro hL0 F _ _ _ _ _ _ μ _ ψ hψ m y
  have hL := hL0 F μ ψ hψ
  dsimp only at hL ⊢
  by_cases hy : ∀ i, y i ∈ (valuation F).integer
  · rw [if_pos hy]
    have hmeas : MeasurableSet (lat F m 0) := ((hL.2 m).1 0).2.2.1
    have h1 : Set.EqOn (fun ξ : Fin m → F => ψ (ξ ⬝ᵥ y)) (fun _ => (1 : ℂ)) (lat F m 0) := by
      intro ξ hξ
      rw [mem_lat_zero] at hξ
      refine hψ.1 _ ?_
      unfold dotProduct
      exact sum_mem fun j _ => mul_mem (hξ j) (hy j)
    rw [setIntegral_congr_fun hmeas h1, setIntegral_const]
    simp
  · rw [if_neg hy]
    simp only [not_forall] at hy
    obtain ⟨i, hi⟩ := hy
    obtain ⟨t, ht, hne⟩ := exists_integer_psi_mul_ne_one hψ hi
    have hsO : ∀ j, (Pi.single i t : Fin m → F) j ∈ (valuation F).integer := by
      intro j
      by_cases hj : j = i
      · rw [hj, Pi.single_eq_same]
        exact ht
      · rw [Pi.single_eq_of_ne hj]
        exact zero_mem _
    have hinv : (fun ξ : Fin m → F => Pi.single i t + ξ) ⁻¹' lat F m 0 = lat F m 0 := by
      ext ξ
      simp only [Set.mem_preimage, mem_lat_zero, Pi.add_apply]
      constructor
      · intro h j
        have h2 := sub_mem (h j) (hsO j)
        simpa using h2
      · intro h j
        exact add_mem (hsO j) (h j)
    have hsd : (Pi.single i t : Fin m → F) ⬝ᵥ y = t * y i := by
      first
        | exact single_dotProduct t i
        | simp [dotProduct, Pi.single_apply]
    have hmp := measurePreserving_add_left (Measure.pi fun _ : Fin m => μ) (Pi.single i t : Fin m → F)
    have hemb := measurableEmbedding_addLeft (Pi.single i t : Fin m → F)
    have hshift := hmp.setIntegral_preimage_emb hemb (fun ξ => ψ (ξ ⬝ᵥ y)) (lat F m 0)
    rw [hinv] at hshift
    simp only [add_dotProduct, AddChar.map_add_eq_mul, hsd] at hshift
    rw [integral_const_mul] at hshift
    have h0 : (∫ ξ in lat F m 0, ψ (ξ ⬝ᵥ y) ∂Measure.pi fun _ => μ) * (ψ (t * y i) - 1) = 0 := by
      linear_combination hshift
    exact (mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr hne)

end GlobalTheory.CompanionTheory.SatakeBound
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem _root_.GlobalTheory.T.smooth_mirabolic_kernel_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k (m + 1)) V), IsSmooth τ → ∀ v : V, v ∈ twKer τ (MirUin k (m + 1)) 1 → (∀ g : GL (Fin (m + 1)) k, τ (levi k (m + 1) g) v ∈ twKer τ (MirUin k (m + 1)) (mirChar k ψ m)) → v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.eq_zero_of_forall_twKer | exact GlobalTheory.CompanionTheory.MirFourier.eq_zero_of_forall_twKer | (intros; apply GlobalTheory.CompanionTheory.MirFourier.eq_zero_of_forall_twKer <;> assumption)
end

section


theorem _root_.GlobalTheory.T.branch_proper_at_point_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint | exact GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint | (intros; apply GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint <;> assumption)
end
