module

public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle004
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle003
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
import Mathlib.RingTheory.Henselian
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
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

noncomputable section

open MeasureTheory GlobalTheory.WeilM GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.SchrLaw

namespace GlobalTheory.CompanionTheory.SchrModel

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem locallyCompact_of_goodChar [T2Space R] {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) :
    LocallyCompactSpace R := by
  exact h.compact.locallyCompactSpace_of_mem_nhds_of_addGroup (h.isOpen.mem_nhds O.zero_mem)


omit [CommRing R] [IsTopologicalRing R] in
theorem integrable_pair {κ : Type} (μ : @Measure (κ → R) (borel _))
    (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ) (φ φ' : SB (κ → R)) :
    @Integrable _ _ _ _ (borel _) (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) μ := by
  haveI := hμ
  have hφ : IsLocallyConstant (φ : (κ → R) → ℂ) ∧ HasCompactSupport (φ : (κ → R) → ℂ) := φ.2
  have hφ' : IsLocallyConstant (φ' : (κ → R) → ℂ) ∧ HasCompactSupport (φ' : (κ → R) → ℂ) := φ'.2
  have hcont : Continuous (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) :=
    (Complex.continuous_conj.comp hφ.1.continuous).mul hφ'.1.continuous
  have hsupp : HasCompactSupport
      (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) :=
    HasCompactSupport.mul_left (f := fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x)) hφ'.2
  letI : MeasurableSpace (κ → R) := borel _
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  exact Continuous.integrable_of_hasCompactSupport hcont hsupp


omit [CommRing R] [IsTopologicalRing R] in
def form {κ : Type} (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ) :
    SB (κ → R) →ₗ⋆[ℂ] SB (κ → R) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ φ' => pair μ φ φ')
    (fun φ₁ φ₂ φ' => by
      unfold pair
      rw [← integral_add (integrable_pair μ hμ φ₁ φ') (integrable_pair μ hμ φ₂ φ')]
      congr 1
      funext x
      simp [add_mul])
    (fun a φ φ' => by
      unfold pair
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext x
      simp [mul_assoc])
    (fun φ φ₁ φ₂ => by
      unfold pair
      rw [← integral_add (integrable_pair μ hμ φ φ₁) (integrable_pair μ hμ φ φ₂)]
      congr 1
      funext x
      simp [mul_add])
    (fun a φ φ' => by
      unfold pair
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext x
      simp [mul_left_comm])


omit [CommRing R] [IsTopologicalRing R] in
theorem pair_conj {κ : Type} (μ : @Measure (κ → R) (borel _)) (φ φ' : (κ → R) → ℂ) :
    (starRingEnd ℂ) (pair μ φ φ') = pair μ φ' φ := by
  show (starRingEnd ℂ) (∫ x, (starRingEnd ℂ) (φ x) * φ' x ∂μ) = ∫ x, (starRingEnd ℂ) (φ' x) * φ x ∂μ
  rw [← @integral_conj (κ → R) (borel _) μ ℂ _ _]
  congr 1
  funext x
  rw [map_mul, Complex.conj_conj, mul_comm]


omit [IsTopologicalRing R] in
theorem pair_pos {κ : Type} (μ : @Measure (κ → R) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (φ : SB (κ → R)) (hφ : φ ≠ 0) :
    0 < (pair μ (φ : (κ → R) → ℂ) φ).re := by
  haveI := hμ
  have hφl : IsLocallyConstant (φ : (κ → R) → ℂ) ∧ HasCompactSupport (φ : (κ → R) → ℂ) := φ.2
  have hcont : Continuous (φ : (κ → R) → ℂ) := hφl.1.continuous
  have hint := integrable_pair μ
    (@Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts _ _ _ (borel _) μ hμ) φ φ
  have hg : ∀ z : ℂ, ((starRingEnd ℂ) z * z).re = Complex.normSq z := by
    intro z
    rw [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hre : (pair μ (φ : (κ → R) → ℂ) φ).re =
      ∫ x, ((starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ : (κ → R) → ℂ) x).re ∂μ :=
    (@integral_re (κ → R) (borel _) μ ℂ _ _ hint).symm
  rw [hre]
  obtain ⟨x0, hx0⟩ : ∃ x, (φ : (κ → R) → ℂ) x ≠ 0 := by
    by_contra hc
    apply hφ
    apply Subtype.ext
    funext x
    by_contra hx
    exact hc ⟨x, hx⟩
  refine (MeasureTheory.integral_pos_iff_support_of_nonneg ?_ ?_).mpr ?_
  · intro x
    show (0 : ℝ) ≤ ((starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ : (κ → R) → ℂ) x).re
    rw [hg]
    exact Complex.normSq_nonneg _
  · exact hint.re
  · have hU : IsOpen ((φ : (κ → R) → ℂ) ⁻¹' {0}ᶜ) := hcont.isOpen_preimage _ isOpen_compl_singleton
    have hsub : (φ : (κ → R) → ℂ) ⁻¹' {0}ᶜ ⊆
        Function.support fun x => ((starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ : (κ → R) → ℂ) x).re := by
      intro x hx
      rw [Function.mem_support, hg]
      exact (Complex.normSq_pos.mpr hx).ne'
    exact lt_of_lt_of_le (hU.measure_pos μ ⟨x0, hx0⟩) (measure_mono hsub)

variable [T2Space R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ]

def sys {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) (d : Darboux B κ)
    (μ : @Measure (κ → R) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    GlobalTheory.CompanionTheory.FinHeis.Sys W (SB (κ → R)) :=
  haveI := locallyCompact_of_goodChar h
  { c := fun w w' => ψ (⅟(2 : R) * B w w')
    rho := fun w =>
      { toFun := fun φ => ⟨d.rho ψ w φ, (schr_law ψ O u d μ w w φ φ h hμ).2.2.1 φ.2⟩
        map_add' := fun φ φ' => Subtype.ext (funext fun x => by simp [Darboux.rho, schr, mul_add])
        map_smul' := fun a φ => Subtype.ext (funext fun x => by simp [Darboux.rho, schr, mul_left_comm]) }
    B := form μ (@Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts _ _ _ (borel _) μ hμ)
    c_add_left := fun x x' y => by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [d.form, map_add (f := _), Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
      ring
    c_add_right := fun x y y' => by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [d.form, map_add (f := _), Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
      ring
    c_self := fun x => by simp [d.form]
    c_norm := fun x y => h.norm_one _
    rho_zero := fun φ => Subtype.ext (schr_law ψ O u d μ 0 0 φ φ h hμ).2.1
    rho_rho := fun w w' φ => Subtype.ext (schr_law ψ O u d μ w w' φ φ h hμ).1
    B_conj := fun φ φ' => pair_conj μ φ φ'
    B_pos := fun φ hφ => pair_pos μ hμ φ hφ
    B_rho := fun w φ φ' => (schr_law ψ O u d μ w w φ φ' h hμ).2.2.2 }

theorem isModel_sys {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) (d : Darboux B κ)
    (μ : @Measure (κ → R) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    IsModel ψ d μ (sys h d μ hμ) := by
  show (∀ w φ, _) ∧ (∀ φ φ', _) ∧ ∀ w w', _
  exact ⟨fun w φ => rfl, fun φ φ' => rfl, fun w w' => rfl⟩

theorem exists_isModel {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) (d : Darboux B κ)
    (μ : @Measure (κ → R) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ S : GlobalTheory.CompanionTheory.FinHeis.Sys W (SB (κ → R)), IsModel ψ d μ S := by
  exact ⟨sys h d μ hμ, isModel_sys h d μ hμ⟩

end GlobalTheory.CompanionTheory.SchrModel
end
end

section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

section Iso

variable {A : Type} [CommRing A] (σ : A →+* A) {ι : Type} [Fintype ι] [DecidableEq ι]

def Iso (D₁ D₂ M : Matrix ι ι A) : Prop := Mᵀ * D₁ * M.map σ = D₂

variable {σ}

omit [DecidableEq ι] in
theorem Iso.mul {D₁ D₂ D₃ M N : Matrix ι ι A} (h : Iso σ D₁ D₂ M) (h' : Iso σ D₂ D₃ N) : Iso σ D₁ D₃ (M * N) := by
  unfold Iso at *
  rw [transpose_mul, Matrix.map_mul, ← h', ← h]
  simp only [Matrix.mul_assoc]

theorem Iso.inv {D₁ D₂ M N : Matrix ι ι A} (h : Iso σ D₁ D₂ M) (hN : M * N = 1) : Iso σ D₂ D₁ N := by
  unfold Iso at *
  have h1 : M.map σ * N.map σ = 1 := by
    rw [← Matrix.map_mul, hN]; exact Matrix.map_one _ (map_zero σ) (map_one σ)
  have h2 : Nᵀ * Mᵀ = 1 := by rw [← transpose_mul, hN, transpose_one]
  calc _ = (Nᵀ * Mᵀ) * D₁ * (M.map σ * N.map σ) := by rw [← h]; simp only [Matrix.mul_assoc]
    _ = D₁ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem Iso.isUnit_det {D₁ D₂ M : Matrix ι ι A} (h : Iso σ D₁ D₂ M) (hD : IsUnit D₂.det) : IsUnit M.det := by
  unfold Iso at h
  rw [← h, det_mul, det_mul, det_transpose] at hD
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hD)

end Iso

section Split

variable {A : Type} [CommRing A] {σ : A →+* A} {β : Type} [Fintype β] [DecidableEq β]

def Wm (A : Type) [CommRing A] (β : Type) [DecidableEq β] : Matrix (β ⊕ β) (β ⊕ β) A := fromBlocks 0 1 1 0

theorem Wm_mul_self : Wm A β * Wm A β = 1 := by
  simp [Wm, fromBlocks_multiply]

theorem Wm_det : IsUnit (Wm A β).det := by
  have := congrArg det (Wm_mul_self (A := A) (β := β))
  rw [det_mul, det_one] at this
  exact IsUnit.of_mul_eq_one _ this

theorem map_one' : (1 : Matrix β β A).map σ = 1 := Matrix.map_one _ (map_zero σ) (map_one σ)

theorem iso_Wm : Iso σ (Wm A β) (Wm A β) (Wm A β) := by
  simp [Iso, Wm, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_map, map_one']

theorem iso_n {s : Matrix β β A} (hs : s.map σ = -sᵀ) : Iso σ (Wm A β) (Wm A β) (fromBlocks 1 s 0 1) := by
  simp [Iso, Wm, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_map, map_one', hs]

theorem iso_col {a b c d : Matrix β β A} (h : Iso σ (Wm A β) (Wm A β) (fromBlocks a b c d)) :
    cᵀ * a.map σ + aᵀ * c.map σ = 0 := by
  simp only [Iso, Wm, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_map] at h
  simpa using (fromBlocks_inj.mp h).1

theorem exists_skew [IsLocalRing A] (hσ : ∀ z, σ (σ z) = z) {w : A} (hw : w + σ w = 1) {z : A} (hz : IsUnit (z - σ z))
    {a b c d : Matrix β β A} (h : Iso σ (Wm A β) (Wm A β) (fromBlocks a b c d)) :
    ∃ s : Matrix β β A, s.map σ = -sᵀ ∧ IsUnit (a + s * c).det := by
  haveI : IsLocalHom σ := ⟨fun x hx => by simpa [hσ] using hx.map σ⟩
  set π := IsLocalRing.residue A with hπ
  set τ := IsLocalRing.ResidueField.map σ with hτ
  have hc : ∀ x, τ (π x) = π (σ x) := fun x => IsLocalRing.ResidueField.map_residue σ x
  have hm : ∀ m : Matrix β β A, (m.map π).map τ = (m.map σ).map π := fun m => by
    ext i j; simp [hc]
  have hdet := (h.isUnit_det Wm_det).map π
  rw [RingHom.map_det, RingHom.mapMatrix_apply, fromBlocks_map] at hdet
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.CompanionTheory.CommonTransversal.exists_skew_isUnit_det τ (a.map π)ᵀ (c.map π)ᵀ
    (fun x => by
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      rw [← hπ, hc, hc, hσ])
    ⟨π z, fun e => by
      have := hz.map π
      rw [map_sub, ← hc, e, sub_self] at this
      exact not_isUnit_zero this⟩
    (by
      have := congrArg (fun m => m.map π) (iso_col h)
      simp only [Matrix.map_add _ (map_add π), Matrix.map_mul, Matrix.map_zero _ (map_zero π)] at this
      rw [transpose_map, transpose_map, transpose_transpose, transpose_transpose, hm, hm, add_comm]
      exact this)
    (fun v h1 h2 => by
      rw [vecMul_transpose] at h1 h2
      have h3 : fromBlocks (a.map π) (b.map π) (c.map π) (d.map π) *ᵥ Sum.elim v 0 = 0 := by
        rw [fromBlocks_mulVec]
        simp [h1, h2]
      have h4 := Matrix.eq_zero_of_mulVec_eq_zero hdet.ne_zero h3
      ext i
      exact congrFun h4 (Sum.inl i))
  choose f hf using (IsLocalRing.residue_surjective (R := A))
  refine ⟨Matrix.of fun i j => w * f (s j i) - σ (w * f (s i j)), ?_, ?_⟩
  · ext i j
    simp [hσ]
  · have e : (Matrix.of fun i j => w * f (s j i) - σ (w * f (s i j))).map π = sᵀ := by
      ext i j
      have h5 : τ (s i j) = - s j i := congrFun (congrFun hs1 j) i
      have h6 : π w + τ (π w) = 1 := by rw [hc, ← map_add (f := _), hw, map_one]
      have hf' : ∀ x, π (f x) = x := hf
      simp only [map_apply, of_apply, map_sub, ← hc, map_mul, hf', h5, transpose_apply]
      linear_combination s j i * h6
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hπ, RingHom.map_det, RingHom.mapMatrix_apply,
      Matrix.map_add _ (map_add π), Matrix.map_mul, e, ← det_transpose, transpose_add, transpose_mul, transpose_transpose]
    exact hs2.ne_zero

theorem decomp_split [IsLocalRing A] (hσ : ∀ z, σ (σ z) = z) {w : A} (hw : w + σ w = 1) {z : A} (hz : IsUnit (z - σ z))
    {h : Matrix (β ⊕ β) (β ⊕ β) A} (hh : Iso σ (Wm A β) (Wm A β) h) :
    ∃ s u t b d : Matrix β β A, Iso σ (Wm A β) (Wm A β) (fromBlocks 1 s 0 1) ∧
      Iso σ (Wm A β) (Wm A β) (fromBlocks 1 u 0 1) ∧ Iso σ (Wm A β) (Wm A β) (fromBlocks t b 0 d) ∧ IsUnit t.det ∧
      h = fromBlocks 1 s 0 1 * (Wm A β * fromBlocks 1 u 0 1 * Wm A β) * fromBlocks t b 0 d := by
  rw [← fromBlocks_toBlocks h] at hh ⊢
  generalize h.toBlocks₁₁ = a at *
  generalize h.toBlocks₁₂ = b at *
  generalize h.toBlocks₂₁ = c at *
  generalize h.toBlocks₂₂ = d at *
  obtain ⟨s, hs, ha⟩ := exists_skew hσ hw hz hh
  have h1 := (iso_n hs).mul hh
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, zero_add] at h1
  set a' := a + s * c with ha'
  have h2 := iso_col h1
  have i1 : a' * a'⁻¹ = 1 := mul_nonsing_inv _ ha
  have i2 : a'⁻¹ * a' = 1 := nonsing_inv_mul _ ha
  have i3 : a'.map σ * a'⁻¹.map σ = 1 := by rw [← Matrix.map_mul, i1, map_one']
  have i4 : a'⁻¹ᵀ * a'ᵀ = 1 := by rw [← transpose_mul, i1, transpose_one]
  have hu : (c * a'⁻¹).map σ = -(c * a'⁻¹)ᵀ := by
    have := congrArg (fun m => a'⁻¹ᵀ * m * a'⁻¹.map σ) h2
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul] at this
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, i4, Matrix.mul_assoc _ (a'.map σ), i3] at this
    rw [Matrix.map_mul, transpose_mul, eq_neg_iff_add_eq_zero, add_comm]
    simpa using this
  have hs' : (-s).map σ = -(-s)ᵀ := by rw [Matrix.map_neg _ (map_neg σ), hs, transpose_neg]
  have hu' : (-(c * a'⁻¹)).map σ = -(-(c * a'⁻¹))ᵀ := by rw [Matrix.map_neg _ (map_neg σ), hu, transpose_neg]
  have h3 := ((iso_Wm.mul (iso_n hu')).mul iso_Wm).mul h1
  have e3 : Wm A β * fromBlocks 1 (-(c * a'⁻¹)) 0 1 * Wm A β * fromBlocks a' (b + s * d) c d =
      fromBlocks a' (b + s * d) 0 (d - c * a'⁻¹ * (b + s * d)) := by
    simp [Wm, fromBlocks_multiply, Matrix.mul_assoc, i2, sub_eq_neg_add]
  rw [e3] at h3
  refine ⟨-s, c * a'⁻¹, a', _, _, iso_n hs', iso_n hu, h3, ha, ?_⟩
  rw [Matrix.mul_assoc]
  have e4 : Wm A β * fromBlocks 1 (c * a'⁻¹) 0 1 * Wm A β * fromBlocks a' (b + s * d) 0 (d - c * a'⁻¹ * (b + s * d)) =
      fromBlocks a' (b + s * d) c d := by
    simp [Wm, fromBlocks_multiply, Matrix.mul_assoc, i2]
  rw [e4]
  simp [fromBlocks_multiply, ha']

end Split

section Lift

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E} {σ : A →+* A}
  {ι : Type} [Fintype ι] [DecidableEq ι]

end Lift

end GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
end
