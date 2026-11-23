module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle045
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.GNGroup

variable {E : Type} [Field E]

theorem cT_mul (σ : E →+* E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT σ (A * B) = cT σ B * cT σ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_mul' (σ : E →+* E) {n a : ℕ} (A : Matrix (Fin n) (Fin n) E) (B : Matrix (Fin n) (Fin a) E) :
    cT σ (A * B) = cT σ B * cT σ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_mul'' (σ : E →+* E) {n a : ℕ} (A : Matrix (Fin n) (Fin a) E) (B : Matrix (Fin a) (Fin a) E) :
    cT σ (A * B) = cT σ B * cT σ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (σ : E →+* E) {n : ℕ} : cT σ (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  simp [cT]

theorem isUp_iff_bt {m : ℕ} (u : Matrix (Fin m) (Fin m) E) :
    IsUp u ↔ u.BlockTriangular id ∧ ∀ i, u i i = 1 := by
  constructor
  · intro h
    exact ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩
  · rintro ⟨h1, h2⟩ i j
    exact ⟨fun hij => h1 hij, fun hij => hij ▸ h2 i⟩

theorem diag_mul_of_bt {m : ℕ} {A B : Matrix (Fin m) (Fin m) E} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin m) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [hA hl, zero_mul]
    · rw [hB hl, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem isUp_mul {m : ℕ} {u u' : Matrix (Fin m) (Fin m) E} (h : IsUp u) (h' : IsUp u') : IsUp (u * u') := by
  rw [isUp_iff_bt] at h h' ⊢
  refine ⟨h.1.mul h'.1, fun i => ?_⟩
  rw [diag_mul_of_bt h.1 h'.1, h.2, h'.2, one_mul]

theorem isUp_inv {m : ℕ} {u : Matrix (Fin m) (Fin m) E} (h : IsUp u) : IsUp u⁻¹ ∧ u * u⁻¹ = 1 := by
  rw [isUp_iff_bt] at h
  have hdet : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular h.1]
    exact Finset.prod_eq_one fun i _ => h.2 i
  letI : Invertible u.det := { invOf := 1, invOf_mul_self := by simp [hdet], mul_invOf_self := by simp [hdet] }
  letI : Invertible u := Matrix.invertibleOfDetInvertible u
  have hbt : u⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular h.1
  have hui : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u (by rw [hdet]; exact isUnit_one)
  refine ⟨(isUp_iff_bt _).2 ⟨hbt, fun i => ?_⟩, Matrix.mul_nonsing_inv u (by rw [hdet]; exact isUnit_one)⟩
  have := congrFun (congrFun hui i) i
  rw [diag_mul_of_bt hbt h.1, h.2, mul_one] at this
  simpa using this

variable [NumberField E]

theorem latMap_mul {n : ℕ} (g g' : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    latMap (g * g') Λ = latMap g (latMap g' Λ) := by
  ext x
  simp only [latMap, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g' *ᵥ y, ⟨y, hy, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by rw [Matrix.mulVec_mulVec]⟩

theorem latMap_one {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) : latMap 1 Λ = Λ := by
  ext x
  simp [latMap, Submodule.mem_map]

omit [NumberField E] in
theorem isUnit_of_isUn (σ : E →+* E) {n : ℕ} {J g : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0)
    (h : IsUn σ J g) : IsUnit g := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have := congrArg Matrix.det h
  rw [cT, Matrix.det_mul, Matrix.det_mul] at this
  refine isUnit_iff_ne_zero.2 fun h0 => hJ ?_
  rw [h0, mul_zero] at this
  exact this.symm

omit [NumberField E] in
theorem isUn_mul (σ : E →+* E) {n : ℕ} {J g g' : Matrix (Fin n) (Fin n) E} (h : IsUn σ J g)
    (h' : IsUn σ J g') : IsUn σ J (g * g') := by
  unfold IsUn at *
  calc cT σ (g * g') * J * (g * g') = cT σ g' * (cT σ g * J * g) * g' := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [h, h']

omit [NumberField E] in
theorem isUn_inv (σ : E →+* E) {n : ℕ} {J a b : Matrix (Fin n) (Fin n) E} (h : IsUn σ J a)
    (hab : a * b = 1) : IsUn σ J b := by
  unfold IsUn at *
  calc cT σ b * J * b = cT σ b * (cT σ a * J * a) * b := by rw [h]
    _ = cT σ (a * b) * J * (a * b) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [hab, cT_one, Matrix.one_mul, Matrix.mul_one]

omit [NumberField E] in
theorem inN_one (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E) :
    InN σ J P 1 := by
  refine ⟨by simp [IsUn, cT_one], ⟨1, ?_, ?_⟩, fun v _ => ⟨0, by simp⟩⟩
  · intro i j
    exact ⟨fun h => Matrix.one_apply_ne (ne_of_lt h).symm, fun h => by subst h; exact Matrix.one_apply_eq i⟩
  · have key : (1 : Matrix (Fin n) (Fin n) E) * eOf P = eOf P * (1 : Matrix (Fin r) (Fin r) E) := by
      rw [Matrix.one_mul, Matrix.mul_one]
    exact key

omit [NumberField E] in
theorem inN_mul (σ : E →+* E) {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E}
    {g g' : Matrix (Fin n) (Fin n) E} (h : InN σ J P g) (h' : InN σ J P g') : InN σ J P (g * g') := by
  obtain ⟨hu, ⟨ν, hν, he⟩, hp⟩ := h
  obtain ⟨hu', ⟨ν', hν', he'⟩, hp'⟩ := h'
  replace he : g * eOf P = eOf P * ν := he
  replace he' : g' * eOf P = eOf P * ν' := he'
  refine ⟨isUn_mul σ hu hu', ⟨ν * ν', isUp_mul hν hν', ?_⟩, fun v hv => ?_⟩
  · have key : (g * g') * eOf P = eOf P * (ν * ν') := by
      rw [Matrix.mul_assoc, he', ← Matrix.mul_assoc, he, Matrix.mul_assoc]
    exact key
  · obtain ⟨c, hc⟩ := hp v hv
    obtain ⟨c', hc'⟩ := hp' v hv
    refine ⟨ν *ᵥ c' + c, ?_⟩
    have e1 : (g * g') *ᵥ v - v = g *ᵥ (g' *ᵥ v - v) + (g *ᵥ v - v) := by
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_sub]; abel
    rw [e1, hc', hc, Matrix.mulVec_mulVec, he, ← Matrix.mulVec_mulVec, Matrix.mulVec_add]

omit [NumberField E] in
theorem inN_inv (σ : E →+* E) {n r : ℕ} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E}
    {a b : Matrix (Fin n) (Fin n) E} (h : InN σ J P a) (hab : a * b = 1) (hba : b * a = 1) :
    InN σ J P b := by
  obtain ⟨hu, ⟨ν, hν, he⟩, hp⟩ := h
  replace he : a * eOf P = eOf P * ν := he
  obtain ⟨hνi, hνν⟩ := isUp_inv hν
  have hJ : cT σ a * J = J * b := by
    calc cT σ a * J = cT σ a * J * (a * b) := by rw [hab, Matrix.mul_one]
      _ = J * b := by rw [← Matrix.mul_assoc, hu]
  refine ⟨isUn_inv σ hu hab, ⟨ν⁻¹, hνi, ?_⟩, fun v hv => ?_⟩
  · have key : b * eOf P = eOf P * ν⁻¹ := by
      calc b * eOf P = (b * (eOf P * ν)) * ν⁻¹ := by
            rw [Matrix.mul_assoc b, Matrix.mul_assoc, hνν, Matrix.mul_one]
        _ = (b * (a * eOf P)) * ν⁻¹ := by rw [he]
        _ = eOf P * ν⁻¹ := by rw [← Matrix.mul_assoc b, hba, Matrix.one_mul]
    exact key
  · have e2 : cT σ (eOf P) * J * b = cT σ ν * (cT σ (eOf P) * J) := by
      rw [Matrix.mul_assoc, ← hJ, ← Matrix.mul_assoc, ← cT_mul', he, cT_mul'', Matrix.mul_assoc]
    have hw : (cT σ (eOf P) * J) *ᵥ (b *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, e2, ← Matrix.mulVec_mulVec]
      have hv' : (cT σ (eOf P) * J) *ᵥ v = 0 := hv
      rw [hv', Matrix.mulVec_zero]
    obtain ⟨c, hc⟩ := hp _ hw
    refine ⟨-c, ?_⟩
    rw [Matrix.mulVec_mulVec, hab, Matrix.one_mulVec] at hc
    rw [Matrix.mulVec_neg, ← hc]
    abel

end GlobalTheory.SnMass.VolN.GNGroup

namespace GlobalTheory.SnMass.VolN

variable {E : Type} [Field E] [NumberField E]

def gNUnits (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Subgroup (Matrix (Fin n) (Fin n) E)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) E) ∈ GN σ J Λ P}
  one_mem' := by
    show ((1 : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) ∈ GN σ J Λ P
    rw [Units.val_one]
    exact ⟨GNGroup.inN_one _ J P, GNGroup.latMap_one Λ⟩
  mul_mem' := by
    intro a b ha hb
    show ((a * b : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) ∈ GN σ J Λ P
    rw [Units.val_mul]
    exact ⟨GNGroup.inN_mul _ ha.1 hb.1, by rw [GNGroup.latMap_mul, hb.2, ha.2]⟩
  inv_mem' := by
    intro a ha
    show ((a⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) ∈ GN σ J Λ P
    refine ⟨GNGroup.inN_inv _ ha.1 a.mul_inv a.inv_mul, ?_⟩
    calc latMap ((a⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) Λ
        = latMap ((a⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E)
            (latMap (a : Matrix (Fin n) (Fin n) E) Λ) := by rw [ha.2]
      _ = Λ := by rw [← GNGroup.latMap_mul, a.inv_mul, GNGroup.latMap_one]

theorem gN_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → (∃ G : Subgroup (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)ˣ, ∀ u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)ˣ, u ∈ G ↔ (u : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) ∈ GN (σ : E →+* E) J Λ P) ∧ ∀ γ ∈ GN (σ : E →+* E) J Λ P, IsUnit γ := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV
  have hJ : J.det ≠ 0 := hV.2.2.1.2
  exact ⟨⟨gNUnits (σ : E →+* E) J Λ P, fun u => Iff.rfl⟩,
    fun γ hγ => GNGroup.isUnit_of_isUn (σ : E →+* E) hJ hγ.1.1⟩

end GlobalTheory.SnMass.VolN
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

end GlobalTheory.SnMass.VolN

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
private lemma mul_vecMulVec_mul_flag_measures {n : Type} [Fintype n] (M N : Matrix n n ℂ) (u v : n → ℂ) :
    M * vecMulVec u v * N = vecMulVec (M *ᵥ u) (v ᵥ* N) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
private lemma single_vecMul_Hpk_eI (k r : ℕ) (a : Fin r) :
    Pi.single (_root_.Formalism.QuantumDeterminants.eI k r a) 1 ᵥ* _root_.Formalism.QuantumDeterminants.Hpk k r = Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) (1 : ℂ) := by
  funext j
  rw [single_one_vecMul]
  change _root_.Formalism.QuantumDeterminants.Hpk k r (_root_.Formalism.QuantumDeterminants.eI k r a) j = (Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) (1 : ℂ) : _ → ℂ) j
  unfold _root_.Formalism.QuantumDeterminants.Hpk _root_.Formalism.QuantumDeterminants.eI _root_.Formalism.QuantumDeterminants.esI
  simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  have ha := a.isLt
  split_ifs <;> first | rfl | (exfalso; omega)


open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors in
theorem _root_.GlobalTheory.SnMass.VolN.rowE_entries : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), _root_.GlobalTheory.SnMass.VolN.IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E) (w : InfinitePlace E) (i j : Fin (2 * r + k + 1)), _root_.GlobalTheory.SnMass.VolN.gM A (_root_.GlobalTheory.SnMass.VolN.rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t) w i j = (if i = j then 1 else 0) + (if j = _root_.Formalism.QuantumDeterminants.esI k r a then (s a : ℂ) * (((A w).mulVec fun l => w.embedding (y l)) i + (if i = _root_.Formalism.QuantumDeterminants.eI k r a then (s a : ℂ) * w.embedding t else 0)) else 0) - (if i = _root_.Formalism.QuantumDeterminants.eI k r a then (s a : ℂ) * _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.bvec j) ((A w).mulVec fun l => w.embedding (y l)) else 0) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hD a y t w i j
  obtain ⟨hσ, -, hJ, -, -, -, -, hA, -, hAd⟩ := hD
  set x : Fin (2 * r + k + 1) → ℂ := fun l => w.embedding (P l a.castSucc) with hx_def
  set v : Fin (2 * r + k + 1) → ℂ := fun l => w.embedding (y l) with hv_def
  have hconj : ∀ z : E, w.embedding (σ z) = star (w.embedding z) := fun z => hσ.2.2.2 w.embedding z
  have hiso : (A w)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * A w = J.map w.embedding := hA w
  have hAx : A w *ᵥ x = (s a : ℂ) • _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a) := (hAd w a).1
  have hdet : IsUnit (A w).det := by
    have h1 : (J.map w.embedding).det ≠ 0 := by
      rw [show (J.map w.embedding).det = w.embedding J.det from (RingHom.map_det _ _).symm]
      exact (map_ne_zero _).2 hJ.2
    rw [← hiso, det_mul, det_mul] at h1
    exact isUnit_iff_ne_zero.2 (right_ne_zero_of_mul h1)
  have hinv : A w * (A w)⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hrow : ∀ u : Fin (2 * r + k + 1) → ℂ,
      star u ᵥ* J.map w.embedding ᵥ* (A w)⁻¹ = star (A w *ᵥ u) ᵥ* _root_.Formalism.QuantumDeterminants.Hpk k r := by
    intro u
    rw [← hiso, vecMul_vecMul, Matrix.mul_assoc, hinv, Matrix.mul_one, ← vecMul_vecMul,
      ← star_mulVec]
  have hmap : (_root_.GlobalTheory.SnMass.VolN.rowE (σ : E →+* E) J (fun l => P l a.castSucc) y t).map
      w.embedding = 1 + vecMulVec (v + w.embedding t • x) (star x ᵥ* J.map w.embedding) -
        vecMulVec x (star v ᵥ* J.map w.embedding) := by
    ext p q

    simp [_root_.GlobalTheory.SnMass.VolN.rowE, vecMulVec_apply, vecMul, dotProduct, map_sum, hconj,
    one_apply, x, v]
    exact Matrix.one_apply.symm
  unfold _root_.GlobalTheory.SnMass.VolN.gM
  rw [hmap, Matrix.mul_sub, Matrix.mul_add, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_one, hinv,
    mul_vecMulVec_mul_flag_measures, mul_vecMulVec_mul_flag_measures, hrow, hrow, mulVec_add, mulVec_smul, hAx]
  have hstar : star ((s a : ℂ) • _root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a)) ᵥ* _root_.Formalism.QuantumDeterminants.Hpk k r =
      (s a : ℂ) • Pi.single (_root_.Formalism.QuantumDeterminants.esI k r a) 1 := by
    unfold _root_.Formalism.QuantumDeterminants.bvec
    rw [star_smul, ← Pi.single_star, star_one, smul_vecMul, single_vecMul_Hpk_eI, Complex.star_def,
      Complex.conj_ofReal]
  rw [hstar]
  unfold _root_.Formalism.QuantumDeterminants.herm _root_.Formalism.QuantumDeterminants.bvec
  rw [dotProduct_mulVec, dotProduct_single_one]
  simp only [Matrix.add_apply, Matrix.sub_apply, vecMulVec_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, Matrix.one_apply]
  split_ifs <;> ring
end
end

section

noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem det_embed_ne_zero {E : Type} [Field E] [NumberField E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0)
    (w : InfinitePlace E) : (J.map w.embedding).det ≠ 0 := by
  rw [show J.map w.embedding = w.embedding.mapMatrix J from rfl, ← RingHom.map_det]
  exact (map_ne_zero _).mpr hJ

theorem A_isUnit_det {E : Type} [Field E] [NumberField E] {k r : ℕ}
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hJ : J.det ≠ 0) (hA : IsModelAt J A) (w : InfinitePlace E) : IsUnit (A w).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h : ((A w)ᴴ * Hpk k r * A w).det = (J.map w.embedding).det := congrArg Matrix.det (hA w)
  rw [det_mul, det_mul, h0, mul_zero] at h
  exact det_embed_ne_zero J hJ w h.symm

theorem actLaws (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) :
    IsVolData σ J Λ P f T A s → (∀ x, actM A 1 x = x) ∧ (∀ γ γ' x, actM A (γ * γ') x = actM A γ (actM A γ' x)) ∧ ∀ γ, (∀ w, gM A γ w = 1) → γ = 1 := by
  intro h
  have hJ : J.det ≠ 0 := h.2.2.1.2
  have hA : IsModelAt J A := h.2.2.2.2.2.2.2.1
  have hu : ∀ w, IsUnit (A w).det := fun w => A_isUnit_det J A hJ hA w
  refine ⟨?_, ?_, ?_⟩
  · intro x
    funext w
    have e : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E).map w.embedding = 1 :=
      map_one w.embedding.mapMatrix
    simp only [actM, e, Matrix.mul_one, Matrix.mul_nonsing_inv _ (hu w), Matrix.one_mul]
    rfl
  · intro γ γ' x
    funext w
    have e : (γ * γ').map w.embedding = γ.map w.embedding * γ'.map w.embedding :=
      map_mul w.embedding.mapMatrix γ γ'
    have m : A w * (γ.map w.embedding * γ'.map w.embedding) * (A w)⁻¹ * Matrix.of (x w) =
        A w * γ.map w.embedding * (A w)⁻¹ * (A w * γ'.map w.embedding * (A w)⁻¹ * Matrix.of (x w)) := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hu w)]
    show Matrix.of.symm (A w * (γ * γ').map w.embedding * (A w)⁻¹ * Matrix.of (x w)) =
      Matrix.of.symm (A w * γ.map w.embedding * (A w)⁻¹ *
        Matrix.of (Matrix.of.symm (A w * γ'.map w.embedding * (A w)⁻¹ * Matrix.of (x w))))
    rw [Equiv.apply_symm_apply, e, m]
  · intro γ hγ
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hi : (A w)⁻¹ * A w = 1 := Matrix.nonsing_inv_mul _ (hu w)
    have h1 : γ.map w.embedding = 1 := by
      have e : A w * γ.map w.embedding * (A w)⁻¹ = 1 := hγ w
      calc γ.map w.embedding = (A w)⁻¹ * (A w * γ.map w.embedding * (A w)⁻¹) * A w := by
            simp only [Matrix.mul_assoc, hi, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ (hu w)]
        _ = 1 := by rw [e, Matrix.mul_one, hi]
    ext i j
    apply w.embedding.injective
    have := congrArg (fun M => M i j) h1
    simpa [Matrix.one_apply, apply_ite] using this

end GlobalTheory.SnMass.VolN
end
end
