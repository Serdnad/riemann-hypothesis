module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle078
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle112
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle090
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsScale
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle113
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagLeviGroup

variable {n : ℕ} {ε : Fin n → Bool}

theorem uMat_mul (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem uMat_mul_inv (g : Formalism.REAL.UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul, mul_inv_cancel, uMat_one]

theorem uMat_inv_mul (g : Formalism.REAL.UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul, inv_mul_cancel, uMat_one]

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem inv_keeps {A B : Matrix (Fin n) (Fin n) ℂ} (hBA : B * A = 1) (V : Submodule ℂ (Fin n → ℂ))
    (hA : ∀ y ∈ V, A *ᵥ y ∈ V) : ∀ y ∈ V, B *ᵥ y ∈ V := by
  apply GlobalTheory.RealIwasawa.inv_stable <;> assumption


variable (ε) in
def leviSub {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : Subgroup (Formalism.REAL.UJ ε) where
  carrier := flagM ε W
  one_mem' := by
    intro i y hy
    simpa [uMat_one] using hy
  mul_mem' := by
    intro g h hg hh i y hy
    rw [uMat_mul, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg i _ (hh i y hy).1).1, (hh i _ (hg i y hy).2).2⟩
  inv_mem' := by
    intro g hg i y hy
    refine ⟨inv_keeps (uMat_inv_mul g) (W i) (fun z hz => (hg i z hz).1) y hy,
      inv_keeps (A := (uMat g)ᴴ) ?_ (W i) (fun z hz => (hg i z hz).2) y hy⟩
    rw [← Matrix.conjTranspose_mul, uMat_mul_inv, Matrix.conjTranspose_one]


variable (ε) in
def compactSub : Subgroup (Formalism.REAL.UJ ε) where
  carrier := maxK ε
  one_mem' := by
    show (uMat (1 : Formalism.REAL.UJ ε))ᴴ * uMat (1 : Formalism.REAL.UJ ε) = 1
    simp [uMat_one]
  mul_mem' := by
    intro g h hg hh
    have hg' : (uMat g)ᴴ * uMat g = 1 := hg
    have hh' : (uMat h)ᴴ * uMat h = 1 := hh
    show (uMat (g * h))ᴴ * uMat (g * h) = 1
    rw [uMat_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (uMat g)ᴴ, hg',
      Matrix.one_mul, hh']
  inv_mem' := by
    intro g hg
    have hg' : (uMat g)ᴴ * uMat g = 1 := hg
    have h1 : uMat g⁻¹ = (uMat g)ᴴ := by
      calc uMat g⁻¹ = ((uMat g)ᴴ * uMat g) * uMat g⁻¹ := by rw [hg', Matrix.one_mul]
        _ = (uMat g)ᴴ := by rw [Matrix.mul_assoc, uMat_mul_inv, Matrix.mul_one]
    show (uMat g⁻¹)ᴴ * uMat g⁻¹ = 1
    conv_lhs => enter [1]; rw [h1, Matrix.conjTranspose_conjTranspose]
    exact uMat_mul_inv g

theorem isClosed_flagM {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) : IsClosed (flagM ε W) := by
  have h : flagM ε W = ⋂ i, ⋂ y ∈ W i,
      ((fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) ∩
        (fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ))) := by
    ext g
    simp only [flagM, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
    rfl
  rw [h]
  refine isClosed_iInter fun i => isClosed_iInter fun y => isClosed_iInter fun _ => ?_
  exact ((W i).closed_of_finiteDimensional.preimage
      (continuous_uMat.matrix_mulVec continuous_const)).inter
    ((W i).closed_of_finiteDimensional.preimage
      (continuous_uMat.matrix_conjTranspose.matrix_mulVec continuous_const))

theorem isClosed_maxK : IsClosed (maxK ε) :=
  isClosed_eq (continuous_uMat.matrix_conjTranspose.matrix_mul continuous_uMat) continuous_const

theorem conj_sub (m u : Formalism.REAL.UJ ε) (y : Fin n → ℂ) :
    uMat (m * u * m⁻¹) *ᵥ y - y = uMat m *ᵥ (uMat u *ᵥ (uMat m⁻¹ *ᵥ y) - uMat m⁻¹ *ᵥ y) := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec y (uMat m) (uMat m⁻¹), uMat_mul_inv, Matrix.one_mulVec,
    uMat_mul, uMat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem form_inv (m : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat m⁻¹ *ᵥ y)) = star (uMat m *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  have hm : (uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m = Formalism.REAL.Jm ε := m.2
  have h1 : Formalism.REAL.Jm ε * uMat m⁻¹ = (uMat m)ᴴ * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * uMat m⁻¹ = ((uMat m)ᴴ * Formalism.REAL.Jm ε * uMat m) * uMat m⁻¹ := by rw [hm]
      _ = _ := by rw [Matrix.mul_assoc, uMat_mul_inv, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]

theorem conj_mem_flagN {a : ℕ} (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) {m u : Formalism.REAL.UJ ε}
    (hm : m ∈ flagM ε W) (hu : u ∈ flagN ε W) : m * u * m⁻¹ ∈ flagN ε W := by
  have hm' : m⁻¹ ∈ flagM ε W := (leviSub ε W).inv_mem hm
  refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
  · rw [conj_sub]
    exact (hm _ _ (hu.1 i _ (hm' _ y hy).1)).1
  · rw [conj_sub]
    refine (hm _ _ (hu.2 _ fun x hx => ?_)).1
    rw [form_inv]
    exact hy _ (hm _ x hx).1

theorem levi_compact_subgroups : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)),
    (∃ M : Subgroup (Formalism.REAL.UJ ε), (M : Set (Formalism.REAL.UJ ε)) = flagM ε W) ∧ IsClosed (flagM ε W) ∧
    (∃ K : Subgroup (Formalism.REAL.UJ ε), (K : Set (Formalism.REAL.UJ ε)) = maxK ε) ∧ IsClosed (maxK ε) ∧
    ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W :=
  fun _ ε _ W => ⟨⟨leviSub ε W, rfl⟩, isClosed_flagM W, ⟨compactSub ε, rfl⟩, isClosed_maxK,
    fun _ hm _ hu => conj_mem_flagN W hm hu⟩

end GlobalTheory.FlagLeviGroup
end
end

section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.RealSpan

section General

variable {E A : Type} [Field E] [CommRing A] {n : ℕ}

theorem span_image_span (ι : E →+* A) (S : Set (Fin n → E)) :
    Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S) =
      Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) ''
        (Submodule.span E S : Set (Fin n → E))) := by
  refine le_antisymm (Submodule.span_mono (Set.image_mono Submodule.subset_span)) ?_
  rw [Submodule.span_le]
  rintro _ ⟨w, hw, rfl⟩
  induction hw using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have : (fun i => ι ((0 : Fin n → E) i)) = 0 := by funext i; simp
    simp only [this]
    exact zero_mem _
  | add y z _ _ hy hz =>
    have : (fun i => ι ((y + z) i)) = (fun i => ι (y i)) + fun i => ι (z i) := by funext i; simp
    simp only [this]
    exact add_mem hy hz
  | smul c y _ hy =>
    have : (fun i => ι ((c • y) i)) = ι c • fun i => ι (y i) := by funext i; simp
    simp only [this]
    exact Submodule.smul_mem _ _ hy

theorem span_image_univ (ι : E →+* A) :
    Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' Set.univ) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun A (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine Submodule.subset_span ⟨Pi.single j 1, trivial, ?_⟩
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem map_mulVec_image (ι : E →+* A) (Y : Matrix (Fin n) (Fin n) E) (w : Fin n → E) :
    Y.map ι *ᵥ (fun i => ι (w i)) = fun i => ι ((Y *ᵥ w) i) := by
  funext i

  simp [Matrix.mulVec, dotProduct, map_sum]

theorem map_mulVec_mem (ι : E →+* A) (Y : Matrix (Fin n) (Fin n) E) (S T : Set (Fin n → E))
    (h : ∀ u ∈ S, Y *ᵥ u ∈ T) (u : Fin n → A)
    (hu : u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S)) :
    Y.map ι *ᵥ u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' T) := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    exact Submodule.subset_span ⟨Y *ᵥ w, h w hw, (map_mulVec_image ι Y w).symm⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | smul c y _ hy => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hy

theorem map_mulVec_eq_zero (ι : E →+* A) (Y : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (h : ∀ u ∈ S, Y *ᵥ u = 0) (u : Fin n → A)
    (hu : u ∈ Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' S)) :
    Y.map ι *ᵥ u = 0 := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    rw [map_mulVec_image, h w hw]
    funext i; simp
  | zero => rw [Matrix.mulVec_zero]
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz, add_zero]
  | smul c y _ hy => rw [Matrix.mulVec_smul, hy, smul_zero]

variable (σ : E →+* E) (s : A →+* A) (ι : E →+* A) (hc : ∀ e, s (ι e) = ι (σ e))
  (J : Matrix (Fin n) (Fin n) E)

include hc

theorem isSkew_map (Y : Matrix (Fin n) (Fin n) E) (h : IsSkew σ J Y) :
    IsSkew s (J.map ι) (Y.map ι) := by
  rw [← GlobalTheory.CoverRadiiEq.skew_iff] at h ⊢
  have h1 : Formalism.UG.cT s (Y.map ι) = (Formalism.UG.cT σ Y).map ι := by
    ext i j; simp [Formalism.UG.cT, hc]
  rw [h1, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add ι), h]
  simp

theorem inNil_map (W : Submodule E (Fin n → E)) (Y : Matrix (Fin n) (Fin n) E) (h : InNil σ J W Y) :
    InNil s (J.map ι) (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set (Fin n → E))))
      (Y.map ι) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨isSkew_map σ s ι hc J Y h1, fun u => ?_, fun u hu => ?_, map_mulVec_eq_zero ι Y _ h4⟩
  · rw [GlobalTheory.PerpBaseChange.perpSet_baseChange E A σ s ι n J W hc]
    exact map_mulVec_mem ι Y Set.univ _ (fun u _ => h2 u) u (by rw [span_image_univ]; trivial)
  · rw [GlobalTheory.PerpBaseChange.perpSet_baseChange E A σ s ι n J W hc] at hu
    exact map_mulVec_mem ι Y _ _ h3 u hu

theorem inCen_map (W : Submodule E (Fin n → E)) (Y : Matrix (Fin n) (Fin n) E) (h : InCen σ J W Y) :
    InCen s (J.map ι) (Submodule.span A ((fun w : Fin n → E => fun i => ι (w i)) '' (W : Set (Fin n → E))))
      (Y.map ι) := by
  refine ⟨inNil_map σ s ι hc J W Y h.1, fun u hu => ?_⟩
  rw [GlobalTheory.PerpBaseChange.perpSet_baseChange E A σ s ι n J W hc] at hu
  exact map_mulVec_eq_zero ι Y _ h.2 u hu

end General

section Lattice

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_smul_mem (Λ : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E)
    (hy : y ∈ Submodule.span E (Λ : Set (Fin n → E))) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntegralBoundFlagMeasures.main
  | exact _root_.GlobalTheory.IntegralBoundFlagMeasures.main
  | (apply _root_.GlobalTheory.IntegralBoundFlagMeasures.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralBoundFlagMeasures.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralBoundFlagMeasures.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralBoundFlagMeasures.main ..)

omit [NumberField E] in
theorem mem_perpSet_span (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (S : Set (Fin n → E))
    (y : Fin n → E) :
    y ∈ perpSet σ J (Submodule.span E S) ↔ ∀ w ∈ S, Formalism.UG.hform σ J w y = 0 := by
  refine ⟨fun h w hw => h w (Submodule.subset_span hw), fun h w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem w hw => exact h w hw
  | zero => simp [Formalism.UG.hform]
  | add u v _ _ hu hv => rw [Formalism.UG.P.csScale_hform_add_left, hu, hv, add_zero]
  | smul c u _ hu => rw [Formalism.UG.P.csScale_hform_smul_left, hu, mul_zero]

theorem span_perp (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (Λ R : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    (Submodule.span E (Submodule.span (𝓞 E) {y | y ∈ Λ ∧ ∀ s ∈ R, Formalism.UG.hform σ J s y = 0} :
      Set (Fin n → E)) : Set (Fin n → E)) = perpSet σ J (Submodule.span E (R : Set (Fin n → E))) := by
  rw [Submodule.span_span_of_tower]
  ext y
  rw [mem_perpSet_span]
  constructor
  · intro hy w hw
    induction hy using Submodule.span_induction with
    | mem u hu => exact hu.2 w hw
    | zero => simp [Formalism.UG.hform]
    | add u v _ _ hu hv => rw [Formalism.UG.P.csScale_hform_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [Formalism.UG.P.csScale_hform_smul_right, hu, mul_zero]
  · intro hy
    obtain ⟨c, hc, hcy⟩ := exists_smul_mem Λ y (by rw [hΛ]; trivial)
    have hc1 : algebraMap (𝓞 E) E c ≠ 0 := by simpa using hc
    rw [← algebraMap_smul E c] at hcy
    have : y = (algebraMap (𝓞 E) E c)⁻¹ • algebraMap (𝓞 E) E c • y := by
      rw [smul_smul, inv_mul_cancel₀ hc1, one_smul]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨hcy, fun w hw => ?_⟩)
    rw [Formalism.UG.P.csScale_hform_smul_right, hy w hw, mul_zero]

end Lattice

theorem conj_emb (I : AutInst) (v : InfinitePlace I.F) (e : I.E) :
    starRingEnd ℂ (I.φ v e) = I.φ v (starRingEnd I.E e) :=
  (I.cm.cmUnram.2.1 (I.φ v) e).symm

theorem spanAt_properties : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), (∀ v, spanAt I R v = Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (Submodule.span I.E (R : Set (Fin I.n → I.E)) : Set (Fin I.n → I.E)))) ∧ (∀ v, spanAt I (lamX I x) v = ⊤) ∧ (∀ v, (spanAt I (perpIn I x R) v : Set (Fin I.n → ℂ)) = perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v)) ∧ (∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InNil (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ nilReal I R) ∧ ∀ Y : Matrix (Fin I.n) (Fin I.n) I.E, InCen (starRingEnd I.E) I.J (Submodule.span I.E (R : Set (Fin I.n → I.E))) Y → diagEmb I Y ∈ cenReal I R := by
  intro I x R
  have h1 : ∀ (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) v, spanAt I R v = Submodule.span ℂ
      ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) ''
        (Submodule.span I.E (R : Set (Fin I.n → I.E)) : Set (Fin I.n → I.E))) :=
    fun R v => span_image_span (I.φ v) _
  have hΛ := (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.1
  refine ⟨h1 R, fun v => ?_, fun v => ?_, fun Y hY v => ?_, fun Y hY v => ?_⟩
  · rw [h1, hΛ]
    exact span_image_univ _
  · rw [h1, h1, GlobalTheory.PerpBaseChange.perpSet_baseChange _ _ (starRingEnd I.E) _ _ _ _ _ (conj_emb I v), perpIn,
      span_perp _ _ _ _ hΛ]
  · rw [h1]
    exact inNil_map _ _ _ (conj_emb I v) _ _ Y hY
  · rw [h1]
    exact inCen_map _ _ _ (conj_emb I v) _ _ Y hY

end GlobalTheory.RealSpan
end
end

section

open Formalism.MainNotions.S NumberField GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

namespace GlobalTheory.StepTens

theorem dAct_tens_of_diff (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
    (hd : ∀ v P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w)
    (P : ℕ) (v : InfinitePlace B.I.F) (X : gLie (B.I.ε v)) (u : ∀ v, B.H v)
    (hu : ∀ v, u v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) :
    ∃ u' : ∀ v, B.H v, (∀ v, u' v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) (P + 1)) ∧
      dAct B (atPlace B v X) (B.tens u) = B.tens u' := by
  classical
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  have hloc := (GlobalTheory.StepLoc.stepSpace_props_of_diff B.I.n (B.I.ε v) (B.H v) (B.σ v) (B.lam v) (hU v)
    (hd v) P).2.1 X.1 X.2 (u v) (hu v)
  have h1 : ∀ v, B.σ v 1 = 1 := fun v => (hU v).1.1
  set y := GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct (B.σ v) X.1 (u v) with hy
  have hder : ∀ v', HasDerivAt (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v') (atPlace B v X v').1 (u v'))
      ((Pi.single v y : ∀ v, B.H v) v') 0 := by
    intro v'
    by_cases h : v' = v
    · subst h
      simpa [atPlace] using hloc.1
    · have h0 : atPlace B v X v' = 0 := by
        simp [atPlace, h]
      rw [h0, Pi.single_eq_of_ne h]
      have : GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit (B.σ v') (0 : gLie (B.I.ε v')).1 (u v') = fun _ => u v' := by
        funext t
        simp [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit, h1]
      rw [this]
      exact hasDerivAt_const _ _
  have hT := (GlobalTheory.TensDer.hasDerivAt_orbit_tens B (atPlace B v X) u _ hder h1).deriv
  refine ⟨Function.update u v y, ?_, ?_⟩
  · intro v'
    by_cases h : v' = v
    · subst h
      simpa using hloc.2
    · rw [Function.update_of_ne h]
      exact GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_mono _ _ _ (Nat.le_succ P) (hu v')
  · unfold dAct
    rw [hT, Finset.sum_eq_single v]
    · simp only [Pi.single_eq_same]
    · intro v' _ h
      rw [Pi.single_eq_of_ne h, ← hm]
      exact m.map_coord_zero v' (by simp)
    · simp

theorem wordAct_tens_of_diff (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
    (hd : ∀ v P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w)
    (u : ∀ v, B.H v) (hu : ∀ v, u v ∈ lowKSub (B.I.ε v) (B.lam v) (B.σ v))
    (l : List (Σ v : InfinitePlace B.I.F, gLie (B.I.ε v))) :
    ∃ u' : ∀ v, B.H v, (∀ v, u' v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) l.length) ∧
      wordAct B l (B.tens u) = B.tens u' := by
  induction l with
  | nil =>
    refine ⟨u, fun v => ?_, rfl⟩
    rw [List.length_nil, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_zero]
    exact hu v
  | cons X l ih =>
    obtain ⟨u', h1, h2⟩ := ih
    obtain ⟨u'', h3, h4⟩ := dAct_tens_of_diff B hU hd l.length X.1 X.2 u' h1
    refine ⟨u'', h3, ?_⟩
    rw [← h4, ← h2]
    rfl

theorem stepSpan_le_of_differentiable (B : RowsAut) (hU : ∀ v, IsURepOn (UJset (B.I.ε v)) (B.σ v))
    (hd : ∀ v P, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec (B.I.ε v) (B.σ v) w) (P : ℕ) :
    ∀ w ∈ VP B P, ∃ (k : ℕ) (u : Fin k → ∀ v, B.H v),
      (∀ l v, u l v ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace (B.I.ε v) (B.lam v) (B.σ v) P) ∧ w = ∑ l, B.tens (u l) := by
  classical
  intro w hw
  obtain ⟨m, hm, -⟩ := GlobalTheory.rowsAut_tens_continuousMultilinear B
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, u, hl, hu, rfl⟩ := hx
    obtain ⟨u', h1, h2⟩ := wordAct_tens_of_diff B hU hd u hu l
    exact ⟨1, fun _ => u', fun _ v => GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace_mono _ _ _ hl (h1 v), by simp [h2]⟩
  | zero => exact ⟨0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, u, hu, rfl⟩ := hx
    obtain ⟨k', u', hu', rfl⟩ := hy
    refine ⟨k + k', Fin.append u u', ?_, ?_⟩
    · intro l
      refine Fin.addCases (fun i => ?_) (fun i => ?_) l
      · simpa using hu i
      · simpa using hu' i
    · simp [Fin.sum_univ_add]
  | smul c x _ hx =>
    obtain ⟨k, u, hu, rfl⟩ := hx
    obtain ⟨v₀⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
    refine ⟨k, fun l => Function.update (u l) v₀ (c • u l v₀), ?_, ?_⟩
    · intro l v
      by_cases h : v = v₀
      · subst h
        simpa using Submodule.smul_mem _ c (hu l v)
      · simpa [Function.update_of_ne h] using hu l v
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← hm, ← hm, m.map_update_smul, Function.update_eq_self]

end GlobalTheory.StepTens
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∃ P : Subgroup (Gn g n), ∀ x, x ∈ P ↔ InPar a (x : Mt g n)) ∧ (∃ U : Subgroup (Gn g n), ∀ x, x ∈ U ↔ IsUniUp (x : Mt g n)) ∧ (∀ x : Gn g n, InPar a (x : Mt g n) → IsUnit (tl a (x : Mt g n)) ∧ IsUnit (br a b (x : Mt g n))) ∧ (∀ x y : Mt g n, InPar a x → InPar a y → tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y) ∧ (∀ (h₁ : Gn g a) (h₂ : Gn g b), (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b)).card = g ^ (a * b)) ∧ (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card = Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  first | exact @GlobalTheory.GLm.ParBasic.par_basic | exact GlobalTheory.GLm.ParBasic.par_basic | (intros; apply GlobalTheory.GLm.ParBasic.par_basic <;> assumption)
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.isCharacterOfFDRep_mem_cyclotomic_adjoin : ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ) (N : ℕ), 0 < N → Nat.card G ∣ N → IsChar χ → ∀ x, χ x ∈ IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  first | exact @GlobalTheory.GLm.isChar_mem_adjoin_exp | exact GlobalTheory.GLm.isChar_mem_adjoin_exp | (intros; apply GlobalTheory.GLm.isChar_mem_adjoin_exp <;> assumption)
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.isotypic_trace_eq_of_one_double_coset : ∀ (G : Type) [Group G] [Fintype G] (H H₁ H₂ : Subgroup G) (l₁ : H₁ →* ℂˣ) (l₂ : H₂ →* ℂˣ), H₁ ≤ H → H₂ ≤ H → Nat.card H₁ = Nat.card H₂ → (∀ (a : H₁) (b : H₂), (a : G) = b → l₁ a = l₂ b) → (∀ h ∈ H, h ∉ H₁ → ∃ a a' : H₁, (a' : G) = h⁻¹ * a * h ∧ l₁ a' ≠ l₁ a) → (∀ h ∈ H, h ∉ H₂ → ∃ b b' : H₂, (b' : G) = h⁻¹ * b * h ∧ l₂ b' ≠ l₂ b) → ∀ φ : G → ℂ, IsClass φ → (Nat.card H₁ : ℂ)⁻¹ * ∑ a : H₁, ((l₁ a)⁻¹ : ℂˣ) * φ a = (Nat.card H₂ : ℂ)⁻¹ * ∑ b : H₂, ((l₂ b)⁻¹ : ℂˣ) * φ b := by
  first | exact @GlobalTheory.GLm.OneDoubleCoset.isotypic_trace_eq | exact GlobalTheory.GLm.OneDoubleCoset.isotypic_trace_eq | (intros; apply GlobalTheory.GLm.OneDoubleCoset.isotypic_trace_eq <;> assumption)
end
