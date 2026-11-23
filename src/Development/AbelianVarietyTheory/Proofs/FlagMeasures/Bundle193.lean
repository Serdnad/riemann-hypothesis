module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle031
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle111
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
public import Formalism.HarderNarasimhan.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle174
public import Formalism.RealPlaceAnalysis.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle175
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadFullFlag

theorem form_uMat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star (uMat g *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat g *ᵥ y)) = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc, h]

private theorem dotProduct_Jm_uMat_sub_one {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat g - 1) *ᵥ y)) =
      -(star ((uMat g - 1) *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)) -
        star ((uMat g - 1) *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat g - 1) *ᵥ y)) := by
  have h := form_uMat g x y
  simp only [sub_mulVec, one_mulVec, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct] at h ⊢
  linear_combination h

theorem flagN_eq_lowers : ∀ (n a : ℕ) (ε : Fin n → Bool) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (W' : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsDualFlag (Formalism.REAL.Jm ε) W (2 * a + 1) → W (2 * a + 1) = ⊤ → (∀ i : Fin (a + 1), W' i = W i) → flagN ε W' = {g | uMat g - 1 ∈ lowers W 0} := by
  intro n a ε W W' hF htop hW'
  obtain ⟨hmono, -, hstab, hdual⟩ := hF
  have hmem : ∀ y, y ∈ W (2 * a + 1) := fun y => by rw [htop]; exact Submodule.mem_top

  have horth : ∀ b, b ≤ 2 * a + 1 → ∀ y,
      y ∈ W (2 * a + 1 - b) ↔ ∀ x ∈ W b, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 :=
    fun b hb y => (hdual b hb y).trans ⟨fun h => h.2, fun h => ⟨hmem y, h⟩⟩
  ext g
  have hsub : ∀ y, (uMat g - 1) *ᵥ y = uMat g *ᵥ y - y := fun y => by
    rw [sub_mulVec, one_mulVec]
  unfold GlobalTheory.FlagMeas.flagN
  simp only [Set.mem_setOf_eq, mem_lowers, add_zero]
  constructor
  · rintro ⟨h1, h2⟩

    have hlow : ∀ b, b < a → ∀ y ∈ W (b + 1), (uMat g - 1) *ᵥ y ∈ W b := by
      intro b hb y hy
      have := h1 ⟨b, hb⟩ y (by rw [hW']; exact hy)
      rw [hW'] at this
      rw [hsub]; exact this
    have hmid : ∀ y ∈ W (a + 1), (uMat g - 1) *ᵥ y ∈ W a := by
      intro y hy
      have hy' : ∀ x ∈ W' (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
        rw [hW']
        have e : 2 * a + 1 - a = a + 1 := by omega
        exact (horth a (by omega) y).1 (by rw [e]; exact hy)
      have := h2 y hy'
      rw [hW'] at this
      rw [hsub]; exact this

    have hup : ∀ k, k ≤ a → ∀ y ∈ W (2 * a + 1 - k + 1),
        (uMat g - 1) *ᵥ y ∈ W (2 * a + 1 - k) := by
      intro k
      induction k with
      | zero =>
        intro _ y _
        simpa using hmem ((uMat g - 1) *ᵥ y)
      | succ k ih =>
        intro hk y hy
        rw [horth (k + 1) (by omega)]
        intro x hx
        have hx' : (uMat g - 1) *ᵥ x ∈ W k := hlow k (by omega) x hx
        have hyk : y ∈ W (2 * a + 1 - k) := by
          have e : 2 * a + 1 - (k + 1) + 1 = 2 * a + 1 - k := by omega
          rw [e] at hy; exact hy
        have hgy : (uMat g - 1) *ᵥ y ∈ W (2 * a + 1 - k) :=
          ih (by omega) y (hmono (by omega : 2 * a + 1 - k ≤ 2 * a + 1 - k + 1) hyk)
        rw [dotProduct_Jm_uMat_sub_one, (horth k (by omega) y).1 hyk _ hx',
          (horth k (by omega) _).1 hgy _ hx']
        simp
    intro b y hy
    rcases lt_trichotomy b a with hb | hb | hb
    · exact hlow b hb y hy
    · subst hb; exact hmid y hy
    · by_cases hbm : 2 * a + 1 ≤ b
      · rw [hstab b hbm]; exact hmem _
      · have hk : b = 2 * a + 1 - (2 * a + 1 - b) := by omega
        have := hup (2 * a + 1 - b) (by omega) y (by rw [← hk]; exact hy)
        rw [← hk] at this; exact this
  · intro h
    refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
    · rw [hW'] at hy ⊢
      rw [← hsub]; exact h i y hy
    · rw [hW'] at hy ⊢
      have hy' : y ∈ W (a + 1) := by
        have e : 2 * a + 1 - a = a + 1 := by omega
        rw [← e]; exact (horth a (by omega) y).2 hy
      rw [← hsub]; exact h a y hy'

end GlobalTheory.RadFullFlag
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem mul_eq_zero_of_mulVec_mulVec {p q n : ℕ} {A : Matrix (Fin p) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin q) ℂ} (h : ∀ x, A *ᵥ (B *ᵥ x) = 0) : A * B = 0 := by
  ext i j
  have hx := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hx
  simpa using hx

theorem Biorth.col_mem {n m : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ}
    (hT : Biorth r m T T') (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (s k : ℕ) (hk : s < k) (x : Fin (r s) → ℂ) : T s *ᵥ x ∈ W k := by
  rw [hW]
  intro b hb
  rw [Matrix.mulVec_mulVec, hT.2.1 b s (by omega), Matrix.zero_mulVec]

theorem Biorth.mul_eq_block {n m p q : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ}
    (hT : Biorth r m T T') (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (b : ℕ) {A : Matrix (Fin p) (Fin n) ℂ} {B : Matrix (Fin n) (Fin q) ℂ}
    (hA : ∀ y ∈ W b, A *ᵥ y = 0) (hB : ∀ x, B *ᵥ x ∈ W (b + 1)) :
    A * B = (A * T b) * (T' b * B) := by
  have hAT : ∀ c, c < b → A * T c = 0 := fun c hc =>
    mul_eq_zero_of_mulVec_mulVec fun x => hA _ (Biorth.col_mem hT hW c b hc x)
  have hTB : ∀ c, b < c → T' c * B = 0 := fun c hc =>
    mul_eq_zero_of_mulVec_mulVec fun x => (hW (b + 1) _).1 (hB x) c (by omega)
  calc A * B = A * (∑ c ∈ Finset.range m, T c * T' c) * B := by rw [hT.2.2, Matrix.mul_one]
    _ = ∑ c ∈ Finset.range m, (A * T c) * (T' c * B) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.mul_assoc]
    _ = (A * T b) * (T' b * B) := by
      apply Finset.sum_eq_single b
      · intro c _ hcb
        rcases lt_or_gt_of_ne hcb with hc | hc
        · rw [hAT c hc, Matrix.zero_mul]
        · rw [hTB c hc, Matrix.mul_zero]
      · intro hb

        have hTb : T b = 0 := by
          rw [← Matrix.one_mul (T b), ← hT.2.2, Matrix.sum_mul]
          apply Finset.sum_eq_zero
          intro c hc
          rw [Matrix.mul_assoc, hT.2.1 c b (by rintro rfl; exact hb hc), Matrix.mul_zero]
        rw [hTb, Matrix.mul_zero, Matrix.zero_mul]

theorem blockFrames_triangular (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ)
    (T U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (T' U' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ)
    (hT : Biorth r m T T') (hU : Biorth r m U U')
    (hWT : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (hWU : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → U' b *ᵥ y = 0) :
    (∀ b, (U' b * T b) * (T' b * U b) = 1) ∧ ∀ c, ∀ Y ∈ lowers W c, ∀ b,
      U' b * Y * U (b + c + 1) =
        (U' b * T b) * (T' b * Y * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) := by
  refine ⟨fun b => ?_, fun c Y hY b => ?_⟩
  · rw [← Biorth.mul_eq_block hT hWT b (fun y hy => (hWU b y).1 hy b le_rfl)
      (fun x => Biorth.col_mem hU hWU b (b + 1) (by omega) x)]
    exact hU.1 b
  · have hY' : ∀ b', ∀ y ∈ W (b' + c + 1), Y *ᵥ y ∈ W b' := mem_lowers.1 hY
    have e1 : U' b * (Y * U (b + c + 1)) = (U' b * T b) * (T' b * (Y * U (b + c + 1))) :=
      Biorth.mul_eq_block hT hWT b (fun y hy => (hWU b y).1 hy b le_rfl) (fun x => by
        rw [← Matrix.mulVec_mulVec]
        exact hY' (b + 1) _ (Biorth.col_mem hU hWU (b + c + 1) (b + 1 + c + 1) (by omega) x))
    have e2 : (T' b * Y) * U (b + c + 1) =
        ((T' b * Y) * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) :=
      Biorth.mul_eq_block hT hWT (b + c + 1)
        (fun y hy => by
          rw [← Matrix.mulVec_mulVec]
          exact (hWT b _).1 (hY' b y hy) b le_rfl)
        (fun x => Biorth.col_mem hU hWU (b + c + 1) (b + c + 1 + 1) (by omega) x)
    calc U' b * Y * U (b + c + 1) = U' b * (Y * U (b + c + 1)) := Matrix.mul_assoc _ _ _
      _ = (U' b * T b) * (T' b * (Y * U (b + c + 1))) := e1
      _ = (U' b * T b) * ((T' b * Y) * U (b + c + 1)) := by rw [Matrix.mul_assoc (T' b)]
      _ = _ := by rw [e2]; simp only [Matrix.mul_assoc]

end GlobalTheory.RadCov
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.LocDual

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_smul_mem (G : Submodule (𝓞 E) (Fin n → E))
    (h : Submodule.span E (G : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ G := by
  first
  | exact @_root_.GlobalTheory.DenominatorTheorem.main_theorem
  | exact _root_.GlobalTheory.DenominatorTheorem.main_theorem
  | (apply _root_.GlobalTheory.DenominatorTheorem.main_theorem <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorTheorem.main_theorem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorTheorem.main_theorem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorTheorem.main_theorem ..)

theorem mem_locFlag_of_smul (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) {c : 𝓞 E} (hc : c ≠ 0) {y : Fin n → E}
    (hy : c • y ∈ F b) : (P⁻¹ *ᵥ fun l => φ (y l)) ∈ locFlag φ P F b := by
  have hc1 : φ (algebraMap (𝓞 E) E c) ≠ 0 := by simpa using hc
  have e : (fun l => φ (y l)) = (φ (algebraMap (𝓞 E) E c))⁻¹ • fun l => φ ((c • y) l) := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
  rw [e, Matrix.mulVec_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hy, rfl⟩)

omit [NumberField E] in
theorem mulVec_mem_of_span (φ : E →+* ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (S : Set (Fin n → E))
    (W : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ S, (Q *ᵥ fun l => φ (y l)) ∈ W) {u : Fin n → ℂ}
    (hu : u ∈ Submodule.span ℂ ((fun w : Fin n → E => fun i => φ (w i)) '' S)) : Q *ᵥ u ∈ W := by
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨y, hy, rfl⟩ := hx; exact h y hy
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact W.smul_mem _ hx

theorem form_frame {P K M : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : Pᴴ * K * P = M)
    (u v : Fin n → ℂ) : star (P⁻¹ *ᵥ u) ⬝ᵥ (M *ᵥ v) = star u ⬝ᵥ (K *ᵥ (P *ᵥ v)) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have e : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.one_mul]

omit [NumberField E] in
theorem form_emb [StarRing E] (φ : E →+* ℂ) (hφ : ∀ x, φ (star x) = starRingEnd ℂ (φ x))
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    star (fun l => φ (x l)) ⬝ᵥ (J.map φ *ᵥ fun l => φ (y l)) = φ (star x ⬝ᵥ (J *ᵥ y)) := by

  simp [dotProduct, Matrix.mulVec, map_sum, map_mul, hφ]

theorem locDual : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n m : ℕ) (J : Matrix (Fin n) (Fin n) E) (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (F : ℕ → Submodule (𝓞 E) (Fin n → E)), (∀ x, φ (star x) = starRingEnd ℂ (φ x)) → IsUnit P → Pᴴ * J.map φ * P = Formalism.REAL.Jm ε → IsDualFlag J F m → Submodule.span E (F m : Set (Fin n → E)) = ⊤ → IsDualFlag (Formalism.REAL.Jm ε) (locFlag φ P F) m ∧ locFlag φ P F m = ⊤ := by
  intro E _ _ _ n m J φ P ε F hφ hP hJ hF hsp
  classical
  obtain ⟨hmono, h0, hm, hd⟩ := hF
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hinv : ∀ z : Fin n → ℂ, P⁻¹ *ᵥ (P *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hinv' : ∀ z : Fin n → ℂ, P *ᵥ (P⁻¹ *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have htop : locFlag φ P F m = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    rw [← hinv z]
    refine mulVec_mem_of_span φ _ _ _ ?_
      (GlobalTheory.PerpBaseChange.mem_span_of_forms φ ∅ (P *ᵥ z) (by simp))
    intro y _
    obtain ⟨c, hc, hy⟩ := exists_smul_mem _ hsp y
    exact mem_locFlag_of_smul φ P F m hc hy
  refine ⟨⟨?_, ?_, ?_, ?_⟩, htop⟩
  · intro a b hab
    exact Submodule.span_mono (Set.image_mono (hmono hab))
  · unfold locFlag
    rw [Submodule.span_eq_bot]
    rintro _ ⟨y, hy, rfl⟩
    rw [h0] at hy
    have : y = 0 := by simpa using hy
    subst this
    have e : (fun l => φ ((0 : Fin n → E) l)) = 0 := by funext l; simp
    simp only [e, Matrix.mulVec_zero]
  · intro b hb
    unfold locFlag
    rw [hm b hb]
  · intro b hb z
    constructor
    · intro hz
      refine ⟨by rw [htop]; trivial, fun x hx => ?_⟩
      induction hz using Submodule.span_induction with
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, dotProduct_add, hx, hy, add_zero]
      | smul c x _ hx => rw [Matrix.mulVec_smul, dotProduct_smul, hx, smul_zero]
      | mem z hz =>
        obtain ⟨y, hy, rfl⟩ := hz
        induction hx using Submodule.span_induction with
        | zero => simp
        | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
        | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]
        | mem a ha =>
          obtain ⟨v, hv, rfl⟩ := ha
          rw [form_frame hP hJ, hinv', form_emb φ hφ, ((hd b hb y).1 hy).2 v hv, map_zero]
    · rintro ⟨-, hz⟩
      rw [← hinv z]
      let f : (Fin n → E) → Module.Dual E (Fin n → E) := fun x =>
        { toFun := fun y => star x ⬝ᵥ (J *ᵥ y)
          map_add' := fun y y' => by rw [Matrix.mulVec_add, dotProduct_add]
          map_smul' := fun c y => by rw [Matrix.mulVec_smul, dotProduct_smul]; rfl }
      have hf : ∀ x y, f x y = star x ⬝ᵥ (J *ᵥ y) := fun _ _ => rfl
      refine mulVec_mem_of_span φ _ _ _ ?_
        (GlobalTheory.PerpBaseChange.mem_span_of_forms φ (f '' (F b : Set _)) (P *ᵥ z) ?_)
      · intro y hy
        obtain ⟨c, hc, hcy⟩ := exists_smul_mem _ hsp y
        refine mem_locFlag_of_smul φ P F _ hc ((hd b hb _).2 ⟨hcy, fun x hx => ?_⟩)
        have h1 : star x ⬝ᵥ (J *ᵥ y) = 0 := hy (f x) ⟨x, hx, rfl⟩
        rw [Matrix.mulVec_smul, dotProduct_smul, h1, smul_zero]
      · rintro _ ⟨x, hx, rfl⟩
        have h1 := hz _ (Submodule.subset_span ⟨x, hx, rfl⟩)
        rw [form_frame hP hJ] at h1
        rw [← h1]
        generalize P *ᵥ z = u
        simp only [hf, Matrix.mulVec_single_one]

        simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hφ, Finset.sum_mul, Finset.mul_sum,
        Pi.star_apply, Matrix.map_apply, Matrix.col_apply, mul_assoc]
        rw [Finset.sum_comm]
        rfl

end GlobalTheory.LocDual
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.HomCovolumeFamily

attribute [local instance] GlobalTheory.HomCovolume.haar_two GlobalTheory.HomCovolume.haar_three

theorem exists_twist {E : Type} [Field E] (φ : E →+* ℂ) :
    ∃ σ : ℂ ≃ₐ[ℝ] ℂ, (∀ x, ‖σ x‖ = ‖x‖) ∧ ∀ x, (InfinitePlace.mk φ).embedding x = σ (φ x) := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨AlgEquiv.refl, fun _ => rfl, fun x => by rw [h]; rfl⟩
  · exact ⟨Complex.conjAe, fun x => by simp, fun x => by rw [h]; rfl⟩

theorem det_map_twist {j : ℕ} (σ : ℂ ≃ₐ[ℝ] ℂ) (A : Matrix (Fin j) (Fin j) ℂ) :
    (A.map σ).det = σ A.det := by
  have := RingHom.map_det (σ : ℂ →+* ℂ) A
  rw [RingHom.mapMatrix_apply] at this
  exact this.symm

theorem map_inv_twist {j : ℕ} (σ : ℂ ≃ₐ[ℝ] ℂ) (A : Matrix (Fin j) (Fin j) ℂ) (hA : A.det ≠ 0) :
    (A⁻¹).map σ = (A.map σ)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]

variable {E : Type} [Field E] [NumberField E]

theorem detNorm_twist {ι : Type} [Fintype ι] (e : ι ≃ InfinitePlace E) (σ : ι → ℂ ≃ₐ[ℝ] ℂ)
    (hσ : ∀ v x, ‖σ v x‖ = ‖x‖) {j : ℕ} (G : ι → Matrix (Fin j) (Fin j) ℂ) :
    GlobalTheory.FlagMeas.detNorm E j (fun w => Matrix.of.symm ((G (e.symm w)).map (σ (e.symm w)))⁻¹) =
      (∏ v, ‖(G v).det‖ ^ 2)⁻¹ := by
  change ∏ w, ‖(Matrix.of (Matrix.of.symm ((G (e.symm w)).map (σ (e.symm w)))⁻¹)).det‖ ^ 2 = _
  rw [← Finset.prod_inv_distrib, ← e.prod_comp]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_inv,
    inv_pow, det_map_twist, hσ]

theorem covAt_eq (hE : IsTotallyComplex E) {j : ℕ} (Λ : Submodule (𝓞 E) (Fin j → E))
    (hΛ : Submodule.IsFullLattice E Λ) (g : MatInf E j) (hg : 0 < GlobalTheory.FlagMeas.detNorm E j g) :
    covAt E j (latAt E j Λ g) = covStd j Λ / GlobalTheory.FlagMeas.detNorm E j g := by
  obtain ⟨κ, -, h⟩ := (GlobalTheory.LatFacts.lattice_facts E hE j).1 Λ hΛ
  have h1 : GlobalTheory.FlagMeas.detNorm E j (fun _ a b => if a = b then 1 else 0) = 1 := by
    have h2 : (Matrix.of fun a b : Fin j => if a = b then (1 : ℂ) else 0) = 1 := rfl
    simp only [GlobalTheory.FlagMeas.detNorm, h2, Matrix.det_one, norm_one, one_pow, Finset.prod_const_one]
  have h3 : covStd j Λ = κ := ((h _ (h1.symm ▸ one_pos)).2.1.trans (congrArg (κ / ·) h1)).trans (div_one κ)
  rw [(h g hg).2.1, h3]

theorem homCovolume_family : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ (r s : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin s → E)), Submodule.IsFullLattice E Λ → Submodule.IsFullLattice E Λ' → ∀ (G : ι → Matrix (Fin r) (Fin r) ℂ) (G' : ι → Matrix (Fin s) (Fin s) ℂ), (∀ v, (G v).det ≠ 0) → (∀ v, (G' v).det ≠ 0) → ∀ L : Submodule ℤ (ι → Fin r → Fin s → ℂ), (∀ z, z ∈ L ↔ ∃ T : Matrix (Fin r) (Fin s) E, (∀ y ∈ Λ', T *ᵥ y ∈ Λ) ∧ ∀ v, Matrix.of (z v) = G v * T.map (φ v) * (G' v)⁻¹) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = (covStd r Λ * ∏ v, ‖(G v).det‖ ^ 2) ^ s * (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * s) / (covStd s Λ' * ∏ v, ‖(G' v).det‖ ^ 2)) ^ r := by
  intro E _ _ hE ι _ φ hφ r s Λ Λ' hΛ hΛ' G G' hG hG' L hL
  let e : ι ≃ InfinitePlace E := Equiv.ofBijective _ hφ
  choose σ hσ hσφ using fun v => exists_twist (φ v)
  have he : ∀ v x, (e v).embedding x = σ v (φ v x) := hσφ
  let Φ : (ι → Fin r → Fin s → ℂ) ≃ₗ[ℝ] (InfinitePlace E → Fin r → Fin s → ℂ) :=
    { toFun := fun z w i k => σ (e.symm w) (z (e.symm w) i k)
      invFun := fun y v i k => (σ v).symm (y (e v) i k)
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun c z => funext fun w => funext fun i => funext fun k =>
        (σ (e.symm w)).toLinearEquiv.map_smul c (z (e.symm w) i k)
      left_inv := fun _ => by ext; simp
      right_inv := fun _ => by ext; simp }
  have hΦ : ∀ z v i k, Φ z (e v) i k = σ v (z v i k) := fun z v i k => by
    change σ (e.symm (e v)) (z (e.symm (e v)) i k) = _
    rw [e.symm_apply_apply]
  have hmp : MeasurePreserving Φ.toContinuousLinearEquiv volume volume := by
    refine GlobalTheory.HomCovolume.measurePreserving_of_ball _ _ _ (fun x => ?_) ?_
    · simp only [pi_norm_le_iff_of_nonneg zero_le_one]
      change (∀ w i k, ‖Φ x w i k‖ ≤ 1) ↔ _
      rw [e.forall_congr_right.symm]
      simp only [hΦ, hσ]
    · simp [volume_pi_closedBall _ zero_le_one, Fintype.card_congr e]
  have hD : 0 < ∏ v, ‖(G v).det‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hG v)) _
  have hD' : 0 < ∏ v, ‖(G' v).det‖ ^ 2 := Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 (hG' v)) _
  have hn := detNorm_twist e σ hσ G
  have hn' := detNorm_twist e σ hσ G'
  have hp := hn ▸ inv_pos.2 hD
  have hp' := hn' ▸ inv_pos.2 hD'
  let L' : Submodule ℤ (InfinitePlace E → Fin r → Fin s → ℂ) :=
    L.comap (Φ.symm.toLinearMap.restrictScalars ℤ)
  have hLL : ∀ z, z ∈ L ↔ Φ z ∈ L' := fun z => by
    change _ ↔ Φ.symm (Φ z) ∈ L
    rw [Φ.symm_apply_apply]
  have hmain := GlobalTheory.HomCovolume.homCovolume E hE r s Λ Λ' hΛ hΛ' _ _ hp hp' L' (fun y => by
    obtain ⟨z, rfl⟩ := Φ.surjective y
    rw [← hLL, hL]
    refine exists_congr fun T => and_congr Iff.rfl ?_
    rw [← e.forall_congr_right]
    refine forall_congr' fun v => ?_
    have h1 : Matrix.of (Φ z (e v)) = (Matrix.of (z v)).map (σ v) := by
      ext i k; exact hΦ z v i k
    have h2 : T.map (e v).embedding = (T.map (φ v)).map (σ v) := by
      ext i k; exact he v _
    have h3 : IsUnit ((G v).map (σ v)).det := by
      rw [det_map_twist]; exact ((map_ne_zero _).2 (hG v)).isUnit
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply, h1, h2,
      Matrix.nonsing_inv_nonsing_inv _ h3, ← map_inv_twist _ _ (hG' v), ← Matrix.map_mul, ← Matrix.map_mul]
    exact (Matrix.map_injective (σ v).injective).eq_iff.symm)
  rw [covAt_eq hE Λ hΛ _ hp, covAt_eq hE Λ' hΛ' _ hp', hn, hn', div_inv_eq_mul, div_inv_eq_mul] at hmain
  exact GlobalTheory.HomCovolume.HasCov.of_measurePreserving Φ.toContinuousLinearEquiv hmp hLL hmain

end GlobalTheory.HomCovolumeFamily
end
end

section

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

theorem _root_.GlobalTheory.T.exists_isometric_realisation_of_sublattice' : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (R : Submodule (𝓞 K) (Fin n → K)), (∀ w, IsUnit (X w).det) → R.FG → ∃ (j : ℕ) (i : Matrix (Fin n) (Fin j) K) (X' : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ) (P : InfinitePlace K → Matrix (Fin n) (Fin j) ℂ) (B : Submodule (𝓞 K) (Fin j → K)), j = rkK R ∧ (∀ w, IsUnit (X' w).det) ∧ (∀ w, (P w)ᴴ * P w = 1) ∧ (∀ w, (X w)⁻¹ * i.map w.embedding = P w * (X' w)⁻¹) ∧ B.FG ∧ Submodule.span K (B : Set (Fin j → K)) = ⊤ ∧ (∀ y ∈ B, i *ᵥ y ∈ R) ∧ (∀ r ∈ R, ∃ y ∈ B, i *ᵥ y = r) ∧ largestSize (Pi.basisFun K (Fin j)) X' B = largestSize (Pi.basisFun K (Fin n)) X R := by
  first | exact @GlobalTheory.exists_isometric_realisation_of_sublattice | exact GlobalTheory.exists_isometric_realisation_of_sublattice | (intros; apply GlobalTheory.exists_isometric_realisation_of_sublattice <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.complete_isotropicFrame_signature_eigenvectors : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ), (∀ i, (T i)ᴴ * T i = 1) → (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) → (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) → ∃ (P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ) (Q : Matrix (Fin n) (Fin (q - ∑ i, j i)) ℂ), (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 := by
  first | exact @GlobalTheory.IsoFrame.complete_isotropic_frame | exact GlobalTheory.IsoFrame.complete_isotropic_frame | (intros; apply GlobalTheory.IsoFrame.complete_isotropic_frame <;> assumption)
end
