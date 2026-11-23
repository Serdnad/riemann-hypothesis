module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle126
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagExplicitConstantLeExpNegHalf
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

private lemma linearIndependent_map_ringHom_complex {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ) {ι : Type}
    [Fintype ι] {v : ι → Fin n → E} (hv : LinearIndependent E v) :
    LinearIndependent ℂ (fun i l => φ (v i l)) := by
  classical

  let f : (ι → E) →ₗ[E] (Fin n → E) := Fintype.linearCombination E v
  have hf : ∀ c, f c = ∑ i, c i • v i := fun c => Fintype.linearCombination_apply E v c
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [hf] at hc
    funext i
    exact (Fintype.linearIndependent_iff.mp hv) c hc i
  obtain ⟨L, hL⟩ := f.exists_leftInverse_of_injective hker
  have hB : ∀ i, LinearMap.toMatrix' L *ᵥ v i = Pi.single i 1 := by
    intro i
    rw [LinearMap.toMatrix'_mulVec]
    have h1 := LinearMap.congr_fun hL (Pi.single i 1)
    have h2 : f (Pi.single i 1) = v i := by
      rw [hf]
      simp [Pi.single_apply]
    rw [LinearMap.comp_apply, h2] at h1
    exact h1
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hcol : ∀ i k, ((LinearMap.toMatrix' L).map φ *ᵥ fun l => φ (v i l)) k
      = if k = i then 1 else 0 := by
    intro i k
    have h3 := RingHom.map_mulVec φ (LinearMap.toMatrix' L) (v i) k
    rw [hB i] at h3
    rw [show (fun l => φ (v i l)) = φ ∘ v i from rfl, ← h3]
    by_cases hki : k = i
    · subst hki; simp
    · simp [hki]
  have h4 := congrArg (fun w => ((LinearMap.toMatrix' L).map φ *ᵥ w) j) hc
  simp only [Matrix.mulVec_zero, Pi.zero_apply] at h4

  rw [← h4, ← Matrix.mulVecLin_apply, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, Matrix.mulVecLin_apply, hcol, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

private lemma map_mem_span_image_of_mem_span {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ)
    (t : Set (Fin n → E)) {x : Fin n → E} (hx : x ∈ Submodule.span E t) :
    (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' t) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
  | zero =>
    have h0 : (fun l => φ ((0 : Fin n → E) l)) = 0 := by funext l; simp
    rw [h0]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    have h1 : (fun l => φ ((y + z) l)) = (fun l => φ (y l)) + (fun l => φ (z l)) := by
      funext l; simp
    rw [h1]
    exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have h1 : (fun l => φ ((c • y) l)) = φ c • (fun l => φ (y l)) := by
      funext l; simp
    rw [h1]
    exact Submodule.smul_mem _ _ hy

theorem finrank_span_image_ringHom {E : Type} [Field E] {n : ℕ} (φ : E →+* ℂ)
    (s : Set (Fin n → E)) :
    Module.finrank ℂ (Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' s))
      = Module.finrank E (Submodule.span E s) := by
  classical
  let V := Submodule.span E s
  let b := Module.finBasis E V
  let v : Fin (Module.finrank E V) → Fin n → E := fun i => (b i : Fin n → E)
  have hv : LinearIndependent E v := b.linearIndependent.map' V.subtype V.ker_subtype
  have hvV : ∀ i, v i ∈ V := fun i => (b i).2
  have hspan : Submodule.span E (Set.range v) = V := by
    have hr : Set.range v = V.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have heq : Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' s)
      = Submodule.span ℂ (Set.range fun i l => φ (v i l)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span E (Set.range v) := by
        rw [hspan]; exact Submodule.subset_span hx
      have h := map_mem_span_image_of_mem_span φ _ hx'
      rw [← Set.range_comp] at h
      exact h
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact map_mem_span_image_of_mem_span φ s (hvV i)
  rw [heq, finrank_span_eq_card (linearIndependent_map_ringHom_complex φ hv), Fintype.card_fin]

theorem finrank_locFlag_and_lowers (E : Type) [Field E] [NumberField E] (n : ℕ) (φ : E →+* ℂ)
    (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (hP : IsUnit P) :
    (∀ b, Module.finrank ℂ (locFlag φ P F b) = Formalism.HN.rkK (F b)) ∧
      ∀ c, ∀ T ∈ lowers F c, P⁻¹ * T.map φ * P ∈ lowers (locFlag φ P F) c := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  refine ⟨fun b => ?_, fun c T hT => ?_⟩
  · have hinj : Function.Injective (Matrix.mulVecLin P⁻¹) := by
      intro x y hxy
      have h := congrArg (fun z => P *ᵥ z) hxy
      simpa [Matrix.mulVec_mulVec, hPP] using h
    have himg : locFlag φ P F b = Submodule.map (Matrix.mulVecLin P⁻¹)
        (Submodule.span ℂ ((fun (y : Fin n → E) l => φ (y l)) '' (F b : Set (Fin n → E)))) := by
      rw [Submodule.map_span, ← Set.image_comp]
      rfl
    rw [himg, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq, finrank_span_image_ringHom]
    rfl
  · rw [GlobalTheory.RadCov.mem_lowers] at hT ⊢
    intro b y hy
    have key : locFlag φ P F (b + c + 1)
        ≤ Submodule.comap (Matrix.mulVecLin (P⁻¹ * T.map φ * P)) (locFlag φ P F b) := by
      rw [locFlag, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
      refine Submodule.subset_span ⟨T *ᵥ x, hT b x hx, ?_⟩
      have h1 : (fun l => φ ((T *ᵥ x) l)) = T.map φ *ᵥ (fun l => φ (x l)) := by
        funext l; exact RingHom.map_mulVec φ T x l
      dsimp only
      rw [h1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc (P⁻¹ * T.map φ) P P⁻¹,
        hPP, Matrix.mul_one]
    exact key hy

end GlobalTheory.RadCov
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.RadCov

open scoped InnerProductSpace

theorem mem_of_orth_piece {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {A B : Submodule ℂ E} (hAB : A ≤ B) {y : E} (hy : y ∈ B)
    (ho : y ∈ (Aᗮ ⊓ B)ᗮ) : y ∈ A := by
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := A) y
  have hwB : w ∈ B := by
    have := B.sub_mem hy (hAB hv)
    simpa using this
  have h1 : ⟪w, v + w⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 ho w ⟨hw, hwB⟩
  have h2 : ⟪w, v⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).1 hw v hv
  rw [inner_add_right, h2, zero_add, inner_self_eq_zero] at h1
  simpa [h1] using hv

theorem exists_orthonormal_family {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (P : Submodule ℂ E) {r : ℕ} (hr : Module.finrank ℂ P = r) :
    ∃ e : Fin r → E, Orthonormal ℂ e ∧ (∀ j, e j ∈ P) ∧
      ∀ y, (∀ j, ⟪e j, y⟫_ℂ = 0) → y ∈ Pᗮ := by
  subst hr
  let b := stdOrthonormalBasis ℂ P
  refine ⟨fun j => (b j : E), ?_, fun j => (b j).2, fun y hy => ?_⟩
  · exact b.orthonormal.comp_linearIsometry P.subtypeₗᵢ
  · rw [Submodule.mem_orthogonal]
    intro u hu
    have h := congrArg (fun x : P => (x : E)) (b.sum_repr ⟨u, hu⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h, sum_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [inner_smul_left, hy j, mul_zero]

theorem exists_orthonormal_block_frame :
    ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ), Monotone W → W 0 = ⊥ →
      (∀ b, m ≤ b → W b = ⊤) →
      (∀ b, Module.finrank ℂ (W (b + 1)) = Module.finrank ℂ (W b) + r b) →
      ∃ U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ, Biorth r m U (fun b => (U b)ᴴ) ∧
        ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0 := by
  intro n m W r hmono h0 htop hr
  let L : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let V : ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin n)) := fun b => (W b).map L.toLinearMap
  have hV : ∀ b y, L y ∈ V b ↔ y ∈ W b := fun b y => by
    simp [V]
  have hVm : Monotone V := fun a b h => Submodule.map_mono (hmono h)
  have hfin : ∀ b, Module.finrank ℂ ((V b)ᗮ ⊓ V (b + 1) : Submodule ℂ _) = r b := fun b => by
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal (hVm (Nat.le_succ b))
    have h2 : ∀ c, Module.finrank ℂ (V c) = Module.finrank ℂ (W c) := fun c =>
      LinearEquiv.finrank_map_eq L (W c)
    rw [h2, h2, hr] at h1
    exact Nat.add_left_cancel h1
  choose e he hmem hdet using fun b => exists_orthonormal_family _ (hfin b)
  let U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ := fun b => Matrix.of fun i j => e b j i
  have hU : ∀ b y j, ((U b)ᴴ *ᵥ y) j = ⟪e b j, L y⟫_ℂ := fun b y j => by
    simp [U, L, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]
  have hUU : ∀ b b' j j', ((U b)ᴴ * U b') j j' = ⟪e b j, e b' j'⟫_ℂ := fun b b' j j' => by
    simp [U, Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  have hflag : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0 := by
    intro k y
    constructor
    · intro hy b hb
      funext j
      rw [hU]
      exact (Submodule.mem_orthogonal' _ _).1 (hmem b j).1 _ (hVm hb ((hV k y).2 hy))
    · intro hy
      have key : ∀ d, L y ∈ V (k + d) → L y ∈ V k := by
        intro d
        induction d with
        | zero => exact id
        | succ d ih =>
          intro h
          refine ih (mem_of_orth_piece (hVm (Nat.le_succ (k + d))) h (hdet _ _ fun j => ?_))
          rw [← hU, hy _ (Nat.le_add_right k d)]
          rfl
      refine (hV k y).1 (key m ((hV _ y).2 ?_))
      rw [htop _ (Nat.le_add_left m k)]
      trivial
  have h1 : ∀ b, (U b)ᴴ * U b = 1 := fun b => by
    ext j j'
    rw [hUU, orthonormal_iff_ite.1 (he b), Matrix.one_apply]
  have hlt : ∀ b b', b' < b → ∀ j j', ⟪e b j, e b' j'⟫_ℂ = 0 := fun b b' h j j' =>
    (Submodule.mem_orthogonal' _ _).1 (hmem b j).1 _ (hVm (Nat.succ_le_of_lt h) (hmem b' j').2)
  have h2 : ∀ b b', b ≠ b' → (U b)ᴴ * U b' = 0 := fun b b' h => by
    ext j j'
    rw [hUU, Matrix.zero_apply]
    rcases lt_or_gt_of_ne h with h | h
    · rw [inner_eq_zero_symm]; exact hlt _ _ h _ _
    · exact hlt _ _ h _ _
  refine ⟨U, ⟨h1, h2, ?_⟩, hflag⟩
  have h3 : ∀ y, (1 - ∑ b ∈ Finset.range m, U b * (U b)ᴴ) *ᵥ y = 0 := by
    intro y
    rw [← Submodule.mem_bot ℂ, ← h0, hflag]
    intro b _
    by_cases hb : m ≤ b
    · refine (hflag m _).1 ?_ b hb
      rw [htop m le_rfl]; trivial
    · rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_sum,
        Finset.sum_eq_single b, ← Matrix.mul_assoc, h1]
      · simp
      · intro c _ hc
        rw [← Matrix.mul_assoc, h2 _ _ hc.symm, Matrix.zero_mul]
      · intro hc
        exact absurd (Finset.mem_range.2 (by omega)) hc
  refine (sub_eq_zero.1 ?_).symm
  ext i k
  have := congrFun (h3 (Pi.single k 1)) i
  simpa using this

end GlobalTheory.RadCov
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.LocSplit

theorem biorth_decomp {K : Type} [CommRing K] {n m : ℕ} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    (h : Biorth r m T T') (y : Fin n → K) :
    y = ∑ b ∈ Finset.range m, T b *ᵥ (T' b *ᵥ y) := by
  have := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ y) h.2.2
  simp only [Matrix.one_mulVec, Matrix.sum_mulVec] at this
  simp only [Matrix.mulVec_mulVec]
  exact this.symm

theorem biorth_map {E K : Type} [CommRing E] [CommRing K] {n m : ℕ} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) E} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) E}
    (h : Biorth r m T T') (φ : E →+* K) {P : Matrix (Fin n) (Fin n) K} (hP : IsUnit P) :
    Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have key : ∀ b b', (T' b).map φ * P * (P⁻¹ * (T b').map φ) = (T' b * T b').map φ := by
    intro b b'
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, h1, Matrix.one_mul, Matrix.map_mul]
  refine ⟨fun b => ?_, fun b b' hb => ?_, ?_⟩
  · rw [key, h.1 b, Matrix.map_one _ (map_zero φ) (map_one φ)]
  · rw [key, h.2.1 b b' hb, Matrix.map_zero _ (map_zero φ)]
  · have e : ∀ b, P⁻¹ * (T b).map φ * ((T' b).map φ * P)
        = P⁻¹ * φ.mapMatrix (T b * T' b) * P := by
      intro b
      rw [RingHom.mapMatrix_apply, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    simp only [e]

    rw [← Finset.sum_mul, ← Finset.mul_sum, ← map_sum, h.2.2, map_one, mul_one, h2]

theorem map_mulVec_comp {E K : Type} [CommRing E] [CommRing K] {n p : ℕ} (φ : E →+* K)
    (A : Matrix (Fin n) (Fin p) E) (y : Fin p → E) :
    A.map φ *ᵥ (fun l => φ (y l)) = fun l => φ ((A *ᵥ y) l) := by
  ext i
  exact (RingHom.map_mulVec φ A y i).symm

theorem block_mem {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule R (Fin n → K)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    {Λ : ∀ b, Submodule R (Fin (r b) → K)} (h : Biorth r m T T')
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0))
    {b k : ℕ} (hb : b < k) {v : Fin (r b) → K} (hv : v ∈ Λ b) : T b *ᵥ v ∈ F k := by
  rw [hF]
  intro b'
  rw [Matrix.mulVec_mulVec]
  by_cases e : b' = b
  · subst e
    rw [h.1, Matrix.one_mulVec]
    exact ⟨hv, fun hk => absurd hk (by omega)⟩
  · rw [h.2.1 _ _ e, Matrix.zero_mulVec]
    exact ⟨zero_mem _, fun _ => rfl⟩

theorem mem_locFlag_iff {E : Type} [Field E] [NumberField E] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule (𝓞 E) (Fin n → E)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) E} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) E}
    {Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)} (h : Biorth r m T T')
    (hΛ : ∀ b, Submodule.IsFullLattice E (Λ b))
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0))
    (φ : E →+* ℂ) {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (k : ℕ) (y : Fin n → ℂ) :
    y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  constructor
  · intro hy b hb
    unfold locFlag at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      have h0 := ((hF k z).1 hz b).2 hb
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one, map_mulVec_comp, h0]
      ext l
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx, smul_zero]
  · intro hy
    rw [biorth_decomp (biorth_map h φ hP) y]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : k ≤ b
    · simp only [hy b hb, Matrix.mulVec_zero]
      exact zero_mem _
    have A : ∀ v : Fin (r b) → E,
        (P⁻¹ * (T b).map φ) *ᵥ (fun l => φ (v l)) ∈ locFlag φ P F k := by
      intro v
      have hv : v ∈ Submodule.span E (Λ b : Set (Fin (r b) → E)) := by
        letI := hΛ b
        rw [Submodule.IsFullLattice.span_eq_top]; trivial
      induction hv using Submodule.span_induction with
      | mem x hx =>
        rw [← Matrix.mulVec_mulVec, map_mulVec_comp]
        exact Submodule.subset_span ⟨_, block_mem h hF (by omega) hx, rfl⟩
      | zero =>
        have : (fun l => φ ((0 : Fin (r b) → E) l)) = 0 := by ext l; simp
        rw [this, Matrix.mulVec_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        have : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + fun l => φ (y l) := by ext l; simp
        rw [this, Matrix.mulVec_add]
        exact add_mem hx hy
      | smul c x _ hx =>
        have : (fun l => φ ((c • x) l)) = φ c • fun l => φ (x l) := by ext l; simp
        rw [this, Matrix.mulVec_smul]
        exact Submodule.smul_mem _ _ hx
    have B : ∀ u : Fin (r b) → ℂ, (P⁻¹ * (T b).map φ) *ᵥ u ∈ locFlag φ P F k := by
      intro u
      have e : u = ∑ j, u j • fun l => φ ((Pi.single j (1 : E) : Fin (r b) → E) l) := by
        ext l
        simp [Finset.sum_apply, Pi.single_apply, apply_ite φ]
      rw [e, Matrix.mulVec_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ _ (A _)
    exact B _

theorem exists_lowers_blocks {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule R (Fin n → K)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    {Λ : ∀ b, Submodule R (Fin (r b) → K)} (h : Biorth r m T T')
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) (c : ℕ)
    (Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) K)
    (hZ : ∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) :
    ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  refine ⟨∑ b : Fin m, T b * Z b * T' (b + c + 1), fun a y hy => ?_, fun a => ?_⟩
  · rw [Matrix.sum_mulVec]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 := (hF _ y).1 hy (b + c + 1)
    by_cases hb : (b : ℕ) < a
    · exact block_mem h hF hb (hZ b _ h1.1)
    · rw [h1.2 (by omega), Matrix.mulVec_zero, Matrix.mulVec_zero]
      exact zero_mem _
  · rw [Matrix.mul_sum, Matrix.sum_mul, Finset.sum_eq_single a]
    · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.1, Matrix.one_mul, Matrix.mul_assoc, h.1,
        Matrix.mul_one]
    · intro b _ hb
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.2.1 _ _ (fun e => hb (Fin.ext e.symm)),
        Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
    · intro ha
      exact absurd (Finset.mem_univ a) ha

theorem locSplit : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' → (∀ b, Submodule.IsFullLattice E (Λ b)) → (∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) → (∀ (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) ∧ ∀ k y, y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0) ∧ ∀ c, (∀ Y ∈ lowers F c, ∀ b, ∀ y ∈ Λ (b + c + 1), (T' b * Y * T (b + c + 1)) *ᵥ y ∈ Λ b) ∧ ∀ Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) E, (∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) → ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  intro E _ _ n m F r T T' Λ h hΛ hF
  refine ⟨fun φ P hP => ⟨biorth_map h φ hP, mem_locFlag_iff h hΛ hF φ hP⟩, fun c => ⟨?_, ?_⟩⟩
  · intro Y hY b y hy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ((hF (b + 1) _).1 (hY (b + 1) _ (block_mem h hF (by omega) hy)) b).1
  · exact exists_lowers_blocks h hF c

end GlobalTheory.RadCov.LocSplit
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.Place

theorem comap_mk_phi (I : AutInst) (v : InfinitePlace I.F) :
    (InfinitePlace.mk (I.φ v)).comap (algebraMap I.F I.E) = v := by
  have h2 : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
  rw [InfinitePlace.comap_mk, h2, InfinitePlace.mk_embedding]

theorem placeMatch : ∀ (I : AutInst) (xf : I.Gf), PlaceMatch I.φ I.P (frm I (1, xf)) := by
  intro I xf
  have hb := GlobalTheory.Count.FrameMajorant.comap_bijective I
  refine ⟨⟨fun v v' h => ?_, fun w => ⟨w.comap (algebraMap I.F I.E), hb.1 (comap_mk_phi I _)⟩⟩, fun v => ?_⟩
  · have h' : InfinitePlace.mk (I.φ v) = InfinitePlace.mk (I.φ v') := h
    rw [← comap_mk_phi I v, h', comap_mk_phi]
  · have he := GlobalTheory.PointEquivariance.embedding_eq I (InfinitePlace.mk (I.φ v))
    have hu : ∀ u, uMat ((((1, xf) : I.GA)).1 u) = 1 := fun u => rfl
    rw [comap_mk_phi] at he
    unfold frm
    rw [comap_mk_phi, hu, Matrix.mul_one]
    by_cases h : (InfinitePlace.mk (I.φ v)).embedding = I.φ v
    · exact Or.inl ⟨h, if_pos h⟩
    · exact Or.inr ⟨he.resolve_left h, if_neg h⟩

end GlobalTheory.RadCov.Place
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.flag_explicit_constant_le_exp_neg_half : ConstantBound := by
  first | exact @GlobalTheory.FlagMeas.constantBound | exact GlobalTheory.FlagMeas.constantBound | (intros; apply GlobalTheory.FlagMeas.constantBound <;> assumption)
end
