module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory ValuativeRel Matrix Filter Topology
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

namespace GlobalTheory.KSplit

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsSmU (χ : kˣ →* ℂˣ) : Prop := IsOpen (χ.ker : Set kˣ) ∧ ∀ x, ‖(χ x : ℂ)‖ = 1


variable (k) in
def intM (m n : Type) : Set (Matrix m n k) := {X | ∀ i j, X i j ∈ 𝒪[k]}

def IsEqv {n : ℕ} (ν : kˣ →* ℂˣ) (z : ℂ) (l : (Matrix (Fin n) (Fin n) k → ℂ) → ℂ) : Prop :=
  (∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∀ φ' ∈ SB (Matrix (Fin n) (Fin n) k), l (φ + φ') = l φ + l φ') ∧
  (∀ c : ℂ, ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), l (c • φ) = c * l φ) ∧
  ∀ g₁ g₂ : GL (Fin n) k, ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k),
    (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) z * l (fun X => φ (g₁.val * X * g₂.val)) = l φ

def indSp (a a' : ℕ) (α β : kˣ →* ℂˣ) : Submodule ℂ (GL (Fin (a + a')) k → ℂ) where
  carrier := {f | (∀ (b : GL (Fin (a + a')) k) (A : GL (Fin a) k) (D : GL (Fin a') k) (N : Matrix (Fin a) (Fin a') k),
      b.val.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks A.val N 0 D.val → ∀ h, f (b * h) =
        (α (gdet A) : ℂ) * β (gdet D) * apow (gdet A) ((a' : ℂ) / 2) * apow (gdet D) (-(a : ℂ) / 2) * f h) ∧
    ∀ᶠ u in 𝓝 (1 : GL (Fin (a + a')) k), ∀ h, f (h * u) = f h}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun b A D N hb h => ?_, (h2.and h2').mono fun u hu h => ?_⟩
    · simp only [Pi.add_apply, h1 b A D N hb, h1' b A D N hb, mul_add]
    · simp only [Pi.add_apply, hu.1, hu.2]
  zero_mem' := ⟨fun _ _ _ _ _ _ => by simp, Eventually.of_forall fun _ _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨fun b A D N hb h => ?_, h2.mono fun u hu h => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, h1 b A D N hb]; ring
    · simp only [Pi.smul_apply, hu]

def mapA {a : ℕ} (a' : ℕ) (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ) (ν β : kˣ →* ℂˣ)
    (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ) (h : GL (Fin (a + a')) k) : ℂ :=
  l fun g => omA ν β 1 h Φ (g * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))

section Frames

variable {R S D : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]

theorem restrict_mem_SB {P : Matrix R D k} {P' : Matrix D R k} (hP : P * P' = 1) {Φ : Matrix R D k → ℂ}
    (hΦ : Φ ∈ SB (Matrix R D k)) : (fun g : Matrix R R k => Φ (g * P)) ∈ SB (Matrix R R k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have c1 : Continuous fun g : Matrix R R k => g * P := continuous_id.matrix_mul continuous_const
  have c2 : Continuous fun X : Matrix R D k => X * P' := continuous_id.matrix_mul continuous_const
  have e : IsClosedEmbedding fun g : Matrix R R k => g * P :=
    Function.LeftInverse.isClosedEmbedding (f := fun X : Matrix R D k => X * P')
      (fun g => by simp only [Matrix.mul_assoc, hP, Matrix.mul_one]) c2 c1
  exact ⟨hΦ.1.comp_continuous c1, hΦ.2.comp_isClosedEmbedding e⟩


omit [DecidableEq R] [DecidableEq D] in
theorem indicator_intM_mem_SB : (intM k R D).indicator (1 : Matrix R D k → ℂ) ∈ SB (Matrix R D k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hc : IsCompact (intM k R D) := isCompact_intMatrix
  have hK : IsClopen (intM k R D) := ⟨hc.isClosed, isOpen_intMatrix⟩
  exact ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) hK).isLocallyConstant,
    HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩

theorem exists_extend_SB {P : Matrix R D k} {Q : Matrix S D k} (hP : P * Pᵀ = 1) (hQ : P * Qᵀ = 0)
    (hPQ : Pᵀ * P + Qᵀ * Q = 1) {φ : Matrix R R k → ℂ} (hφ : φ ∈ SB (Matrix R R k)) :
    ∃ Φ ∈ SB (Matrix R D k), ∀ g, Φ (g * P) = φ g := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hI := indicator_intM_mem_SB (k := k) (R := R) (D := S)
  have c1 : Continuous fun X : Matrix R D k => X * Pᵀ := continuous_id.matrix_mul continuous_const
  have c2 : Continuous fun X : Matrix R D k => X * Qᵀ := continuous_id.matrix_mul continuous_const
  have c3 : Continuous fun x : Matrix R R k × Matrix R S k => x.1 * P + x.2 * Q :=
    (continuous_fst.matrix_mul continuous_const).add (continuous_snd.matrix_mul continuous_const)
  refine ⟨fun X => φ (X * Pᵀ) * (intM k R S).indicator 1 (X * Qᵀ),
    ⟨(hφ.1.comp_continuous c1).mul (hI.1.comp_continuous c2), ?_⟩, fun g => ?_⟩
  · refine HasCompactSupport.intro ((hφ.2.isCompact.prod hI.2.isCompact).image c3) fun X hX => ?_
    by_contra h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
    refine hX ⟨(X * Pᵀ, X * Qᵀ), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, ?_⟩
    simp only [Matrix.mul_assoc, ← Matrix.mul_add, hPQ, Matrix.mul_one]
  · simp only [Matrix.mul_assoc, hP, hQ, Matrix.mul_one, Matrix.mul_zero]
    rw [Set.indicator_of_mem (show (0 : Matrix R S k) ∈ intM k R S from fun _ _ => zero_mem _)]
    simp


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem frame_rel (σ : R ⊕ S ≃ D) : X0 k σ * (X0 k σ)ᵀ = 1 ∧ Y0 k σ * (Y0 k σ)ᵀ = 1 ∧ X0 k σ * (Y0 k σ)ᵀ = 0 ∧
    Y0 k σ * (X0 k σ)ᵀ = 0 ∧ (X0 k σ)ᵀ * X0 k σ + (Y0 k σ)ᵀ * Y0 k σ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j; rw [frameMatrixFirstColumnBlock_mul_apply]; simp [X0, Matrix.one_apply, eq_comm]
  · ext i j; rw [frameMatrixSecondColumnBlock_mul_apply]; simp [Y0, Matrix.one_apply, eq_comm]
  · ext i j; simp [frameMatrixFirstColumnBlock_mul_apply, Y0]
  · ext i j; simp [frameMatrixSecondColumnBlock_mul_apply, X0]
  · ext i j
    obtain ⟨i | i, rfl⟩ := σ.surjective i <;> obtain ⟨j | j, rfl⟩ := σ.surjective j <;>
      simp [X0, Y0, Matrix.mul_apply, Matrix.one_apply, Function.swap, eq_comm]

end Frames

variable {a a' : ℕ} {z : ℂ} {ν α β : kˣ →* ℂˣ}

theorem restrict_X0 {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ} (hΦ : Φ ∈ SB (Matrix (Fin a) (Fin (a + a')) k)) :
    (fun g : Matrix (Fin a) (Fin a) k => Φ (g * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))) ∈ SB _ :=
  restrict_mem_SB (frame_rel _).1 hΦ

theorem mapA_omA_right (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ) (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ)
    (x h : GL (Fin (a + a')) k) : mapA a' l ν β (omA ν β 1 x Φ) h = mapA a' l ν β Φ (h * x) := by
  unfold mapA
  rw [← omA_mul, one_mul]

end Local

section Adelic

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def locMat {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GL (Fin n) (Fv F v)) :
    UA σ J →* GL (Fin n) (Fv F v) where
  toFun g := b⁻¹ * Matrix.GeneralLinearGroup.map (piW t) g.1 * b
  map_one' := by simp
  map_mul' g h := by simp [mul_assoc]

theorem locMat_val {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (b : GL (Fin n) (Fv F v))
    (g : UA σ J) : (locMat t b g).val = (b⁻¹).val * (mat g).map (piW t) * b.val := rfl

end Adelic

end GlobalTheory.KSplit

end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.SplitFullyNorm

theorem exists_prime_absNorm_eq_of_splitsFully (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (W : HeightOneSpectrum (𝓞 E)) (h : SplitsFully E (W.under (𝓞 F))) :
    ∃ p : ℕ, p.Prime ∧ Ideal.absNorm W.asIdeal = p ∧ (p : 𝓞 E) ∉ W.asIdeal ^ 2 := by
  classical

  set P : Ideal ℤ := W.asIdeal.under ℤ with hPdef
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot W.ne_bot
  haveI hPprime : P.IsPrime := Ideal.IsPrime.under ℤ W.asIdeal
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hP0

  have hunder : (W.under (𝓞 F)).asIdeal.under ℤ = P := by
    change (W.asIdeal.under (𝓞 F)).under ℤ = W.asIdeal.under ℤ
    exact Ideal.under_under _
  have hcard : (P.primesOver (𝓞 E)).ncard = Module.finrank ℚ E := by
    have h' := h
    unfold SplitsFully at h'
    rwa [hunder] at h'

  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [NumberField.RingOfIntegers.rank] at hsum

  have hone : ∀ q : P.primesOver (𝓞 E), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    intro q
    haveI : q.1.IsPrime := q.2.1
    have hpos := Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) q.1) (Ideal.inertiaDeg_pos q.1 ℤ)
    by_contra hne
    have hlt : ∑ _r : P.primesOver (𝓞 E), (1 : ℕ) <
        ∑ r : P.primesOver (𝓞 E), r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := by
      apply Finset.sum_lt_sum
      · intro r _
        haveI : r.1.IsPrime := r.2.1
        exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) r.1) (Ideal.inertiaDeg_pos r.1 ℤ)
      · exact ⟨q, Finset.mem_univ _, by omega⟩
    rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, Fintype.card_eq_nat_card,
      Nat.card_coe_set_eq, hcard] at hlt
    exact lt_irrefl _ hlt
  have hWmem : W.asIdeal ∈ P.primesOver (𝓞 E) := ⟨W.isPrime, ⟨rfl⟩⟩
  have hw := hone ⟨W.asIdeal, hWmem⟩
  have he : W.asIdeal.ramificationIdx ℤ = 1 := Nat.eq_one_of_mul_eq_one_right hw
  have hf : W.asIdeal.inertiaDeg ℤ = 1 := Nat.eq_one_of_mul_eq_one_left hw

  set n : ℕ := (Submodule.IsPrincipal.generator P).natAbs with hn
  have hspan : Ideal.span {((n : ℕ) : ℤ)} = P := by
    rw [hn, Int.span_natAbs, Ideal.span_singleton_generator]
  have hn0 : ((n : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply hP0
    rw [← hspan, h0, Ideal.span_singleton_eq_bot]
  have hnprime : n.Prime := by
    rw [Nat.prime_iff_prime_int, ← Ideal.span_singleton_prime hn0, hspan]
    exact hPprime
  haveI : W.asIdeal.LiesOver (Ideal.span {((n : ℕ) : ℤ)}) := ⟨by rw [hspan]⟩
  refine ⟨n, hnprime, ?_, ?_⟩
  ·
    rw [← Ideal.pow_inertiaDeg n W.asIdeal, hf, pow_one]
  ·
    intro hmem
    have hmap0 : P.map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP0
    have hle : P.map (algebraMap ℤ (𝓞 E)) ≤ W.asIdeal ^ 2 := by
      rw [← hspan, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      simpa using hmem
    have hdvd : W.asIdeal ^ 2 ∣ P.map (algebraMap ℤ (𝓞 E)) := Ideal.dvd_iff_le.mpr hle
    have hfin : FiniteMultiplicity W.asIdeal (P.map (algebraMap ℤ (𝓞 E))) :=
      FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact W.isPrime.ne_top) hmap0
    have h2 := hfin.le_multiplicity_of_pow_dvd hdvd
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity P W.asIdeal hmap0, he] at h2
    omega

end GlobalTheory.SplitFullyNorm
end

section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors Matrix TensorProduct

namespace GlobalTheory.AdaptedPlaneIdeal

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_hasSig {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (φ : E →+* ℂ)
    (h : HasSig (J.map φ) r s) : J.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  intro h0
  have hM : (J.map φ).det = 0 := by
    have := RingHom.map_det φ J
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hM
  have hD : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]; simp [Matrix.det_neg]
  have h1 := Matrix.rank_of_isUnit _ hD
  rw [← hA] at h1
  have h2 : (Aᵀ * J.map φ * A.map star).rank ≤ (J.map φ).rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have h3 := LinearMap.finrank_range_add_finrank_ker (J.map φ).mulVecLin
  have h4 : 0 < Module.finrank ℂ (LinearMap.ker (J.map φ).mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun e => hv0 (congrArg Subtype.val e)⟩
  rw [Module.finrank_fin_fun] at h3
  have h5 : (J.map φ).rank = Module.finrank ℂ (LinearMap.range (J.map φ).mulVecLin) :=
    (Matrix.finrank_range_mulVecLin (J.map φ)).symm
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
  omega

section Split

variable {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}

end Split

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Split

variable {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}

end Split

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

end GlobalTheory.AdaptedPlaneIdeal
end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem exists_orthCompl_hypPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
    n = n₁ + 2 → (∀ i j, σ (J j i) = J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    ∃ (ι : Matrix (Fin n) (Fin n₁) E) (P : Matrix (Fin n₁) (Fin n) E), P * ι = 1 ∧
      (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) ∧
      ∀ z, form σ J z x = 0 → form σ J z y = 0 → ∃ u, z = ι *ᵥ u := by
  intro F E _ _ _ _ _ σ n n₁ J x y hn hJ hxx hyy hxy
  classical
  set a : Fin n → E := J *ᵥ fun i => σ (x i) with ha_def
  set b : Fin n → E := J *ᵥ fun i => σ (y i) with hb_def
  have hfa : ∀ z, form σ J z x = z ⬝ᵥ a := fun z => rfl
  have hfb : ∀ z, form σ J z y = z ⬝ᵥ b := fun z => rfl
  have hxa : x ⬝ᵥ a = 0 := hxx
  have hxb : x ⬝ᵥ b = 1 := hxy
  have ha : a ≠ 0 := by
    intro h0
    have hv : x ᵥ* J = 0 := by
      funext j
      apply σ.toRingHom.injective
      have h1 := congrFun h0 j
      simp only [ha_def, Matrix.mulVec, dotProduct, Pi.zero_apply] at h1

      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, map_zero, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hJ j i, mul_comm]
    apply one_ne_zero (α := E)
    rw [← hxb, hb_def, Matrix.dotProduct_mulVec, hv, zero_dotProduct]
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (funext h)
  set w : Fin n → E := (a i)⁻¹ • (Pi.single i 1 - (b i) • x) with hw
  have hwa : w ⬝ᵥ a = 1 := by
    rw [hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxa, single_dotProduct]
    simp [hi]
  have hwb : w ⬝ᵥ b = 0 := by
    rw [hw, smul_dotProduct, sub_dotProduct, smul_dotProduct, hxb, single_dotProduct]
    simp
  let M : Matrix (Fin 2) (Fin n) E := Matrix.of ![a, b]
  have hM : ∀ z, M *ᵥ z = ![z ⬝ᵥ a, z ⬝ᵥ b] := by
    intro z; funext k; fin_cases k <;> simp [M, Matrix.mulVec, dotProduct_comm]
  have hsurj : LinearMap.range (Matrix.mulVecLin M) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨v 0 • w + v 1 • x, ?_⟩
    rw [Matrix.mulVecLin_apply, hM]
    funext k; fin_cases k <;> simp [add_dotProduct, smul_dotProduct, hwa, hwb, hxa, hxb]
  have hrank : Module.finrank E (LinearMap.ker (Matrix.mulVecLin M)) = n₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin M)
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h
    omega
  set K := LinearMap.ker (Matrix.mulVecLin M) with hK
  have hmemK : ∀ z, z ∈ K ↔ z ⬝ᵥ a = 0 ∧ z ⬝ᵥ b = 0 := by
    intro z
    rw [hK, LinearMap.mem_ker, Matrix.mulVecLin_apply, hM]
    constructor
    · intro h; exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
    · rintro ⟨h1, h2⟩; funext k; fin_cases k <;> simp [h1, h2]
  let bK : Module.Basis (Fin n₁) E K := Module.finBasisOfFinrankEq E K hrank
  let f : (Fin n₁ → E) →ₗ[E] (Fin n → E) := K.subtype ∘ₗ bK.equivFun.symm.toLinearMap
  have hfinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp bK.equivFun.symm.injective
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hfinj
  refine ⟨LinearMap.toMatrix' f, LinearMap.toMatrix' g, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · intro u
    rw [LinearMap.toMatrix'_mulVec, hfa, hfb]
    exact (hmemK _).1 (bK.equivFun.symm u).2
  · intro z h1 h2
    have hz : z ∈ K := (hmemK z).2 ⟨h1, h2⟩
    refine ⟨bK.equivFun ⟨z, hz⟩, ?_⟩
    rw [LinearMap.toMatrix'_mulVec]
    simp [f]

end GlobalTheory
end

section

noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacLn

def trPair (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul])
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun c x y => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul])

theorem trPair_apply {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x y : κ → mixedEmbedding.mixedSpace F) :
    trPair F κ x y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i) := rfl

def coord {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} (d : Darboux B κ) (w : W) :
    (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) :=
  (fun i => evI F ((d.e w).1 i), fun i => evI F ((d.e w).2 i))

end GlobalTheory.VacLn
end
end

section

open scoped NNReal Pointwise
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.UnitaryVol

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_isCartan {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h1 := h.2.2 (star v) (by simpa using hv)
  rw [star_star, hMv, dotProduct_zero] at h1
  simp at h1

theorem isHermND_map {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ}
    (hσ : ∀ x, σ (σ x) = x) (h : X.IsHerm σ B r s) : IsHermND σ (X.J.map σ) := by
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.map_apply, hσ]
    exact (h.herm j i).symm
  · have hJ : X.J.det ≠ 0 := by
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
      intro hz
      apply det_ne_zero_of_isCartan (h.cartan w)
      rw [show X.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix X.J from rfl, ← RingHom.map_det, hz, map_zero]
    rw [show X.J.map σ = (σ : E →+* E).mapMatrix X.J from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 hJ

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  haveI : Countable E := Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (GL (Fin n) E) :=
    Function.Injective.countable (f := fun (g : GL (Fin n) E) (i j : Fin n) => (g : Matrix (Fin n) (Fin n) E) i j)
      fun _ _ h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  haveI := (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).to_subtype
  exact Function.Injective.countable
    (f := fun γ : ratU σ J => (⟨γ.1.1, Subgroup.mem_subgroupOf.1 γ.2⟩ :
      Set.range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))))
    fun γ γ' h => Subtype.val_injective (Subtype.val_injective (congrArg Subtype.val h :))

end GlobalTheory.UnitaryVol
end
end
