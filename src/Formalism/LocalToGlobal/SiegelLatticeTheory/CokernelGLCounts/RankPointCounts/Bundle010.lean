module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle008
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle005
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle009
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

section

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Proj

variable {A : Type*} [CommRing A] {n : ℕ}

theorem entIn_transpose {J : AddSubgroup A} {X : Matrix (Fin n) (Fin n) A} (h : EntIn J X) : EntIn J X.transpose :=
  fun i j => h j i

theorem entIn_smul {J : AddSubgroup A} (e : A) (hJ : ∀ x ∈ J, e * x ∈ J) {X : Matrix (Fin n) (Fin n) A}
    (h : EntIn J X) : EntIn J (e • X) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact hJ _ (h i j)

theorem proj_inv (f : Fin n → ℕ) (hf : ∀ i, f i < n) {J : AddSubgroup A} (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J)
    (e : A) (he : e * e = e) (x : GL (Fin n) A)
    (hlow : ∀ i j, f i ≤ f j → ((x : Matrix (Fin n) (Fin n) A) - 1) i j = 0)
    (hx : EntIn J (e • ((x : Matrix (Fin n) (Fin n) A) - 1))) :
    EntIn J (e • (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1)) := by
  set X := (x : Matrix (Fin n) (Fin n) A) - 1 with hXd
  set Y := ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1 with hYd
  have hx1 : (x : Matrix (Fin n) (Fin n) A) = 1 + X := by rw [hXd]; abel
  have hy1 : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 + Y := by rw [hYd]; abel
  have hXY : X + Y + X * Y = 0 := by
    have h1 : (x : Matrix (Fin n) (Fin n) A) * ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hx1, hy1] at h1
    have h2 : (1 + X) * (1 + Y) = (1 : Matrix (Fin n) (Fin n) A) + (X + Y + X * Y) := by
      simp only [add_mul, mul_add, one_mul, mul_one]; abel
    rw [h2] at h1
    simpa using h1
  have hYX : Y + X + Y * X = 0 := by
    have h1 : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * (x : Matrix (Fin n) (Fin n) A) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hx1, hy1] at h1
    have h2 : (1 + Y) * (1 + X) = (1 : Matrix (Fin n) (Fin n) A) + (Y + X + Y * X) := by
      simp only [add_mul, mul_add, one_mul, mul_one]; abel
    rw [h2] at h1
    simpa using h1
  have hv : (1 + e • X) * (1 + e • Y) = 1 := by
    rw [add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]
    have : e • Y + (e • X + e • (X * Y)) = e • (X + Y + X * Y) := by rw [smul_add, smul_add]; abel
    rw [add_assoc, this, hXY, smul_zero, add_zero]
  have hv' : (1 + e • Y) * (1 + e • X) = 1 := by
    rw [add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]
    have : e • X + (e • Y + e • (Y * X)) = e • (Y + X + Y * X) := by rw [smul_add, smul_add]; abel
    rw [add_assoc, this, hYX, smul_zero, add_zero]
  let y : GL (Fin n) A := ⟨1 + e • X, 1 + e • Y, hv, hv'⟩
  have hyv : (y : Matrix (Fin n) (Fin n) A) - 1 = e • X := by simp [y]
  have hyi : ((y⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1 = e • Y := by
    show (1 + e • Y) - 1 = e • Y
    simp
  have key := inv_sub_one f hf hJ y (fun i j h => by
      rw [hyv, Matrix.smul_apply, hlow i j h, smul_zero]) (by rw [hyv]; exact hx)
  rw [hyi] at key
  exact key.1

end Proj

section Close

open Formalism.MainNotions.S.Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)} {L : LocAt F E sig p} {n : ℕ}

theorem latS_of_eq {c c' t : L.Fp} (h : c' = c * t) (ht : t ∈ 𝒪[L.Fp]) {x : L.Ep} (hx : x ∈ latS L c') :
    x ∈ latS L c := by
  rw [h] at hx; exact latS_mono ht hx

theorem entIn_latS_of_eq {c c' t : L.Fp} (h : c' = c * t) (ht : t ∈ 𝒪[L.Fp]) {X : Matrix (Fin n) (Fin n) L.Ep}
    (hX : EntIn (latS L c') X) : EntIn (latS L c) X := fun i j => latS_of_eq h ht (hX i j)

end Close

end Formalism.L2.SG.Pf.ProdEApprox
end
end

section

noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

def lawX {ι P : Type} (BX : P → (P → ℂ) → (P → ℂ) → ℂ) (γ x : ι → P → ℂ) : ι → P → ℂ :=
  fun v p => γ v p + x v p + BX p (γ v) (x v)

theorem pi_measure_eq_prod_absNorm_mul_sqrt_discr (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (P : Type) [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBm : ∀ p, Measurable (fun z : (P → ℂ) × (P → ℂ) => BX p z.1 z.2))
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (hB0 : ∀ p (x : P → ℂ), BX p x 0 = 0)
    (c : ℝ) (hc : 0 ≤ c) (I : P → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : P → AddSubgroup K)
    (hΛ : ∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : P → ℕ)
    (hk : ∀ p, (Λ p).relIndex
      (((I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k p)
    (hk0 : ∀ p, k p ≠ 0) (s : P → ℂ) (hs : ∀ p, s p ≠ 0)
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (hinv : ∀ γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) → ∃ γ' : ι → P → ℂ,
      (∀ p, (fun v => γ' v p) - τ p γ' ∈ (Λ p).map (embS φ (s p))) ∧
        ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x)
    (Kset : Set (ι → P → ℂ)) (hK : MeasurableSet Kset)
    (hKd : ∀ x, ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) ∧
      lawX BX γ x ∈ Kset) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : P => ENNReal.ofReal c • (volume : Measure ℂ)) Kset =
      ∏ p, ENNReal.ofReal (c ^ Fintype.card ι * k p *
        (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
        2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s p‖ ^ (2 * Fintype.card ι)) := by
  have hsf : SigmaFinite (ENNReal.ofReal c • (volume : Measure ℂ)) :=
    (inferInstance : SigmaFinite (c.toNNReal • (volume : Measure ℂ)))
  let sw : (ι → P → ℂ) → (P → ι → ℂ) := fun x p v => x v p
  let usw : (P → ι → ℂ) → (ι → P → ℂ) := fun y v p => y p v
  have h1 : ∀ x, usw (sw x) = x := fun x => rfl
  have h2 : ∀ y, sw (usw y) = y := fun y => rfl
  have hsw : MeasurePreserving sw _ _ := swap_mp (ι := ι) (P := P) (ENNReal.ofReal c • (volume : Measure ℂ))
  have husw : Measurable usw :=
    Measurable.of_eval fun v => Measurable.of_eval fun p =>
      (measurable_pi_apply v).comp (measurable_pi_apply p)
  let B : ∀ _ : P, (P → ι → ℂ) → (P → ι → ℂ) → (ι → ℂ) := fun p y y' v => BX p (fun q => y q v) (fun q => y' q v)
  let τT : ∀ _ : P, (P → ι → ℂ) → (ι → ℂ) := fun p y => τ p (usw y)
  have hlaw : ∀ γ x, mlaw B (sw γ) (sw x) = sw (lawX BX γ x) := fun γ x => rfl
  have hmemT : ∀ γ : ι → P → ℂ, (∀ p, sw γ p - τT p (sw γ) ∈ (Λ p).map (embS φ (s p))) ↔
      (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) := fun γ => Iff.rfl
  have hpre : Kset = sw ⁻¹' (usw ⁻¹' Kset) := by ext x; simp [h1]
  have hKT : MeasurableSet (usw ⁻¹' Kset) := husw hK
  rw [hpre, hsw.measure_preimage hKT.nullMeasurableSet]
  refine covol_oneT K ι φ σ hφ P h B ?_ ?_ ?_ c hc I Λ hΛ k hk hk0 s hs τT ?_ ?_ (usw ⁻¹' Kset) hKT ?_
  · intro p
    refine Measurable.of_eval fun v => ?_
    have hf : Measurable (fun z : (P → ι → ℂ) × (P → ι → ℂ) => ((fun q => z.1 q v), (fun q => z.2 q v))) :=
      (Measurable.of_eval fun q => (measurable_pi_apply v).comp ((measurable_pi_apply q).comp measurable_fst)).prodMk
        (Measurable.of_eval fun q => (measurable_pi_apply v).comp ((measurable_pi_apply q).comp measurable_snd))
    exact (hBm p).comp hf
  · intro p x x' y y' hxy
    funext v
    exact hBd p _ _ _ _ fun q hq => ⟨congrFun (hxy q hq).1 v, congrFun (hxy q hq).2 v⟩
  · intro p x
    funext v
    exact hB0 p _
  · intro p x x' hxx
    exact hτ p _ _ fun q hq v => congrFun (hxx q hq) v
  · intro γT hγT
    obtain ⟨γ', hγ', hinv'⟩ := hinv (usw γT) ((hmemT (usw γT)).1 (by rw [h2]; exact hγT))
    refine ⟨sw γ', (hmemT γ').2 hγ', fun g => ⟨?_, ?_⟩⟩
    · have := (hinv' (usw g)).1
      calc mlaw B (sw γ') (mlaw B γT g) = mlaw B (sw γ') (mlaw B (sw (usw γT)) (sw (usw g))) := by rw [h2, h2]
        _ = sw (lawX BX γ' (lawX BX (usw γT) (usw g))) := by rw [hlaw, hlaw]
        _ = g := by rw [this, h2]
    · have := (hinv' (usw g)).2
      calc mlaw B γT (mlaw B (sw γ') g) = mlaw B (sw (usw γT)) (mlaw B (sw γ') (sw (usw g))) := by rw [h2, h2]
        _ = sw (lawX BX (usw γT) (lawX BX γ' (usw g))) := by rw [hlaw, hlaw]
        _ = g := by rw [this, h2]
  · intro g
    obtain ⟨γ, ⟨hγΓ, hγK⟩, hγu⟩ := hKd (usw g)
    refine ⟨sw γ, ⟨(hmemT γ).2 hγΓ, ?_⟩, ?_⟩
    · show usw (mlaw B (sw γ) g) ∈ Kset
      rw [show g = sw (usw g) from (h2 g).symm, hlaw, h1]; exact hγK
    · rintro γT ⟨hΓT, hKT'⟩
      have e := hγu (usw γT) ⟨(hmemT (usw γT)).1 (by rw [h2]; exact hΓT), by
        have : usw (mlaw B γT g) ∈ Kset := hKT'
        rw [show γT = sw (usw γT) from (h2 γT).symm, show g = sw (usw g) from (h2 g).symm, hlaw, h1] at this
        exact this⟩
      rw [← e, h2]

theorem covol_one_eq_one (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (P : Type) [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBm : ∀ p, Measurable (fun z : (P → ℂ) × (P → ℂ) => BX p z.1 z.2))
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (hB0 : ∀ p (x : P → ℂ), BX p x 0 = 0)
    (c : ℝ) (hc : 0 ≤ c) (I : P → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : P → AddSubgroup K)
    (hΛ : ∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : P → ℕ)
    (hk : ∀ p, (Λ p).relIndex
      (((I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k p)
    (hk0 : ∀ p, k p ≠ 0) (s : P → ℂ) (hs : ∀ p, s p ≠ 0)
    (hconst : ∏ p, (c ^ Fintype.card ι * k p *
        (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
        2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s p‖ ^ (2 * Fintype.card ι)) = 1)
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (hinv : ∀ γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) → ∃ γ' : ι → P → ℂ,
      (∀ p, (fun v => γ' v p) - τ p γ' ∈ (Λ p).map (embS φ (s p))) ∧
        ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x)
    (Kset : Set (ι → P → ℂ)) (hK : MeasurableSet Kset)
    (hKd : ∀ x, ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) ∧
      lawX BX γ x ∈ Kset) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : P => ENNReal.ofReal c • (volume : Measure ℂ)) Kset = 1 := by
  rw [pi_measure_eq_prod_absNorm_mul_sqrt_discr K ι φ σ hφ P h BX hBm hBd hB0 c hc I Λ hΛ k hk hk0 s hs τ hτ hinv Kset hK hKd,
    ← ENNReal.ofReal_prod_of_nonneg, hconst, ENNReal.ofReal_one]
  intro p _
  have hN := FractionalIdeal.absNorm_nonneg (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  have hN' : (0 : ℝ) ≤ (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) := by
    exact_mod_cast hN
  positivity

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

section

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section T

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def ThCorr (M : Model F E) (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t₁ t₂ : Term V M r)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'),
    H.IsGeneric t₁ → H.IsGeneric t₂ → H.Respects t₁ t₂ φ φ' →
    ∀ (w₁ : V) (hw₁ : w₁ ∈ H.W0 t₁.f t₁.f') (w₂ : V) (hw₂ : w₂ ∈ H.W0 t₂.f t₂.f'),
      φ (H.mkW t₁.f ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp H hw₁⟩) = H.mkW t₂.f ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H hw₂⟩ →
      φ' (H.mkW t₁.f' ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp' H hw₁⟩) = H.mkW t₂.f' ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H hw₂⟩ →
      (w₁ ∈ t₁.abelian₂ ↔ w₂ ∈ t₂.abelian₂)

theorem mem_iff_of_image_eq {A B : Type} [AddCommGroup A] [Module E A] [AddCommGroup B] [Module E B]
    (φ : A ≃ₗ[E] B) {S : Set A} {T : Set B} (h : φ '' S = T) {a : A} {b : B} (hab : φ a = b) :
    a ∈ S ↔ b ∈ T := by
  subst hab
  subst h
  exact φ.injective.mem_set_image.symm

theorem thCorr_holds (M : Model F E) (r : ℕ) : ThCorr M r := by
  intro V _ _ H t₁ t₂ φ φ' hg₁ hg₂ hR w₁ hw₁ w₂ hw₂ he he'
  obtain ⟨hL, -, hL', -, hι⟩ := hR
  have e1 := mem_iff_of_image_eq φ hL he
  have e2 := mem_iff_of_image_eq φ' hL' he'
  cases hs : M.split with
  | none =>
    exact (lemma0L_holds M r hs V H t₁ hg₁ w₁ hw₁).trans
      ((and_congr e1 e2).trans (lemma0L_holds M r hs V H t₂ hg₂ w₂ hw₂).symm)
  | some g =>
    have hinj : Function.Injective (Prod.map φ' φ) := φ'.injective.prodMap φ.injective
    have e3 := hinj.mem_set_image (s := H.iotaGraph g t₁)
      (a := (H.mkW t₁.f' ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp' H hw₁⟩, H.mkW t₁.f ⟨w₁, mem_perp_isotropicSpan_of_mem_framePerp H hw₁⟩))
    rw [hι g hs, Prod.map_apply, he, he'] at e3
    exact (lemma0G_holds M r g hs V H t₁ hg₁ w₁ hw₁).trans
      ((and_congr e1 (and_congr e2 e3.symm)).trans (lemma0G_holds M r g hs V H t₂ hg₂ w₂ hw₂).symm)

end T

end Formalism.L2.SG.LsDatumA
end
end
