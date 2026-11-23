module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension

@[expose] public section

section

open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory

theorem selfDual_inv_gram_integral (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
    (w : HeightOneSpectrum (𝓞 E))
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ L, ∀ o : 𝓞 E,
      IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J y x)))
    (X : Matrix (Fin n) (Fin n) E) (hX : IsUnit X.det) (hG : IsUnit (Xᵀ * J * X.map σ).det)
    (hval : ∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) (s : 𝓞 E) (hs : s ∉ w.asIdeal)
    (hsr : ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r)
    (e : E) (he : ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) (i k : Fin n) :
    w.valuation E (e * (Xᵀ * J * X.map σ)⁻¹ i k) ≤ 1 := by
  set G := Xᵀ * J * X.map σ with hGdef
  set a : Fin n → E := fun j => e * G⁻¹ i j with ha
  have haG : a ᵥ* G = fun j => if j = i then e else 0 := by
    have h1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hG
    funext j
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.mul_apply, Matrix.one_apply] at h2
    simp only [Matrix.vecMul, dotProduct, ha, mul_assoc, ← Finset.mul_sum, h2]
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h, Ne.symm h]
  have key : ∀ c : Fin n → E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (X *ᵥ a) (X *ᵥ c) = e * σ (c i) := by
    intro c
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form
    have h1 : (fun j => σ ((X *ᵥ c) j)) = X.map σ *ᵥ (fun j => σ (c j)) := by
      funext j

      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [h1, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.dotProduct_mulVec, haG]
    simp [dotProduct]
  have hXX : X⁻¹ * X = 1 := Matrix.nonsing_inv_mul X hX
  have hXX' : X * X⁻¹ = 1 := Matrix.mul_nonsing_inv X hX
  have hform_smul : ∀ (t : E) (u v : Fin n → E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (t • u) v = t * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J u v := by
    intro t u v
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form
    rw [smul_dotProduct, smul_eq_mul]
  set y : Fin n → E := (s : E) • (X *ᵥ a) with hy
  have hyL : y ∈ L := by
    refine (hL y).2 fun x hx o => ?_
    obtain ⟨r, hr⟩ := hsr x hx i
    have hx' : X *ᵥ (X⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hXX', Matrix.one_mulVec]
    have h3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J y x = e * (r : E) := by
      rw [hy, hform_smul, ← hx', key, ← hr]
      ring
    rw [h3]
    have h4 : (o : E) * (e * (r : E)) = ((o * r : 𝓞 E) : E) * e := by
      push_cast; ring
    rw [h4]
    exact he (o * r)
  have h5 := hval y hyL k
  have h6 : (X⁻¹ *ᵥ y) k = (s : E) * (e * G⁻¹ i k) := by
    rw [hy, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hXX, Matrix.one_mulVec]
    rfl
  rw [h6, map_mul] at h5
  have hsv : w.valuation E (s : E) = 1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hs
  rw [hsv, one_mul] at h5
  exact h5

end GlobalTheory
end

section

open NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LinBarAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def coAt (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
  -((1 : GL (Fin a') (Fv F v)).1ᵀ * G.V'.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ *
    (1 : GL (Fin (a + a')) (Fv F v)).1)

theorem coAt_eq_zero (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (h : u.map (piW (t.comp σ)) = 0) : coAt G t u = 0 := by
  unfold coAt; rw [h]; simp

end GlobalTheory.LinBarAt
end
end

section

open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.FourSumComposition

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_cA (σ : E →ₐ[F] E) {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    piW τ (cA σ z) = piW (τ.comp σ) z := by

  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [piW, cA, GlobalTheory.AdelicU.compFin, GlobalTheory.AdelicU.splitProj_tmul]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), hy, hz]

theorem piW_incM {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (i j : Fin m) :
    piW τ (incM F J i j) = τ (J i j) := by
  simp [incM, inclR, piW, GlobalTheory.AdelicU.compFin, GlobalTheory.AdelicU.splitProj_tmul]

theorem comp_comp {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) : (τ.comp σ).comp σ = τ := by
  ext x
  simp [GlobalTheory.AdelicU.cm_conj_conj h x]

theorem sum_four {R : Type} [CommRing R] {m n : ℕ} (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R)
    (X U : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, X i j * A k i * -B l j * U k l = ∑ k, ∑ l, (-(A * X * B.transpose)) k l * U k l := by

  have hR : ∀ k l, (-(A * X * B.transpose)) k l * U k l = ∑ j, ∑ i, X i j * A k i * -B l j * U k l := by
    intro k l
    simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, neg_mul,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  simp only [hR]
  calc ∑ i, ∑ j, ∑ k, ∑ l, X i j * A k i * -B l j * U k l
      = ∑ i, ∑ k, ∑ j, ∑ l, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ l, X i j * A k i * -B l j * U k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ j, ∑ i, X i j * A k i * -B l j * U k l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E), (∀ (i j : Fin m), (σ : E → E) (JA j i) = JA i j) → (∀ (i j : Fin n), (σ : E → E) (JB j i) = -JB i j) → ∀ (x u : Matrix (Fin m) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), Matrix.map x (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) = (0 : Matrix (Fin m) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) → Matrix.map u (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (AlgHom.comp τ σ)) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) = (0 : Matrix (Fin m) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) → (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) + (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (AlgHom.comp τ σ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) = ∑ k : Fin m, ∑ l : Fin n, (-(Matrix.map JA (⇑τ : E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) * Matrix.map x (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (AlgHom.comp τ σ)) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) * Matrix.transpose (Matrix.map JB (⇑τ : E → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)))) k l * Matrix.map u (⇑(GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) k l := by
  intro F E _ _ _ _ _ σ hσ v τ m n JA JB hA hB x u hx hu
  have hx' : ∀ i j, piW τ (x i j) = 0 := fun i j => by simpa using congrFun (congrFun hx i) j
  have hu' : ∀ k l, piW (τ.comp σ) (u k l) = 0 := fun k l => by simpa using congrFun (congrFun hu k) l

  have h1 : piW τ (GlobalTheory.WeilM.hTens (cA σ) (incM F JA) (incM F JB) x u) = 0 := by
    simp [GlobalTheory.WeilM.hTens, piW_cA, hu']

  have h2 : piW (τ.comp σ) (GlobalTheory.WeilM.hTens (cA σ) (incM F JA) (incM F JB) x u) =
      ∑ i, ∑ j, ∑ k, ∑ l, (x.map (piW (τ.comp σ))) i j * (JA.map τ) k i * -(JB.map τ) l j *
        (u.map (piW τ)) k l := by

    simp only [GlobalTheory.WeilM.hTens, map_sum, map_mul, piW_cA, comp_comp hσ, piW_incM, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hA k i, hB l j, map_neg]
  rw [h1, zero_add, h2]
  exact sum_four _ _ _ _

end GlobalTheory.FourSumComposition
end

section

noncomputable section

namespace GlobalTheory.ThK.DescB

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


variable (σ) in
def finK {n : ℕ} (W : Spc F E n) (τ : ∀ w : InfinitePlace F, EmbOver E w) : Set (UA σ W.J) :=
  {x | ∃ k ∈ KInf σ W τ, ∃ g ∈ UAt σ W (fun u : AF F => u.2), x = k * g}

variable {a a' : ℕ}

structure InducedMaj (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) : Prop where
  cartan : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w)
  tie : ∀ w, ∃ a : Fin n₁ → ℂ, Y.θ w * (H.ι.map (B.emb w).1 + Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) a) =
    (H.ι.map (B.emb w).1 + Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) a) * Y₁.θ w

theorem InducedMaj.of_comm {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (h₁ : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w))
    (h₂ : ∀ w, Y.θ w * H.ι.map (B.emb w).1 = H.ι.map (B.emb w).1 * Y₁.θ w) : InducedMaj B H Y Y₁ :=
  ⟨h₁, fun w => ⟨0, by
    have e : Matrix.vecMulVec (fun i => (B.emb w).1 (H.x i)) (0 : Fin n₁ → ℂ) = 0 := by ext; simp [Matrix.vecMulVec_apply]
    rw [e, add_zero]; exact h₂ w⟩⟩


variable (σ) in
def IsIsoPlane (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) : Prop :=
  n = n₁ + 2 ∧ form σ Y.J H.x H.x = 0 ∧ form σ Y.J H.y H.y = 0 ∧ form σ Y.J H.x H.y = 1 ∧
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) ∧ H.ιᵀ * Y.J * H.ι.map σ = Y₁.J ∧
    (∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w)) ∧ InducedMaj B H Y Y₁

theorem IsIsoPlane.of_adapted {B : Base F E} {n n₁ i₀ i₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (h : ∀ w, IsCartan (Complex.I • Y.J.map (B.emb w).1) (Y.θ w))
    (h₁ : ∀ w, IsCartan (Complex.I • Y₁.J.map (B.emb w).1) (Y₁.θ w)) : IsIsoPlane σ B H Y Y₁ :=
  ⟨hH.rank, hH.xx, hH.yy, hH.xy, hH.orth, hH.gram, h, .of_comm h₁ fun w => (hH.cartan w).1⟩

end GlobalTheory.ThK.DescB

end
end

section

open NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LinWAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def coW (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Matrix (Fin a) (Fin (a + a')) (Fv F v) :=
  -(G.V.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ)

theorem coW_eq_zero (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v)
    (u : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (h : u.map (piW (t.comp σ)) = 0) : coW G t u = 0 := by
  unfold coW; rw [h]; simp

end GlobalTheory.LinWAt
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.SkewDet

theorem det_ne_zero_of_isSkew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (W : Spc F E n), W.IsSkew σ B r s → W.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B n r s W hW
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hA⟩ := hW.sig w
  subst hrs
  intro hdet
  set φ : E →+* ℂ := (B.emb w).1
  set M : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := Complex.I • W.J.map φ with hM
  have hMdet : M.det = 0 := by
    rw [hM, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_zero, mul_zero]
  set P : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have hP : Pᵀ * M * P.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]
    ext i j
    simp [P, Matrix.mul_apply]
  have h2 := congrArg Matrix.det hP
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, hMdet, mul_zero, zero_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg] at h2
  rw [Matrix.det_one, mul_one] at h2
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) h2.symm

end GlobalTheory.SkewDet
end

section

noncomputable section

namespace GlobalTheory.XTermMaj

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def crd (x : AE F E) : Fin (Module.finrank F E) → AF F :=
  (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun x

def maj (N : ℕ) (U : Set (Fin (Module.finrank F E) → Af F)) (x : AE F E) : ENNReal :=
  U.indicator (fun _ => ENNReal.ofReal ((1 + ∑ i, ∑ v : InfinitePlace F, ‖(crd F E x i).1 v‖) ^ (-(N : ℝ))))
    (fun i => (crd F E x i).2)

end GlobalTheory.XTermMaj

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.TraceCorrection

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem form_add_left (x x' y : Fin n → E) : form σ J (x + x') y = form σ J x y + form σ J x' y := by
  simp [form, add_dotProduct]

theorem form_add_right (x y y' : Fin n → E) : form σ J x (y + y') = form σ J x y + form σ J x y' := by
  have h : (fun i => σ ((y + y') i)) = (fun i => σ (y i)) + fun i => σ (y' i) := by
    ext i; simp
  simp only [form, h, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_left (c : E) (x y : Fin n → E) : form σ J (c • x) y = c * form σ J x y := by
  simp [form, smul_dotProduct]

theorem form_smul_right (c : E) (x y : Fin n → E) : form σ J x (c • y) = σ c * form σ J x y := by
  have h : (fun i => σ ((c • y) i)) = σ c • fun i => σ (y i) := by
    ext i; simp
  simp only [form, h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_symm (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (form σ J x y) = form σ J y x := by

  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem exists_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ x y₀ : Fin n → E, form σ J x x = 0 → form σ J y₀ x = 1 →
    (∀ z ∈ L, form σ J z x • y₀ ∈ L) →
    ∃ y : Fin n → E, form σ J y y = 0 ∧ form σ J x y = 1 ∧ ∀ z ∈ L, form σ J z y • x ∈ L ∧ form σ J z x • y ∈ L := by
  intro F E _ _ _ _ _ σ hσ n J L hJ hL θ hθ x y₀ hxx hy₀x hL0
  have hsa : σ (form σ J y₀ y₀) = form σ J y₀ y₀ := form_symm σ J hσ hJ y₀ y₀
  have hxw : ∀ w, form σ J x w = σ (form σ J w x) := fun w => (form_symm σ J hσ hJ w x).symm
  have hxy₀ : form σ J x y₀ = 1 := by rw [hxw, hy₀x, map_one]
  have hsθ : σ (θ : E) = 1 - θ := by linear_combination hθ
  have hθi : IsIntegral ℤ (θ : E) := θ.isIntegral_coe
  have hA : ∀ z ∈ L, ∀ w ∈ L,
      IsIntegral ℤ (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) := by
    intro z hz w hw
    have h := (hL _).1 (hL0 z hz) _ (hL0 w hw)
    rw [form_smul_left, form_smul_right] at h
    have k : form σ J z x * (σ (form σ J w x) * form σ J y₀ y₀) =
        form σ J y₀ y₀ * form σ J z x * σ (form σ J w x) := by ring
    rw [← k]; exact h
  refine ⟨y₀ + (-((θ : E) * form σ J y₀ y₀)) • x, ?_, ?_, ?_⟩
  · simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, hxx, hxy₀, hy₀x,
      map_neg, map_mul, hsθ, hsa]
    ring
  · simp only [form_add_right, form_smul_right, hxx, hxy₀]
    ring
  intro z hz
  constructor
  · have e : form σ J z (y₀ + (-((θ : E) * form σ J y₀ y₀)) • x) • x =
        form σ J z y₀ • x + (σ (-((θ : E) * form σ J y₀ y₀)) * form σ J z x) • x := by
      rw [form_add_right, form_smul_right, add_smul]
    rw [e]
    refine L.add_mem ((hL _).2 fun w hw => ?_) ((hL _).2 fun w hw => ?_)
    · have h := (hL z).1 hz _ (hL0 w hw)
      rw [form_smul_right] at h
      rw [form_smul_left, hxw, mul_comm]
      exact h
    · rw [form_smul_left, hxw]
      have h := (hA z hz w hw).neg.add (hθi.mul (hA z hz w hw))
      have k : σ (-((θ : E) * form σ J y₀ y₀)) * form σ J z x * σ (form σ J w x) =
          -(form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) +
            (θ : E) * (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) := by
        rw [map_neg, map_mul, hsθ, hsa]; ring
      rw [k]; exact h
  · have e : form σ J z x • (y₀ + (-((θ : E) * form σ J y₀ y₀)) • x) =
        form σ J z x • y₀ + (form σ J z x * (-((θ : E) * form σ J y₀ y₀))) • x := by
      rw [smul_add, mul_smul]
    rw [e]
    refine L.add_mem (hL0 z hz) ((hL _).2 fun w hw => ?_)
    rw [form_smul_left, hxw]
    have h := (hθi.mul (hA z hz w hw)).neg
    have k : form σ J z x * (-((θ : E) * form σ J y₀ y₀)) * σ (form σ J w x) =
        -((θ : E) * (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x))) := by ring
    rw [k]; exact h

end GlobalTheory.TraceCorrection
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CMTraceZero

theorem exists_ne_zero_conj_neg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨_, hc, _, hτ⟩ := hB.cm
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hw := hc.isComplex w
    rw [InfinitePlace.isComplex_iff] at hw
    apply hw
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hτ w.embedding x
    rw [hall x] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv, neg_sub]

end GlobalTheory.CMTraceZero
end

section

namespace GlobalTheory.ClosingLemmaThird

theorem main : (let d1 : {F : Type} → [inst : Field F] → [inst_1 : NumberField F] → {κ : Type} → [Fintype κ] → ((v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) → (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) → Prop := @(fun {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (φ₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ) (Φ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) ↦ ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : Fin m → (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), Φ = ∑ k : Fin m, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ (k : Fin m) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), φ k v ∈ GlobalTheory.WeilM.SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (∀ (k : Fin m), ∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) in Filter.cofinite, φ k v = vac v) ∧ ∀ (k : Fin m), φ k v₁ = φ₀); ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {κ : Type} [inst_2 : Fintype κ] {vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ} {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ} {Φ Ψ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ}, d1 vac v₁ φ₀ Φ → d1 vac v₁ φ₀ Ψ → d1 vac v₁ φ₀ (Φ + Ψ)) := by
  intro d1 F _ _ κ _ vac v₁ φ₀ Φ Ψ hΦ hΨ
  obtain ⟨m, f, φ, hΦe, h1, h2, h3⟩ := hΦ
  obtain ⟨m', g, ψ, hΨe, g1, g2, g3⟩ := hΨ
  refine ⟨m + m', Fin.append f g, Fin.append φ ψ, ?_, ?_, ?_, ?_⟩
  · rw [hΦe, hΨe, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · intro k v
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h1 i v
    · simpa only [Fin.append_right] using g1 i v
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h2 i
    · simpa only [Fin.append_right] using g2 i
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h3 i
    · simpa only [Fin.append_right] using g3 i

end GlobalTheory.ClosingLemmaThird
end
