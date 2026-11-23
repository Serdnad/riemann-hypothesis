module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.LeviPlane

variable {R : Type} [CommRing R] (c : R →+* R) {n : ℕ}

def fm (J : Matrix (Fin n) (Fin n) R) (u v : Fin n → R) : R := u ⬝ᵥ J *ᵥ (fun i => c (v i))

def lev (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) : Matrix (Fin n) (Fin n) R :=
  1 + (s - 1) • Matrix.vecMulVec X (J *ᵥ fun i => c (Y i)) - (r - 1) • Matrix.vecMulVec Y (J *ᵥ fun i => c (X i))

theorem lev_mulVec (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R) (s r : R) (w : Fin n → R) :
    lev c J X Y s r *ᵥ w = w + ((s - 1) * fm c J w Y) • X - ((r - 1) * fm c J w X) • Y := by
  ext i
  simp only [lev, fm, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, dotProduct_comm w]
  ring

theorem fm_skew (hc : ∀ x, c (c x) = x) (J : Matrix (Fin n) (Fin n) R) (hJ : ∀ i j, c (J j i) = -J i j)
    (p q : Fin n → R) : fm c J p q = -c (fm c J q p) := by

  simp only [fm, dotProduct, Matrix.mulVec, map_sum, map_mul, hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

variable {c}

theorem fm_add_left (J : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) : fm c J (u + u') v = fm c J u v + fm c J u' v := by
  simp [fm, add_dotProduct]

theorem fm_sub_left (J : Matrix (Fin n) (Fin n) R) (u u' v : Fin n → R) : fm c J (u - u') v = fm c J u v - fm c J u' v := by
  simp [fm, sub_dotProduct]

theorem fm_smul_left (J : Matrix (Fin n) (Fin n) R) (a : R) (u v : Fin n → R) : fm c J (a • u) v = a * fm c J u v := by
  simp [fm, smul_dotProduct]

theorem fm_add_right (J : Matrix (Fin n) (Fin n) R) (u v v' : Fin n → R) : fm c J u (v + v') = fm c J u v + fm c J u v' := by
  have : (fun i => c ((v + v') i)) = (fun i => c (v i)) + fun i => c (v' i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_add, dotProduct_add]

theorem fm_sub_right (J : Matrix (Fin n) (Fin n) R) (u v v' : Fin n → R) : fm c J u (v - v') = fm c J u v - fm c J u v' := by
  have : (fun i => c ((v - v') i)) = (fun i => c (v i)) - fun i => c (v' i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_sub, dotProduct_sub]

theorem fm_smul_right (J : Matrix (Fin n) (Fin n) R) (a : R) (u v : Fin n → R) : fm c J u (a • v) = c a * fm c J u v := by
  have : (fun i => c ((a • v) i)) = c a • fun i => c (v i) := by ext i; simp
  simp only [fm, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem entry (J M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Mᵀ * J * M.map c) i j = fm c J (M *ᵥ Pi.single i 1) (M *ᵥ Pi.single j 1) := by
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one]
  simp only [fm, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, Matrix.col_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.LeviPlane

namespace GlobalTheory.LeviPlane
variable {R : Type} [CommRing R] {c : R →+* R} {n : ℕ}

section Plane
variable (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) R} (hJ : ∀ i j, c (J j i) = -J i j) {X Y : Fin n → R}
  (hxx : fm c J X X = 0) (hyy : fm c J Y Y = 0) (hxy : fm c J X Y = 1)
include hc hJ hxx hyy hxy

theorem fm_yx : fm c J Y X = -1 := by rw [fm_skew c hc J hJ, hxy, map_one]

theorem lev_mul (s r s' r' : R) : lev c J X Y s r * lev c J X Y s' r' = lev c J X Y (s * s') (r * r') := by
  have hyx := fm_yx hc hJ hxx hyy hxy
  have key : ∀ w, (lev c J X Y s r * lev c J X Y s' r') *ᵥ w = lev c J X Y (s * s') (r * r') *ᵥ w := by
    intro w
    rw [← Matrix.mulVec_mulVec, lev_mulVec, lev_mulVec, lev_mulVec]
    simp only [fm_add_left, fm_sub_left, fm_smul_left, hxx, hyy, hxy, hyx]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem lev_one : lev c J X Y 1 1 = 1 := by simp [lev]

theorem lev_unitary (s r : R) (hsr : s * c r = 1) :
    (lev c J X Y s r)ᵀ * J * (lev c J X Y s r).map c = J := by
  have hyx := fm_yx hc hJ hxx hyy hxy
  have hrs : r * c s = 1 := by
    have := congrArg c hsr; rw [map_mul, hc, map_one] at this; rw [mul_comm]; exact this
  have key : ∀ u v, fm c J (lev c J X Y s r *ᵥ u) (lev c J X Y s r *ᵥ v) = fm c J u v := by
    intro u v
    rw [lev_mulVec, lev_mulVec]
    simp only [fm_add_left, fm_sub_left, fm_smul_left, fm_add_right, fm_sub_right, fm_smul_right, hxx, hyy, hxy, hyx]
    rw [fm_skew c hc J hJ X v, fm_skew c hc J hJ Y v]
    simp only [map_mul, map_sub, map_one, map_neg]
    linear_combination (-(fm c J u Y * c (fm c J v X))) * hsr + (fm c J u X * c (fm c J v Y)) * hrs
  ext i j
  rw [entry, key]
  have h1 := entry (c := c) J 1 i j
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero c) (map_one c), Matrix.mul_one,
    Matrix.one_mulVec] at h1
  exact h1.symm

end Plane

theorem lev_X {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R} (hxx : fm c J X X = 0) (hxy : fm c J X Y = 1) (s r : R) :
    lev c J X Y s r *ᵥ X = s • X := by
  rw [lev_mulVec, hxx, hxy]; ext i; simp; ring

theorem lev_Y (hc : ∀ x, c (c x) = x) {J : Matrix (Fin n) (Fin n) R} (hJ : ∀ i j, c (J j i) = -J i j) {X Y : Fin n → R}
    (hxx : fm c J X X = 0) (hyy : fm c J Y Y = 0) (hxy : fm c J X Y = 1) (s r : R) :
    lev c J X Y s r *ᵥ Y = r • Y := by
  rw [lev_mulVec, hyy, fm_yx hc hJ hxx hyy hxy]; ext i; simp; ring

theorem lev_mul_ι {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R} {k : ℕ} (ι : Matrix (Fin n) (Fin k) R)
    (hι : ∀ j, fm c J (fun i => ι i j) X = 0 ∧ fm c J (fun i => ι i j) Y = 0) (s r : R) :
    lev c J X Y s r * ι = ι := by
  ext i j
  have h := congrFun (lev_mulVec c J X Y s r (fun i => ι i j)) i
  rw [(hι j).1, (hι j).2] at h
  simp only [mul_zero, zero_smul, add_zero, sub_zero] at h
  rw [Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct] using h

end GlobalTheory.LeviPlane

namespace GlobalTheory.LeviPlane
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, Algebra.TensorProduct.map_tmul, h]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem cAr_inclR (σ : E →ₐ[F] E) (e : E) :
    (cA σ).toRingHom (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := cA_inclR σ e

theorem fm_inc (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    fm (cA σ).toRingHom (incM F J) (incV F x) (incV F y) = inclR (F := F) (AF F) (form σ J x y) := by

  simp only [fm, form, incV, incM, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul,
  AlgHom.coe_toRingHom, cAr_inclR, cA_inclR]

end GlobalTheory.LeviPlane

end
end

section

noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Fin

variable {n d n₁ d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} {Y₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure IsIndMap (v : Pl F) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁) {P P₁ : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P)
    (p₁ : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (A : P →ₗ[ℂ] (UA σ W.J → P₁)) : Prop where
  right : ∀ g ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
    Acts (evFin F v) (om (1, g)) φ φ₁ → ∀ h ∈ UAt σ W (evFin F v), A (p φ₁) h = A (p φ) (h * g)
  unip : ∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) → ∀ x, ∀ h ∈ UAt σ W (evFin F v), A x (u * h) = A x h
  levi : ∀ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (m : UA σ W.J), IsLevi H' t h₁ m → m ∈ UAt σ W (evFin F v) →
    h₁ ∈ UAt σ W₁ (evFin F v) → ∀ φ ∈ SB (Fin n₁ × Fin d₁ → Fv F v), ∀ φ₁ ∈ SB (Fin n₁ × Fin d₁ → Fv F v),
    Acts (evFin F v) (om₁ (1, h₁)) φ φ₁ → ∀ x, ∀ h ∈ UAt σ W (evFin F v), A x h = p₁ φ →
      A x (m * h) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • p₁ φ₁

def IndLineFin (v : Pl F) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁) {P P₁ : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] (p : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] P)
    (p₁ : ((Fin n₁ × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) : Prop :=
  ∀ A A' : P →ₗ[ℂ] (UA σ W.J → P₁), IsIndMap v om om₁ p p₁ H' χ z A → IsIndMap v om om₁ p p₁ H' χ z A' →
    (∀ x, ∀ h ∈ UAt σ W (evFin F v), A x h = 0) ∨ ∃ c : ℂ, ∀ x, ∀ h ∈ UAt σ W (evFin F v), A' x h = c • A x h

end Fin

section Inf

variable {n d n₁ d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d} {Y₁ : Spc F E n₁} {W₁ : Spc F E d₁}

structure IsFrobInf (B : Base F E) (M : Model σ Y W) (M₁ : Model σ Y₁ W₁) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁)
    {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E)
    (z : ℝ) (φ : P →ₗ[ℂ] P₁) : Prop where
  unip : ∀ γ ∈ Lines σ W, (∀ s, γ s ∈ unip σ W H') → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
    ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → φ (p f₁) = 0
  lie : ∀ γ ∈ Lines σ W, ∀ γ₁ ∈ Lines σ W₁, ∀ t : Multiplicative ℝ →* (AE F E)ˣ, (∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ →
    ∀ g ∈ M₁.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n₁ × Fin d₁),
    ActsD (evI F) (fun s => om₁ (1, γ₁ (Multiplicative.ofAdd s))) g g₁ → φ (p f) = p₁ g → ∀ c : ℂ,
    HasDerivAt (fun s : ℝ => (χ (t (Multiplicative.ofAdd s)) : ℂ) *
      (((absE F E (t (Multiplicative.ofAdd s)) : ℝ) ^ z : ℝ) : ℂ)) c 0 →
      φ (p f₁) = p₁ g₁ + c • φ (p f)
  cpt : ∀ k ∈ KInf σ W B.emb, ∀ (t : (AE F E)ˣ) (k₁ : UA σ W₁.J), IsLevi H' t k₁ k → k₁ ∈ KInf σ W₁ B.emb →
    ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ →
    ∀ g ∈ M₁.Pol B.ψ B.emb, ∀ g₁ : SInf F (Fin n₁ × Fin d₁), Acts (evI F) (om₁ (1, k₁)) g g₁ → φ (p f) = p₁ g →
      φ (p f₁) = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • p₁ g₁

def IndLineInf (B : Base F E) (M : Model σ Y W) (M₁ : Model σ Y₁ W₁) (om : Rep σ Y W) (om₁ : Rep σ Y₁ W₁)
    {P P₁ : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (p₁ : SInf F (Fin n₁ × Fin d₁) →ₗ[ℂ] P₁) (H' : Plane E d d₁) (χ : Chr F E)
    (z : ℝ) : Prop :=
  ∀ φ φ' : P →ₗ[ℂ] P₁, IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ → IsFrobInf B M M₁ om om₁ p p₁ H' χ z φ' →
    φ = 0 ∨ ∃ c : ℂ, φ' = c • φ

end Inf

end GlobalTheory.IndLine
end
end

section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKRealConj

theorem soLoc_reG' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (ψ : AddChar (AF F) ℂ) {v : Pl (F := F)}
    (t : E →ₐ[F] Fv F v) : (reG G V V' W).M'.SoLoc ψ t = G.M'.SoLoc ψ t := by
  ext φ
  simp only [Model.SoLoc, Model.IsLinBar, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, ι, ⟨a, b, c⟩, h2⟩; exact ⟨h1, ι, ⟨a, b, c⟩, h2⟩
  · rintro ⟨h1, ι, ⟨a, b, c⟩, h2⟩; exact ⟨h1, ι, ⟨a, b, c⟩, h2⟩

theorem so_reG' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (ψ : AddChar (AF F) ℂ) {v : Pl (F := F)}
    (t : E →ₐ[F] Fv F v) : (reG G V V' W).M'.So ψ t = G.M'.So ψ t := by
  unfold Model.So
  rw [soLoc_reG']
  rfl

end GlobalTheory.ThKRealConj
end

section

noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d}

def IsTwEig (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) (x : P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k → ∀ f ∈ M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f = x →
      p f₁ = ((χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)) • x

def IsOffEig (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ) (x : P) : Prop :=
  ∃ k ∈ KInf σ W B.emb, ∃ t : (AE F E)ˣ, IsLevi H' t (1 : UA σ W₁.J) k ∧ ∃ c : ℂ,
    c ≠ (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ) ∧ ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f = x → p f₁ = c • x

def twPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : Submodule ℂ P :=
  Submodule.span ℂ {x | x ∈ V ∧ IsTwEig B M om p W₁ H' χ z x}

def offPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : Submodule ℂ P :=
  Submodule.span ℂ {x | x ∈ V ∧ IsOffEig B M om p W₁ H' χ z x}

def KStabL (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (N : Submodule ℂ P) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ k₁ ∈ KInf σ W₁ B.emb, IsLevi H' 1 k₁ k → ∀ f ∈ M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → p f ∈ N → p f₁ ∈ N

theorem twPart_le (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (χ : Chr F E) (z : ℝ)
    (V : Submodule ℂ P) : twPart B M om p W₁ H' χ z V ≤ V :=
  Submodule.span_le.2 fun _ hx => hx.1

end GlobalTheory.IndLine
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviTorus

open Matrix

variable {R : Type} [CommRing R] {n m : ℕ}

section
variable (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R)

theorem conj_mulVec (hJ : ∀ i j, c (J j i) = -J i j) (V : Fin n → R) (hc : ∀ r, c (c r) = r) :
    (fun i => c ((J *ᵥ fun k => c (V k)) i)) = -(V ᵥ* J) := by
  funext i

  simp only [mulVec, vecMul, dotProduct, map_sum, map_mul, hc, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hJ k i]; ring

theorem conj_dot (a b : Fin n → R) : c (a ⬝ᵥ b) = (fun i => c (a i)) ⬝ᵥ (fun i => c (b i)) := by

  simp [dotProduct, map_sum, map_mul]

theorem vmv_mulVec (u v w : Fin n → R) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

end

section Props

variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R}
  (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j)
  (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0) (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0)
  (hXY : X ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 1)
include hc hJ hXY

theorem dot_yx : Y ⬝ᵥ J *ᵥ (fun i => c (X i)) = -1 := by
  rw [dotProduct_mulVec]
  have h := conj_mulVec c J hJ Y hc
  rw [show Y ᵥ* J = -(fun i => c ((J *ᵥ fun k => c (Y k)) i)) by rw [h, neg_neg]]
  rw [neg_dotProduct, ← conj_dot, dotProduct_comm (J *ᵥ _) X, hXY, map_one]


end Props

end GlobalTheory.LeviTorus

namespace GlobalTheory.LeviTorus

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, h]
  | add a b ha hb => simp [map_add (f := _), ha, hb]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem form_incl (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    incV F x ⬝ᵥ incM F J *ᵥ (fun i => cA σ (incV F y i)) = inclR (F := F) (AF F) (form σ J x y) := by

  simp [form, incV, incM, cA_incl, dotProduct, mulVec, map_sum, map_mul]

theorem vecMul_incM (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin k) E) (y : Fin n → E) :
    (incM F J *ᵥ fun i => cA σ (incV F y i)) ᵥ* incM F A =
      fun j => inclR (F := F) (AF F) (form σ J (A *ᵥ Pi.single j 1) y) := by
  funext j
  rw [← form_incl]
  simp only [vecMul, dotProduct, incV, incM, Matrix.map_apply, mulVec_single_one]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]; rfl

end GlobalTheory.LeviTorus
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

theorem glueMeas_eq_chartMeas_of_compat_on : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {ρ : κ → Y → ENNReal} (e' : OpenPartialHomeomorph Y (V n)) (ρ' : Y → ENNReal), S ⊆ e'.source → (∀ j, DifferentiableOn ℂ (e j ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' (e j).source)) → (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y) → (∀ j y, y ∈ S → y ∈ (e j).source → ρ' y = ENNReal.ofReal (‖transDet e' (e j) y‖ ^ 2) * ρ j y) → glueMeas e ρ S = chartMeas e' ρ' S := by
  intro n Y κ _ _ _ _ e hd hcov S hS ρ e' ρ' hSe hd' hρ hρ'
  have hm := GlobalTheory.ChernScale.glueMeas_restrict_eq e (ρ := ρ) (ρ' := fun i => S.indicator (ρ i)) (c := 1)
    ENNReal.one_ne_top hS (fun i y _ hy => by rw [one_mul, Set.indicator_of_mem hy])
  rw [one_smul] at hm
  have cσ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      S.indicator (ρ i) y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * S.indicator (ρ j) y := by
    intro i j y hi hj
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; exact hρ i j y hy hi hj
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  have key : (glueMeas e ρ).restrict S = (chartMeas e' ρ').restrict S := by
    rw [hm]
    refine ext_of_cover (fun i => (e i).source) (fun i => (e i).open_source) hcov fun i A hA hAi => ?_
    have hsub : A ∩ S ⊆ (e i).source := Set.inter_subset_left.trans hAi
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA,
      glueMeas_apply e (fun i => S.indicator (ρ i)) hd cσ i (hA.inter hS) hsub]
    refine (chartMeas_eq e' (e i) (hd' i) (hA.inter hS) (Set.inter_subset_right.trans hSe) hsub
      fun y hy => ?_).symm
    rw [Set.indicator_of_mem hy.2]
    exact hρ' i y hy.2 (hsub hy)
  have := congrArg (fun μ : Measure Y => μ S) key
  simpa only [Measure.restrict_apply_self] using this

end GlobalTheory.GoodTop
end
end
