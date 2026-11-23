module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle057
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DblZMemHn
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle004

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem natCast_mul_X_mem_symO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} (c : Coeff l) {n : ℕ} (Λ : Lt E n) (N : ℕ)
    (hΛ : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ) (ℓ : LtN Dw n) :
    (N : MvPolynomial (LtN Dw n) c.F) * MvPolynomial.X ℓ ∈ Formalism.L2.Pj.symO c (⟨Λ⟩ : GenLat E n) := by
  obtain ⟨τ, i, j⟩ := ℓ
  refine Subring.subset_closure (Or.inr ⟨τ, i, Pi.single j (N : E), hΛ ?_, ?_⟩)
  · have h1 : (Pi.single j (1 : E) : Fin n → E) ∈ Formalism.L2.Pj.stdLat E n := by
      intro k _
      by_cases hk : k = j
      · subst hk
        rw [Pi.single_eq_same]
        exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · rw [Pi.single_eq_of_ne hk]
        exact Submodule.zero_mem _
    have h2 := Submodule.smul_mem_smul (Ideal.mem_span_singleton_self (N : 𝓞 E)) h1
    have h3 : (N : 𝓞 E) • (Pi.single j (1 : E) : Fin n → E) = Pi.single j (N : E) := by
      rw [Nat.cast_smul_eq_nsmul, ← Pi.single_nsmul]
      simp
    rwa [h3] at h2
  · unfold letB
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Pi.single_eq_of_ne hk]
    · simp

theorem exists_natCast_mul_mem_symO {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) {n : ℕ} (Λ : Lt E n) (N : ℕ) (hN : 0 < N)
    (hΛ : Ideal.span {(N : 𝓞 E)} • Formalism.L2.Pj.stdLat E n ≤ Λ) (P : MvPolynomial (LtN Dw n) c.F) :
    ∃ M : ℕ, 0 < M ∧ (M : MvPolynomial (LtN Dw n) c.F) * P ∈ Formalism.L2.Pj.symO c (⟨Λ⟩ : GenLat E n) := by
  haveI := c.fin
  induction P using MvPolynomial.induction_on with
  | C x =>
    obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := c.F) {x}
    have h1 := h x (Finset.mem_singleton_self x)
    have h2 : MvPolynomial.C (y • x) ∈ Formalism.L2.Pj.symO (Dw := Dw) c (⟨Λ⟩ : GenLat E n) :=
      Subring.subset_closure (Or.inl ⟨⟨y • x, h1⟩, rfl⟩)
    refine ⟨(y * y).natAbs, Int.natAbs_pos.2 (mul_ne_zero hy hy), ?_⟩
    have h3 : (((y * y).natAbs : ℕ) : MvPolynomial (LtN Dw n) c.F) = ((y * y : ℤ) : MvPolynomial (LtN Dw n) c.F) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg y)]
    have h4 := Subring.mul_mem _ (intCast_mem (Formalism.L2.Pj.symO (Dw := Dw) c (⟨Λ⟩ : GenLat E n)) y) h2
    rw [h3]
    convert h4 using 1
    rw [zsmul_eq_mul, map_mul, map_intCast]
    push_cast
    ring
  | add p q hp hq =>
    obtain ⟨M, hM, h⟩ := hp
    obtain ⟨M', hM', h'⟩ := hq
    refine ⟨M * M', Nat.mul_pos hM hM', ?_⟩
    have := Subring.add_mem _ (Subring.mul_mem _ (natCast_mem _ M') h) (Subring.mul_mem _ (natCast_mem _ M) h')
    convert this using 1
    push_cast
    ring
  | mul_X p ℓ hp =>
    obtain ⟨M, hM, h⟩ := hp
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have := Subring.mul_mem _ h (natCast_mul_X_mem_symO c Λ N hΛ ℓ)
    convert this using 1
    push_cast
    ring

theorem rowHighest_eq_sum_harmL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g q0 n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (Dc : Dic Dw c σ X g q0 n a) (Λ : Lt E n) (N : ℕ), 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ → ∀ Q ∈ Harm.rowHighest ℂ Dc.k Dc.k', ∃ (m : ℕ) (t : Fin m → ℂ) (P : Fin m → MvPolynomial (LtN Dw n) c.F), (∀ i, P i ∈ harmL c (⟨Λ⟩ : GenLat E n) a) ∧ Q = ∑ i, t i • MvPolynomial.rename Dc.eL (MvPolynomial.map σ (P i)) := by
  intro E _ _ _ H Dw l c σ r g q0 n X a Dc Λ N hN hΛ Q hQ
  obtain ⟨m, t, v, hv⟩ := Submodule.mem_span_set'.1 (Dc.span hQ)
  have hP : ∀ i, ∃ P : MvPolynomial (LtN Dw n) c.F,
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ∧
      MvPolynomial.rename Dc.eL (MvPolynomial.map σ P) = (v i).1 := fun i => (v i).2
  choose P hP hPv using hP
  choose M hM hMP using fun i => exists_natCast_mul_mem_symO c Λ N hN hΛ (P i)
  refine ⟨m, fun i => t i / (M i : ℂ), fun i => (M i : MvPolynomial (LtN Dw n) c.F) * P i,
    fun i => ⟨?_, hMP i⟩, ?_⟩
  · have e : (M i : MvPolynomial (LtN Dw n) c.F) * P i = (M i : c.F) • P i := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
    change (M i : MvPolynomial (LtN Dw n) c.F) * P i ∈ _
    rw [e]
    exact ⟨Submodule.smul_mem _ _ (hP i).1,
      fun s k k' h u => by rw [map_smul, (hP i).2.1 s k k' h u],
      fun mm hm => (hP i).2.2 mm (MvPolynomial.support_smul hm)⟩
  · rw [← hv]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 : (M i : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (hM i).ne'
    rw [map_mul, map_mul, map_natCast, map_natCast, hPv, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      div_mul_cancel₀ _ h0]

end GlobalTheory.Dict
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Extend

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [IsCMField E] in
theorem mapL_mul (a b : GL (Fin r) E) (L : Lt E r) : mapL (a * b) L = mapL a (mapL b L) := by
  unfold mapL
  rw [← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]
  rfl

omit [IsCMField E] in
theorem mapL_one (L : Lt E r) : mapL (1 : GL (Fin r) E) L = L := by
  unfold mapL
  rw [Units.val_one, Matrix.toLin'_one]
  exact Submodule.map_id L

omit [NumberField E] [IsCMField E] in
theorem lact_lact {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = (((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl

omit [NumberField E] [IsCMField E] in
theorem lact_rmul {Ψ : Finset (E →+* ℂ)} (a : GL (Fin r) E) (x b : Frame Ψ r) :
    lact a (rmul x b) = rmul (lact a x) b := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ) =
    (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ
  rw [Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem differentiable_lact {Ψ : Finset (E →+* ℂ)} (a : GL (Fin r) E) :
    Differentiable ℂ (lact (Ψ := Ψ) a) := by
  rw [differentiable_pi]; intro τ
  rw [differentiable_pi]; intro i
  rw [differentiable_pi]; intro j
  simp only [lact, Matrix.mul_apply, mat, Matrix.of_apply]
  fun_prop

variable {X : Data E r}

theorem gramE {a : GL (Fin r) E} (ha : IsUn X a) :
    (a : Matrix (Fin r) (Fin r) E).transpose * X.Gm * (a : Matrix (Fin r) (Fin r) E).map FD.cc = X.Gm := by
  ext i j
  have h := ha (Pi.single i 1) (Pi.single j 1)
  simp only [FD.herm, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, _root_.mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, ite_mul, zero_mul, _root_.one_mul] at h
  have hL : ((a : Matrix (Fin r) (Fin r) E).transpose * X.Gm * (a : Matrix (Fin r) (Fin r) E).map FD.cc) i j =
      ∑ c, ∑ d, (a : Matrix (Fin r) (Fin r) E) c i * X.Gm c d * FD.cc ((a : Matrix (Fin r) (Fin r) E) d j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hL, h]
  simp [apply_ite FD.cc]

omit [NumberField E] [IsCMField E] in
theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ G M = M.transpose * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [FD.gram, hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem dmin_lact {a : GL (Fin r) E} (ha : IsUn X a) (x : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm (lact a x) τ i = dmin X.Gm x τ i := by
  have hc : ((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
      ((a : Matrix (Fin r) (Fin r) E).map FD.cc).map τ.1 := by
    ext i j
    simp only [Matrix.map_apply]
    exact (IsCMField.complexEmbedding_complexConj E τ.1 _).symm
  have key : ((a : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
      ((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    rw [hc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, gramE ha]
  have e1 : mat (lact a x) τ = (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  unfold dmin
  congr 1
  rw [gram_eq, gram_eq, e1, Matrix.transpose_mul, Matrix.map_mul]
  calc (mat x τ).transpose * ((a : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
        (((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) * (mat x τ).map (starRingEnd ℂ))
      = (mat x τ).transpose * (((a : Matrix (Fin r) (Fin r) E).map τ.1).transpose * X.Gm.map τ.1 *
        ((a : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ)) * (mat x τ).map (starRingEnd ℂ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [key]

theorem lact_mem {a : GL (Fin r) E} (ha : IsUn X a) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact a x ∈ X.dom := by
  intro τ
  have e1 : mat (lact a x) τ = (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · have hu : IsUnit ((a : Matrix (Fin r) (Fin r) E).map τ.1).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (a.isUnit.map τ.1.mapMatrix)
    rw [e1, Matrix.det_mul]
    exact mul_ne_zero hu.ne_zero (hx τ).1
  · rw [dmin_lact ha]
    exact (hx τ).2 i

end GlobalTheory.Dict.Extend

theorem GlobalTheory.Dict.exists_form_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)) (𝓛 : Set (Lt E r)) (mu : GL (Fin r) E → Lt E r → ℂ) (la : Wt X.Ψ r) (Jx : Type) [Finite Jx] (L : Jx → Lt E r) (Q : Jx → Frame X.Ψ r → ℂ), (∀ ga ∈ Δ, IsUn X ga) → (∀ ga ∈ Δ, ∀ L' ∈ 𝓛, mapL ga L' ∈ 𝓛 ∧ ‖mu ga L'‖ = 1) → (∀ ga ∈ Δ, ∀ ga' ∈ Δ, ∀ L' ∈ 𝓛, mu (ga * ga') L' = mu ga (mapL ga' L') * mu ga' L') → (∀ k, L k ∈ 𝓛) → (∀ k k', ∀ ga ∈ Δ, mapL ga (L k) = L k' → k = k') → (∀ k, ∀ ga ∈ Δ, mapL ga (L k) = L k → mu ga (L k) = 1) → (∀ k, IsStabForm X Δ (L k) la (Q k)) → ∃ F : Lt E r → Frame X.Ψ r → ℂ, IsForm X Δ 𝓛 mu la F ∧ ∀ k, ∀ x ∈ X.dom, F (L k) x = Q k x := by
  intro E _ _ _ r X Δ 𝓛 mu la Jx _ L Q hun hmu hcoc hL hsep hst hQ
  let F : Lt E r → Frame X.Ψ r → ℂ := fun L' x =>
    if h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L' then
      (mu h.choose.2 (L h.choose.1))⁻¹ * Q h.choose.1 (lact h.choose.2⁻¹ x) else 0
  have key : ∀ k, ∀ a ∈ Δ, ∀ x ∈ X.dom,
      F (mapL a (L k)) x = (mu a (L k))⁻¹ * Q k (lact a⁻¹ x) := by
    intro k a ha x hx
    have h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = mapL a (L k) := ⟨(k, a), ha, rfl⟩
    simp only [F, dif_pos h]
    obtain ⟨h1, h2⟩ := h.choose_spec
    generalize h.choose = p at h1 h2
    obtain ⟨k', b⟩ := p
    dsimp only at h1 h2 ⊢
    have hs : a⁻¹ * b ∈ Δ := Δ.mul_mem (Δ.inv_mem ha) h1
    have h3 : mapL (a⁻¹ * b) (L k') = L k := by
      rw [Extend.mapL_mul, h2, ← Extend.mapL_mul, inv_mul_cancel, Extend.mapL_one]
    obtain rfl := hsep k' k _ hs h3
    have h4 : mu b (L k') = mu a (L k') := by
      have := hcoc a ha _ hs _ (hL k')
      rwa [mul_inv_cancel_left, h3, hst _ _ hs h3, _root_.mul_one] at this
    have h5 := (hQ k').inv _ hs h3 _ (Extend.lact_mem (hun _ (Δ.inv_mem h1)) hx)
    rw [Extend.lact_lact, mul_inv_cancel_right] at h5
    rw [h4, h5]
  have zero : ∀ L', (¬ ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L') → ∀ x, F L' x = 0 :=
    fun L' h x => by simp only [F, dif_neg h]
  choose C hC using fun k => (hQ k).bdd
  obtain ⟨B, hB⟩ := (Set.finite_range C).bddAbove
  refine ⟨F, ⟨fun L' _ => ?_, fun L' _ x hx b hb => ?_, fun g hg L' hL' x hx => ?_,
    max B 0, fun L' _ x hx => ?_⟩, fun k x hx => ?_⟩
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨⟨k, a⟩, ha, rfl⟩ := h
      refine DifferentiableOn.congr ?_ (key k a ha)
      exact ((hQ k).hol.comp (Extend.differentiable_lact a⁻¹).differentiableOn
        fun x hx => Extend.lact_mem (hun _ (Δ.inv_mem ha)) hx).const_mul _
    · exact (differentiableOn_const 0).congr fun x _ => zero L' h x
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨h1, -⟩ := h.choose_spec
      simp only [F, dif_pos h]
      rw [Extend.lact_rmul, (hQ _).bor _ (Extend.lact_mem (hun _ (Δ.inv_mem h1)) hx) b hb]
      ring
    · rw [zero L' h, zero L' h, mul_zero]
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨⟨k, a⟩, ha, rfl⟩ := h
      dsimp only at ha ⊢
      rw [← Extend.mapL_mul, key k _ (Δ.mul_mem hg ha) _ (Extend.lact_mem (hun g hg) hx), key k a ha x hx,
        hcoc g hg a ha _ (hL k), Extend.lact_lact, _root_.mul_inv_rev g a, inv_mul_cancel_right, mul_inv,
        _root_.mul_assoc]
    · rw [zero L' h, mul_zero]
      refine zero _ ?_ _
      rintro ⟨⟨k, a⟩, ha, h2⟩
      refine h ⟨(k, g⁻¹ * a), Δ.mul_mem (Δ.inv_mem hg) ha, ?_⟩
      dsimp only at h2 ⊢
      rw [Extend.mapL_mul, h2, ← Extend.mapL_mul, inv_mul_cancel, Extend.mapL_one]
  · by_cases h : ∃ p : Jx × GL (Fin r) E, p.2 ∈ Δ ∧ mapL p.2 (L p.1) = L'
    · obtain ⟨⟨k, a⟩, ha, rfl⟩ := h
      dsimp only at ha ⊢
      have hu := hun _ (Δ.inv_mem ha)
      have h1 := hC k _ (Extend.lact_mem hu hx)
      refine le_trans (le_of_eq ?_) (h1.trans ((hB ⟨k, rfl⟩).trans (le_max_left _ _)))
      simp only [Data.pnorm, Extend.dmin_lact hu]
      rw [key k a ha x hx, norm_mul, norm_inv, (hmu a ha _ (hL k)).2, inv_one, _root_.one_mul]
    · simp only [Data.pnorm]
      rw [zero L' h, norm_zero, zero_mul]
      exact le_max_right _ _
  · have h := key k 1 Δ.one_mem x hx
    rw [hst k 1 Δ.one_mem (Extend.mapL_one _), Extend.mapL_one, inv_one, inv_one, _root_.one_mul,
      Extend.lact_one] at h
    exact h
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ColPoly

section Deriv

variable {σ κ W W' : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup W']
  [NormedSpace ℂ W']

theorem polyDeriv_comp_linear {F : W' → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (A : W →L[ℂ] W')
    (P : MvPolynomial σ ℂ) (u : σ → W) (x : W) :
    I2.polyDeriv P u (fun z => F (A z)) x = I2.polyDeriv P (fun l => A (u l)) F (A x) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  have hcomp := A.iteratedFDeriv_comp_right hF x
    (i := Multiset.card (Finsupp.toMultiset m)) (by exact_mod_cast le_top)
  rw [show (fun z => F (A z)) = F ∘ A from rfl, hcomp]
  rfl

private theorem polyDeriv_C_indep (a : ℂ) (u v : σ → W) (F : W → ℂ) (x : W) :
    I2.polyDeriv (MvPolynomial.C a : MvPolynomial σ ℂ) u F x =
      I2.polyDeriv (MvPolynomial.C a : MvPolynomial σ ℂ) v F x := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : m = 0 := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_C, if_neg (Ne.symm hne)])
  subst hm0
  congr 1

theorem polyDeriv_subst [Fintype κ] {F : W → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F) (s : σ → κ → ℂ)
    (j : σ → κ → σ) (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ)
    (hΦ : ∀ l, Φ (MvPolynomial.X l) = ∑ k, MvPolynomial.C (s l k) * MvPolynomial.X (j l k))
    (u : σ → W) (P : MvPolynomial σ ℂ) (x : W) :
    I2.polyDeriv (Φ P) u F x = I2.polyDeriv P (fun l => ∑ k, s l k • u (j l k)) F x := by
  induction P using MvPolynomial.induction_on generalizing x with
  | C a =>
    rw [MvPolynomial.algHom_C]
    exact polyDeriv_C_indep a _ _ F x
  | add p q hp hq => rw [map_add (f := _), I2.polyDeriv_add, I2.polyDeriv_add, hp, hq]
  | mul_X p l hp =>
    have e1 : (fun y => I2.polyDeriv (Φ p) u F y) =
        fun y => I2.polyDeriv p (fun l => ∑ k, s l k • u (j l k)) F y := funext hp
    rw [polyDeriv_mul_X hF p _ l x, map_mul, hΦ l, Finset.mul_sum, I2.jof_polyDeriv_sum]
    simp_rw [MvPolynomial.C_mul', mul_smul_comm, I2.polyDeriv_smul, polyDeriv_mul_X hF (Φ p) u _ x, e1]

    rw [map_sum]
    simp only [map_smul, smul_eq_mul]

end Deriv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ}

noncomputable def hActL (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (h : Matrix (Fin n) (Fin n) E) :
    (Fin n → Fin g → ℂ) →L[ℂ] (Fin n → Fin g → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := hAct X idx h
      map_add' := fun x y => by funext k i; simp [hAct, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by funext k i; simp [hAct, Finset.mul_sum, mul_left_comm] }

end GlobalTheory.Dict.ColPoly


open GlobalTheory.Dict.ColPoly in
theorem GlobalTheory.Dict.exists_rowHighest_polyDeriv_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ∀ P ∈ Harm.rowHighest ℂ k k', ∃ P' ∈ Harm.rowHighest ℂ k k', ∀ F : (Fin n → Fin g → ℂ) → ℂ, AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv P (letterDir X hr idx) (fun z => F (hAct X idx h z)) 0 = I2.polyDeriv P' (letterDir X hr idx) F 0 := by
  intro E _ _ _ r X g q0 hr bas idx n _hs _hn h hh k k' P hP
  classical
  let A : X.Ψ → Matrix (Fin n) (Fin n) ℂ := fun t => (h.map (t.1 : E →+* ℂ))ᵀ
  let B : X.Ψ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => h.map (ComplexEmbedding.conjugate (t.1 : E →+* ℂ))
  have hAB : ∀ t, A t * B t = 1 := by
    intro t
    have h1 := congrArg (fun M => M.map (t.1 : E →+* ℂ)) hh
    simp only [Matrix.map_mul, GlobalTheory.SW.Base.ccT_map, Matrix.map_one _ (map_zero _) (map_one _)] at h1
    ext i j
    have h2 := congrFun (congrFun h1 j) i
    simp only [A, B, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.conjTranspose_apply, ComplexEmbedding.conjugate_coe_eq, Matrix.one_apply] at h2 ⊢
    convert h2 using 1
    · exact Finset.sum_congr rfl fun l _ => by rw [mul_comm]; rfl
    · by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
  let s : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → ℂ :=
    fun l k₁ => rowType X (rowOf X hr (l.1, l.2.1)) (h k₁ l.2.2)
  let j : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → Harm.Var X.Ψ q0 X.p0 (Fin n) :=
    fun l k₁ => (l.1, l.2.1, k₁)
  have hΦ : ∀ l, GlobalTheory.Harm.colSubst A B (MvPolynomial.X l) =
      ∑ k₁, MvPolynomial.C (s l k₁) * MvPolynomial.X (j l k₁) := by
    rintro ⟨t, (a | b), k₀⟩
    · have e : rowType X (t, rowIdx hr (Sum.inl a)) = t.1 := by
        simpa using rowType_rowOf_inl X hr t a
      simp [GlobalTheory.Harm.xForm, GlobalTheory.Harm.rowForm_apply, A, s, j, e]
    · have e : rowType X (t, rowIdx hr (Sum.inr b)) = ComplexEmbedding.conjugate t.1 := by
        simpa using rowType_rowOf_inr X hr t b
      simp [GlobalTheory.Harm.yForm, GlobalTheory.Harm.rowForm_apply, B, s, j, e, ComplexEmbedding.conjugate_coe_eq]
  have hdir : (fun l => hActL X idx h (letterDir X hr idx l)) =
      fun l => ∑ k₁, s l k₁ • letterDir X hr idx (j l k₁) := by
    funext l k₁ i
    show hAct X idx h (letterDir X hr idx l) k₁ i = _
    by_cases hi : i = idx.symm (rowOf X hr (l.1, l.2.1))
    · subst hi
      simp [hAct, letterDir, Pi.single_apply, Finset.sum_apply, s, j, ite_apply, mul_ite,
        Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp only [rowOf_apply] at hi
      simp [hAct, letterDir, Pi.single_apply, Finset.sum_apply, s, j, hi, ite_apply, mul_ite]
  refine ⟨GlobalTheory.Harm.colSubst A B P, GlobalTheory.Harm.colSubst_mem_rowHighest hAB hP, fun F hF => ?_⟩
  have hF' : ContDiff ℂ (⊤ : ℕ∞) F := contDiffOn_univ.1 (hF.contDiffOn uniqueDiffOn_univ)
  have e0 := polyDeriv_comp_linear hF' (hActL X idx h) P (letterDir X hr idx) 0
  rw [map_zero, hdir] at e0
  rw [show (fun z => F (hAct X idx h z)) = fun z => F (hActL X idx h z) from rfl, e0]
  exact (polyDeriv_subst hF' s j (GlobalTheory.Harm.colSubst A B) hΦ (letterDir X hr idx) P 0).symm
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.det_doubledCoordinates_to_rationalCoords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (idx : Fin g ≃ X.Ψ × Fin r) (e : (Fin g ⊕ Fin g) ≃ QI E r), ∃ c : ℂ, ∀ x₁ x₂ : Frame X.Ψ r, ∃ L : Matrix (QI E r) (Fin g ⊕ Fin g) ℂ, (L.submatrix e id).det = c * ∏ τ : X.Ψ, ((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det)⁻¹ ∧ ∀ (n : ℕ) (z₁ w : Fin n → Fin g → ℂ) (k : Fin n), zetaOf X.Ψ (dblz X idx x₁ x₂ z₁ w) (dblz' X idx x₁ x₂ z₁ w) k = L *ᵥ Sum.elim (z₁ k) (w k) := by
  first | exact @GlobalTheory.SW.det_dbl_coords | exact GlobalTheory.SW.det_dbl_coords | (intros; apply GlobalTheory.SW.det_dbl_coords <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.dblZ_mem_Hn_and_det_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, IsType X.Ψ ∧ dblZ X x₁ x₂ ∈ Hn X.Ψ r ∧ ∀ τ, (aLin X x₁ x₂ τ).det ≠ 0 ∧ (aAnti X x₁ x₂ τ).det ≠ 0 ∧ aLin X x₂ x₁ τ = (aAnti X x₁ x₂ τ).map conj := by
  first | exact @GlobalTheory.SW.dblZ_mem_Hn | exact GlobalTheory.SW.dblZ_mem_Hn | (intros; apply GlobalTheory.SW.dblZ_mem_Hn <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.level_structure_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (D : Level X) (hn : r ≤ n), X.Λ ∈ D.lats ∧ (∀ u k k', D.Red u k → D.Red u k' → k = k') ∧ (∀ γ, γ ∈ D.grp ↔ IsUn X γ ∧ ∃ k ∈ D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k) ∧ (∀ L ∈ D.lats, SelfD X (D.sh L) ∧ Submodule.span E (L : Set (Fin r → E)) = ⊤ ∧ (∀ L' ∈ D.lats, (D.sh L').toAddSubgroup.relIndex (D.sh L).toAddSubgroup = L'.toAddSubgroup.relIndex L.toAddSubgroup) ∧ ∀ γ ∈ D.grp, mapL γ L ∈ D.lats ∧ D.sh (mapL γ L) = mapL γ (D.sh L)) ∧ (∀ k : D.J, ‖((D.lam k : ℂˣ) : ℂ)‖ = 1) ∧ (∀ y y' : Matrix (Fin n) (Fin r) E, (∀ k, Cong X D.𝔪 (y k) (y' k)) → D.dat hn y = D.dat hn y') ∧ ∀ γ ∈ D.grp, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → ∀ y : Matrix (Fin n) (Fin r) E, D.dat hn (y * (γ : Matrix (Fin r) (Fin r) E)ᵀ) = (D.lam k : ℂˣ) * D.dat hn y := by
  first | exact @GlobalTheory.SW.level_laws | exact GlobalTheory.SW.level_laws | (intros; apply GlobalTheory.SW.level_laws <;> assumption)
end
