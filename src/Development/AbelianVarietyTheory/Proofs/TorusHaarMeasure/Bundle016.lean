module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle025
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle010
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PoincareAssembly

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_chi {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, hpow⟩ := X.χ_fin la
  have h := congrArg norm (hpow γ hγ)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h

theorem cpt_lact {r : ℕ} (X : Data E r) (γ : GL (Fin r) E) (x : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (lact γ x) z = lact γ (cpt X x z) := by
  funext τ
  show (mat (lact γ x) τ * mat (nmat X z) τ : Matrix (Fin r) (Fin r) ℂ) =
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (cpt X x z) τ : Matrix (Fin r) (Fin r) ℂ)
  simp only [mat, lact, cpt, rmul]
  exact Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (x τ))
    (Matrix.of (nmat X z τ))

theorem dom_of_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : lact γ x ∈ X.dom) : x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    have h := (hx τ).1
    rw [e1, Matrix.det_mul] at h
    exact right_ne_zero_of_mul h
  · have := (hx τ).2 i
    unfold dmin at this ⊢
    rwa [OntoS.gram_lact X hγ] at this

theorem isOrth_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : IsOrth X x) : IsOrth X (lact γ x) := fun τ => by
  rw [OntoS.gram_lact X hγ, hx τ]

theorem phla_lact {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (x : Frame X.Ψ r) : phla X la (lact γ x) = phla X la x := by
  unfold phla Data.nfac dmin
  simp only [OntoS.gram_lact X hγ]

theorem poin_mul {r : ℕ} (X : Data E r) (la la' : Wt X.Ψ r) (P g : Frame X.Ψ r → ℂ)
    (hg : X.IsSec la' g) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x := by
  unfold poin
  rw [← tsum_mul_left]
  refine tsum_congr fun γ => ?_
  have h1 : X.χ la' γ.1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_chi X la' γ.2]; exact one_ne_zero
  have h2 : X.χ la γ.1 ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_chi X la γ.2]; exact one_ne_zero
  simp only [X.χ_add la la' γ.1 γ.2, hg.2.2 γ.1 γ.2 x hx]
  field_simp

theorem poinStatement_of :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ κ : Frame X.Ψ r → ℝ, Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x, IsOrth X x → ENNReal.ofReal ‖P x‖ ≤ ENNReal.ofReal (C * Real.sqrt (κ x)) * ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom), (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ‖P (cpt X x z)‖ ≤ C * Real.sqrt (κ x)) → (∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (κ : Frame X.Ψ r → ℝ) (P : Frame X.Ψ r → ℂ), IsBEq X la P → (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) → (∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ‖P (cpt X x z)‖ ≤ C * Real.sqrt (κ x)) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) ∧ X.IsBddSec la (poin X la P)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (κ : Frame X.Ψ r → ℝ), (Measurable κ ∧ (∀ x ∈ X.dom, 0 < κ x ∧ κ x ≤ 1) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, κ (rmul x b) = κ x) ∧ (∀ z ∈ OmF X x0, κ (cpt X x0 z) = kaF X x0 bb z) ∧ (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) ≤ C) ∧ ∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → κ (cpt X x z) ≤ C * κ x) → IsMetricW X la W → WLower X la W → ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), InAt X x0 W bb F → IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) → ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) → (PoinStatement (E := E)) := by
  intro hκ hball hloc hbdd hFF r X x0 ho hPD la W bb hW hWl hbb F P _ hF hP hPF
  obtain ⟨κ, hκ⟩ := hκ r X x0 ho hPD bb hbb
  obtain ⟨hs, hb⟩ := hbdd r X la κ P hP hκ.2.2.2.2.1
    (hloc r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF)
  refine ⟨hs, hb, hFF r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF hs, fun ρ hρ hρ1 => ?_,
    fun la' g hg x hx => poin_mul X la la' P g hg hx⟩
  obtain ⟨C, hC⟩ := hball r X x0 ho la W bb κ hκ hW hWl F P hF hP hPF ρ hρ hρ1
  obtain ⟨K, hK, hKs⟩ := hκ.2.2.2.2.1
  refine ⟨C * K.toReal, fun x hx hxo => ?_⟩
  set S : ℝ≥0∞ := ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
    (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ) with hS
  have hterm : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ ≤
      ENNReal.ofReal C * S * ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) := by
    intro γ
    rw [← ofReal_norm, norm_mul, norm_inv, norm_chi X la γ.2, inv_one, one_mul]
    refine (hC _ (isOrth_lact X γ.2 hxo)).trans ?_
    rw [ENNReal.ofReal_mul' (Real.sqrt_nonneg _), mul_right_comm]
    gcongr
    refine iSup_le fun z => iSup_le fun hz => iSup_le fun hd => ?_
    rw [cpt_lact] at hd ⊢
    have hd' := dom_of_lact X γ.2 hd
    rw [phla_lact X la γ.2, hW.2.2 γ.1 γ.2 _ hd']
    exact le_iSup_of_le z (le_iSup_of_le hz (le_iSup_of_le hd' le_rfl))
  calc ENNReal.ofReal ‖poin X la P x‖
      = ‖∑' γ : X.Γ, (X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ := ofReal_norm _
    _ ≤ ∑' γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖ₑ := enorm_tsum_le_tsum_enorm
    _ ≤ ∑' γ : X.Γ, ENNReal.ofReal C * S * ENNReal.ofReal (Real.sqrt (κ (lact γ.1 x))) :=
        ENNReal.tsum_le_tsum hterm
    _ ≤ ENNReal.ofReal C * S * K := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact hKs x hx
    _ = ENNReal.ofReal (C * K.toReal) * S := by
        rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK.ne, mul_right_comm]

end GlobalTheory.PoincareAssembly
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.MajInv

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section copy
open Matrix
open scoped ComplexConjugate
variable {r : ℕ} (X : Data E r)

omit [NumberField E] [IsCMField E] in
theorem col_map_eq (P : Matrix (Fin r) (Fin r) E) (τ : E →+* ℂ) (k : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col (P.map τ) k = Data.emb τ (P *ᵥ Pi.single k 1) := by
  funext i
  simp [ReciprocityTheory.ChartRestriction.G.FD.col, Data.emb]

theorem hermC_expand (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  rw [Data.mulVec_eq_sum_col (P.map τ) u, Data.mulVec_eq_sum_col (P.map τ) w, hermC_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hermC_smul_left, hermC_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hermC_smul_right, col_map_eq, col_map_eq, hermC_emb]
  ring

theorem hermC_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X.Gm u w := by
  have h1 : ((1 : Matrix (Fin r) (Fin r) E).map τ) = 1 := Matrix.map_one τ τ.map_zero τ.map_one
  conv_rhs => rw [← one_mulVec u, ← one_mulVec w, ← h1]
  rw [hermC_expand, hermC_expand]
  simp only [hγ, one_mulVec]

theorem gram_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm (γ.map τ * Y) = ReciprocityTheory.ChartRestriction.G.FD.gram τ X.Gm Y := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, of_apply]
  have hc : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.col (γ.map τ * Y) c = (γ.map τ) *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col Y c := by
    intro c; funext i; simp [ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mul_apply, mulVec, dotProduct]
  rw [hc, hc, hermC_stab X hγ]

end copy

theorem exists_colP_rmul_eq_sum {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (a : Fin X.p0) :
    ∃ L : Fin X.p0 → ℂ, X.colP (rmul x b) τ a = ∑ c, L c • X.colP x τ c := by
  classical
  refine ⟨fun c => b τ (Fin.castLE X.p0_le c) (Fin.castLE X.p0_le a), ?_⟩
  funext k
  have e1 : X.colP (rmul x b) τ a k = ∑ j, x τ k j * b τ j (Fin.castLE X.p0_le a) := by
    show (mat x τ * mat b τ : Matrix (Fin r) (Fin r) ℂ) k (Fin.castLE X.p0_le a) = _
    rw [Matrix.mul_apply]; rfl
  rw [e1, Finset.sum_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE X.p0_le) ((Fin.castLE_injective _).injOn)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun j _ hj => ?_) (fun c _ => ?_)
  · have hj' : X.p0 ≤ (j : ℕ) := by
      by_contra h
      exact hj ⟨⟨j, not_le.mp h⟩, by simp, by ext; simp⟩
    rw [(hb τ).2 j _ (by
      show ((Fin.castLE X.p0_le a : Fin r) : ℕ) < j
      have := a.isLt
      simp only [Fin.val_castLE]; omega), mul_zero]
  · show b τ _ _ * x τ k _ = _
    rw [mul_comm]

theorem maj_rmul {r : ℕ} (X : Data E r) {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (v : Fin r → ℂ) : X.maj (rmul x b) τ v = X.maj x τ v := by
  have h := MajorantConjugateTransfer.maj_transfer X hx (OrthogonalFrameDomain.rmul_mem_dom X hx hb) τ 1 1 (by simp) (by simp)
    (fun c => ?_) (fun a => ?_) v
  · simpa using h
  · have := exists_colP_rmul_eq_sum X (rmul x b) (ExtFPf.invF_mem X hb) τ c
    rw [ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF] at this
    simpa using this
  · simpa using exists_colP_rmul_eq_sum X x hb τ a

theorem gram_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) :=
  gram_stab X hγ.1 τ.1 (mat x τ)

theorem lact_mem_dom {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : lact γ x ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have e1 : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
    rw [e1, Matrix.det_mul, show ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det =
      τ.1 (γ : Matrix (Fin r) (Fin r) E).det by rw [RingHom.map_det]; rfl]
    refine mul_ne_zero ?_ (hx τ).1
    have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).det) :=
      (Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit
    exact (hu.map τ.1).ne_zero
  · have := (hx τ).2 i
    unfold dmin at this ⊢
    rwa [gram_lact X hγ]

theorem maj_lact {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ)
    (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj (lact γ x) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) =
      X.maj x τ v := by
  have hc : ∀ c, col (mat (lact γ x) τ) c =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ col (mat x τ) c := by
    intro c; funext i
    show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) i c = _
    simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  unfold Data.maj Data.posPart Data.gramPos
  simp only [hc, gram_lact X hγ, hermC_stab X hγ.1]

end GlobalTheory.MajInv

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem maj_lact_rmul :
    (∀ (r : ℕ) (X : Data E r) (γ : GL (Fin r) E), IsUStab X.Gm X.Λ γ → ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj (lact γ (rmul x b)) τ (Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) v) = X.maj x τ v) := by
  intro r X γ hγ x hx b hb
  refine ⟨MajInv.lact_mem_dom X hγ (OrthogonalFrameDomain.rmul_mem_dom X hx hb), fun τ v => ?_⟩
  rw [MajInv.maj_lact X hγ, MajInv.maj_rmul X hx hb]

end GlobalTheory
end
