module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelWeilFormulaDegreeSucc
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle049
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle052
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle028
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle020
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle018
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.siegelWeil_formula_degree_succ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * (N + 1) < n → SWAt Ψ n N → SWAt Ψ n (N + 1) := by
  first | exact @GlobalTheory.SW.swAt_succ | exact GlobalTheory.SW.swAt_succ | (intros; apply GlobalTheory.SW.swAt_succ <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.doubledGaussianKernel_diagonal_translation_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ a b w : WR X n, cexp (π * I * (EFR X w (a - b) : ℝ)) * (gaussR X bas idx x₁ (zR X idx x₁ (w + a)) * conj (gaussR X bas idx x₂ (zR X idx x₂ (w + b))) * kZero X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))) = gaussR X bas idx x₁ (zR X idx x₁ a) * conj (gaussR X bas idx x₂ (zR X idx x₂ b)) * kZero X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)) := by
  first | exact @GlobalTheory.Ker.Diag.kernel_diag | exact GlobalTheory.Ker.Diag.kernel_diag | (intros; apply GlobalTheory.Ker.Diag.kernel_diag <;> assumption)
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

theorem _root_.GlobalTheory.T.vacuum_multiplier_eq_one_on_stabiliser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (D : SW.Level X) (hn : r ≤ n) (ph : (Fin n → LaJ Xo c d) → c.F), IsSympl X bas → Even n → LevTie d σ ph D hn → ∀ (D' : Datum H) (φ : D'.La →ₗ[𝓞 E] (Fin r → E)), r = D'.p + D'.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((D'.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → ∀ L ∈ D.lats, ∀ ga ∈ D.grp, mapL ga L = L → mu ga L = 1 ∧ ∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + l.M • u' := by
  first | exact @GlobalTheory.Dict.mult_eq_one_on_stab | exact GlobalTheory.Dict.mult_eq_one_on_stab | (intros; apply GlobalTheory.Dict.mult_eq_one_on_stab <;> assumption)
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

theorem _root_.GlobalTheory.T.exists_letterRowWeightDictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (σ : c.F →+* ℂ) (r g n : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (e : Fin g ≃ Lt1 Dw), _root_.Formalism.L2.PjFree.GoodEmb c σ → r = Dw.p + Dw.q → X.p0 = Dw.q → (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) → SelfD X X.Λ → Dom a n → ∃ Dc : Dic Dw c σ X g Dw.p n a, Dc.e = e ∧ (LastPos Dw a → 0 < Dw.p → ∃ τ, ∃ i : Fin Dw.p, i.val + 1 = Dw.p ∧ 1 ≤ Dc.k τ i) := by
  first | exact @GlobalTheory.Dict.exists_dic | exact GlobalTheory.Dict.exists_dic | (intros; apply GlobalTheory.Dict.exists_dic <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

namespace DblVan

theorem vecMul_inv_inl {E : Type} [Field E] {N : ℕ} {γ : M2 E N} (hγ : IsUnit γ.det)
    {u : Fin N ⊕ Fin N → E} (hu : u ∈ botSpan γ) (a : Fin N) : (u ᵥ* γ⁻¹) (Sum.inl a) = 0 := by
  change u ∈ Submodule.span E (Set.range fun b : Fin N => γ (Sum.inr b)) at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx

    have hrow : (γ (Sum.inr b) ᵥ* γ⁻¹) (Sum.inl a) = (γ * γ⁻¹) (Sum.inr b) (Sum.inl a) := rfl
    rw [hrow, Matrix.mul_nonsing_inv γ hγ, Matrix.one_apply_ne (by simp)]
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.add_vecMul, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Matrix.smul_vecMul, Pi.smul_apply, hx, smul_zero]

theorem heisH_zero_apply_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
    (b : Matrix (Fin n) (Fin N) E) (ψ : Matrix (Fin n) (Fin N) E → ℂ) : heisH 0 b ψ 0 = ψ 0 := by
  simp [heisH, cc]

theorem toCols_eq_zero {E : Type} [Field E] {n N : ℕ} {γ T : M2 E N} (hγ : IsUnit γ.det)
    {ξ : Fin N → E} (hu : Sum.elim ξ 0 ᵥ* T ∈ botSpan γ) (v : Fin n → E) :
    (Matrix.fromCols (vecMulVec v ξ) (0 : Matrix (Fin n) (Fin N) E) * T * γ⁻¹).toCols₁ = 0 := by
  ext k a
  rw [Matrix.toCols₁_apply, Matrix.zero_apply]

  have hrow : (Matrix.fromCols (vecMulVec v ξ) (0 : Matrix (Fin n) (Fin N) E) * T) k =
      v k • (Sum.elim ξ 0 ᵥ* T) := by
    ext j
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fintype.sum_sum_type, vecMulVec_apply,
      Finset.mul_sum, mul_assoc]
  have hentry : (Matrix.fromCols (vecMulVec v ξ) (0 : Matrix (Fin n) (Fin N) E) * T * γ⁻¹) k
      (Sum.inl a) = ((v k • (Sum.elim ξ 0 ᵥ* T)) ᵥ* γ⁻¹) (Sum.inl a) := by
    rw [← hrow]; rfl
  rw [hentry]
  exact vecMul_inv_inl hγ (Submodule.smul_mem _ _ hu) a

end DblVan


open DblVan in
theorem weil_dbl_zero_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → ∀ ξ : Fin r → E, (∃ (s : Finset (Fin n → E)) (a : (Fin n → E) → ℂ), ∑ v ∈ s, a v ≠ 0 ∧ ∑ v ∈ s, a v • heisG X bas (vecMulVec v ξ) φ₁ = 0) → ∀ γ ∈ UU E r, Sum.elim ξ 0 ᵥ* dblT X ∈ botSpan γ → weil X.Ψ γ (dbl X bas idx φ₁ φ₂) 0 = 0 := by
  intro E _ _ _ r X g bas idx n hs hn φ₁ φ₂ h₁ h₂ ξ hker γ hγ hξ
  obtain ⟨s, a, hsum, hkill⟩ := hker
  have hΨ : IsType X.Ψ := X.cmType
  have hγu : IsUnit γ.det := (HAct.group_part hγ).1

  have hSBd : ∀ ψ : TF n g, IsSB ψ → IsSB (dbl X bas idx ψ φ₂) := fun ψ hψ =>
    (GlobalTheory.T.doubledHermitianTestFunction_spec E r X g bas idx n hs hn ψ φ₂ hψ h₂).1
  have hΦ := hSBd φ₁ h₁
  have hG := (heisG_laws E r X g bas idx n hs hn).2.2.2
  have hwadd : ∀ f f' : Matrix (Fin n) (Fin r) E → ℂ, IsSB f → IsSB f' →
      weil X.Ψ γ (f + f') = weil X.Ψ γ f + weil X.Ψ γ f' := fun f f' hf hf' =>
    ((GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E X.Ψ hΨ n r hn γ hγ f hf).2.2.2.1 f' hf').2
  have hwsmul : ∀ (c : ℂ) (f : Matrix (Fin n) (Fin r) E → ℂ), IsSB f →
      weil X.Ψ γ (c • f) = c • weil X.Ψ γ f := fun c f hf =>
    (GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E X.Ψ hΨ n r hn γ hγ f hf).2.2.2.2.1 c

  have hdbl0 : dbl X bas idx (0 : TF n g) φ₂ = 0 := by
    have h := (GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂).2.1 0 1
    rwa [zero_smul, one_smul, zero_mul, zero_smul] at h
  have hw0 : weil X.Ψ γ (0 : Matrix (Fin n) (Fin r) E → ℂ) = 0 := by
    have h := hwsmul 0 _ hΦ
    rwa [zero_smul, zero_smul] at h

  have hone : ∀ v : Fin n → E, weil X.Ψ γ (dbl X bas idx (heisG X bas (vecMulVec v ξ) φ₁) φ₂) 0 =
      weil X.Ψ γ (dbl X bas idx φ₁ φ₂) 0 := by
    intro v
    have h3 := (GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn φ₁ φ₂ h₁ h₂).2.2 (vecMulVec v ξ) 0
    rw [(hG 0 φ₂ h₂).2.1] at h3
    rw [h3, (GlobalTheory.T.hermitianHeisenbergOperator_laws E X.Ψ hΨ n r hn _ _ _ hΦ).2.2 γ hγ, Matrix.fromCols_toCols,
      DblVan.toCols_eq_zero hγu hξ v, DblVan.heisH_zero_apply_zero]

  have hlin : ∀ t : Finset (Fin n → E),
      IsSB (∑ v ∈ t, a v • heisG X bas (vecMulVec v ξ) φ₁) ∧
      weil X.Ψ γ (dbl X bas idx (∑ v ∈ t, a v • heisG X bas (vecMulVec v ξ) φ₁) φ₂) =
        ∑ v ∈ t, a v • weil X.Ψ γ (dbl X bas idx (heisG X bas (vecMulVec v ξ) φ₁) φ₂) := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨isSB_zero, by rw [Finset.sum_empty, Finset.sum_empty, hdbl0, hw0]⟩
    | insert w t hw ih =>
      obtain ⟨hS, hval⟩ := ih
      have hGw := (hG (vecMulVec w ξ) φ₁ h₁).1
      have hcGw := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) _ _ hGw hGw).2.1 (a w)
      rw [Finset.sum_insert hw, Finset.sum_insert hw]
      refine ⟨(isSB_algebra_haar_linear ℚ (Fin n) (Fin g) _ _ hcGw hS).1, ?_⟩
      have hI := GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn _ φ₂ hcGw h₂
      have hJ := GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg E r X g bas idx n hs hn _ φ₂ hGw h₂
      have hsm : dbl X bas idx (a w • heisG X bas (vecMulVec w ξ) φ₁) φ₂ =
          a w • dbl X bas idx (heisG X bas (vecMulVec w ξ) φ₁) φ₂ := by
        have h := hJ.2.1 (a w) 1
        rwa [one_smul, map_one, mul_one] at h
      rw [(hI.1 _ hS).1, hwadd _ _ (hSBd _ hcGw) (hSBd _ hS), hval, hsm,
        hwsmul _ _ (hSBd _ hGw)]

  have hmain := (hlin s).2
  rw [hkill, hdbl0, hw0] at hmain
  have h0 := congrFun hmain 0
  simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hone,
    ← Finset.sum_mul] at h0
  exact (mul_eq_zero.mp h0.symm).resolve_left hsum

end GlobalTheory.SW
end
