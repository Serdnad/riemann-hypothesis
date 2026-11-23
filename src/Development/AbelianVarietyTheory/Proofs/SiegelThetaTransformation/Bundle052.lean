module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MultiplierSqMulDetUnitaryColumnChange
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetFrameNeZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledThetaTestFunctionSesquilinearHeisenberg
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle031
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle046
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle051
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaInnerProductEqRealTorusMean
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle005

@[expose] public section

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker.Diag

open GlobalTheory.SW.DblLin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)


variable (X) in
noncomputable def kRow (x₁ x₂ : Frame X.Ψ r) (z w : Fin g → ℂ) : ℂ :=
  ∑ τ, cz' X idx x₁ x₂ τ (z, w) ⬝ᵥ (imH (dblZ X x₁ x₂ τ))⁻¹ *ᵥ cz X idx x₁ x₂ τ (z, w)

theorem kZero_eq (x₁ x₂ : Frame X.Ψ r) (z w : Fin n → Fin g → ℂ) :
    kZero X idx x₁ x₂ z w =
      (∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹) *
        cexp (π * ∑ k, kRow X idx x₁ x₂ (z k) (w k)) := by
  simp only [kZero, Finset.prod_mul_distrib, ← Complex.exp_sum, ← Finset.mul_sum, kRow]
  rw [Finset.sum_comm]
  rfl

theorem kRow_per (hs : IsSympl X bas) {x₁ x₂ : Frame X.Ψ r} (h₁ : x₁ ∈ X.dom) (h₂ : x₂ ∈ X.dom)
    (y : Fin r → E) (z z' : Fin g → ℂ) :
    kRow X idx x₁ x₂ (pv X idx x₁ y + z) (fun i => conj ((pv X idx x₂ y + z') i)) =
      hx X bas idx x₁ (z + (1 / 2 : ℂ) • pv X idx x₁ y) (pv X idx x₁ y) +
      conj (hx X bas idx x₂ (z' + (1 / 2 : ℂ) • pv X idx x₂ y) (pv X idx x₂ y)) +
      kRow X idx x₁ x₂ z (fun i => conj (z' i)) := by
  have h := expo_row idx hs h₁ h₂ y y z (star z')
  have e0 : ∀ τ : X.Ψ, Data.emb τ.1 (0 : Fin r → E) = 0 := fun τ => by
    funext a; simp [Data.emb]
  have e1 : (fun i => conj ((pv X idx x₂ y + z') i)) = star z' + star (per X x₂ y ∘ idx) := by
    funext i; simp [pv, add_comm]
  rw [e1, add_comm (pv X idx x₁ y) z]
  simp only [sub_self, e0, star_zero, zero_dotProduct, dotProduct_zero, add_zero,
    Finset.sum_const_zero, mul_zero, Pi.zero_apply, star_star, hermForm_Hm] at h
  simp only [cc, map_zero, mul_zero, Finset.sum_const_zero, Rat.cast_zero, add_zero] at h
  exact h

theorem continuous_kRow (x₁ x₂ : Frame X.Ψ r) :
    Continuous fun p : (Fin g → ℂ) × (Fin g → ℂ) => kRow X idx x₁ x₂ p.1 p.2 := by
  refine continuous_finsetSum _ fun τ _ => ?_
  exact (cz' X idx x₁ x₂ τ).continuous_of_finiteDimensional.dotProduct
    (continuous_const.matrix_mulVec (cz X idx x₁ x₂ τ).continuous_of_finiteDimensional)

theorem continuous_hx (x : Frame X.Ψ r) :
    Continuous fun z : Fin g → ℂ => hx X bas idx x z z :=
  (continuous_const.matrix_mulVec continuous_id).dotProduct
    (continuous_const.matrix_mulVec (continuous_const.matrix_mulVec continuous_id).star)

theorem kernel_diag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, ∀ a b w : WR X n, cexp (π * I * (EFR X w (a - b) : ℝ)) * (gaussR X bas idx x₁ (zR X idx x₁ (w + a)) * conj (gaussR X bas idx x₂ (zR X idx x₂ (w + b))) * kZero X idx x₁ x₂ (zR X idx x₁ (w + a)) (fun k i => conj (zR X idx x₂ (w + b) k i))) = gaussR X bas idx x₁ (zR X idx x₁ a) * conj (gaussR X bas idx x₂ (zR X idx x₂ b)) * kZero X idx x₁ x₂ (zR X idx x₁ a) (fun k i => conj (zR X idx x₂ b k i)) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn x₁ h₁ x₂ h₂ a b w
  obtain ⟨⟨L₁, hL₁⟩, im₁, -, hd, -⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x₁ h₁
  obtain ⟨⟨L₂, hL₂⟩, im₂, -⟩ := GlobalTheory.T.realPeriodMap_homeomorph_riemannForm_density E r X g q0 hr bas idx n hs hn x₂ h₂
  have add₁ (u v : WR X n) : zR X idx x₁ (u + v) = zR X idx x₁ u + zR X idx x₁ v := by
    rw [← hL₁, ← hL₁, ← hL₁, map_add (f := _)]
  have add₂ (u v : WR X n) : zR X idx x₂ (u + v) = zR X idx x₂ u + zR X idx x₂ v := by
    rw [← hL₂, ← hL₂, ← hL₂, map_add (f := _)]
  have hE (w : WR X n) : EFR X w (a - b) = EFR X w a - EFR X w b := by
    rw [← im₁, ← im₁, ← im₁, ← sub_im, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eq_sub_iff_add_eq, ← GlobalTheory.Dict.fock_hx_add_right, ← Pi.add_apply (zR X idx x₁ (a - b)),
      ← add₁, sub_add_cancel]
  have key : ∀ w : WR X n, π * I * (EFR X w (a - b) : ℝ) +
      (-(π / 2 * ∑ k, hx X bas idx x₁ (zR X idx x₁ (w + a) k) (zR X idx x₁ (w + a) k)) +
        conj (-(π / 2 * ∑ k, hx X bas idx x₂ (zR X idx x₂ (w + b) k) (zR X idx x₂ (w + b) k))) +
        π * ∑ k, kRow X idx x₁ x₂ (zR X idx x₁ (w + a) k) (fun i => conj (zR X idx x₂ (w + b) k i))) =
      -(π / 2 * ∑ k, hx X bas idx x₁ (zR X idx x₁ a k) (zR X idx x₁ a k)) +
        conj (-(π / 2 * ∑ k, hx X bas idx x₂ (zR X idx x₂ b k) (zR X idx x₂ b k))) +
        π * ∑ k, kRow X idx x₁ x₂ (zR X idx x₁ a k) (fun i => conj (zR X idx x₂ b k i)) := by
    intro w
    refine hd.induction_on w (isClosed_eq ?_ continuous_const) fun y => ?_
    · have c₁ (k) : Continuous fun w : WR X n => zR X idx x₁ (w + a) k := by
        simp only [← hL₁]; fun_prop
      have c₂ (k) : Continuous fun w : WR X n => zR X idx x₂ (w + b) k := by
        simp only [← hL₂]; fun_prop
      have c₃ : Continuous fun w : WR X n => EFR X w (a - b) := by
        unfold EFR hermC; fun_prop
      have c₄ := continuous_finsetSum Finset.univ fun k _ =>
        (continuous_hx (bas := bas) idx x₁).comp (c₁ k)
      have c₅ := continuous_finsetSum Finset.univ fun k _ =>
        (continuous_hx (bas := bas) idx x₂).comp (c₂ k)
      have c₆ := continuous_finsetSum Finset.univ fun k _ =>
        (continuous_kRow idx x₁ x₂).comp ((c₁ k).prodMk (c₂ k).star)
      exact (continuous_const.mul (continuous_ofReal.comp c₃)).add
        (((continuous_const.mul c₄).neg.add
          (continuous_conj.comp (continuous_const.mul c₅).neg)).add (continuous_const.mul c₆))
    · have i₁ := sub_conj (∑ k, hx X bas idx x₁ (zR X idx x₁ (embR X y) k) (zR X idx x₁ a k))
      have i₂ := sub_conj (∑ k, hx X bas idx x₂ (zR X idx x₂ (embR X y) k) (zR X idx x₂ b k))
      rw [im₁] at i₁
      rw [im₂] at i₂
      rw [hE, add₁, add₂]
      simp only [Pi.add_apply (zR X idx _ (embR X y)), zR_embR] at i₁ i₂ ⊢
      simp only [kRow_per idx hs h₁ h₂]
      have s₁ (k) := GlobalTheory.Dict.fock_hx_conj X bas idx x₁ hs h₁ (pv X idx x₁ (y k)) (zR X idx x₁ a k)
      have s₂ (k) := GlobalTheory.Dict.fock_hx_conj X bas idx x₂ hs h₂ (pv X idx x₂ (y k)) (zR X idx x₂ b k)

      simp only [GlobalTheory.Dict.fock_hx_add_left, GlobalTheory.Dict.fock_hx_add_right, GlobalTheory.Dict.fock_hx_smul_left,
      s₁, s₂, Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum, map_add, map_mul, map_neg,
      conj_conj, map_div₀, conj_ofReal, map_ofNat, map_one]
      push_cast at i₁ i₂ ⊢
      linear_combination (-(π : ℂ) / 2) * i₁ + ((π : ℂ) / 2) * i₂
  simp only [gaussR, kZero_eq, ← Complex.exp_conj]
  have := congrArg cexp (key w)
  simp only [Complex.exp_add] at this
  linear_combination (∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹) * this

end GlobalTheory.Ker.Diag
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

theorem _root_.GlobalTheory.T.multiplier_sq_mul_det_unitary_column_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ Λ ∈ Vset E n 1, ∀ Λ' ∈ Vset E n 1, ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ x ∈ X.dom, ∀ t : ℂ, ‖t‖ = 1 → (∀ z : Fin n → Fin g → ℂ, thA X bas idx (unitv (projA X bas w (tens Λ' L) v)) x (Dict.hAct X idx h z) = t * thA X bas idx (unitv (projA X bas w (tens Λ L) v)) x z) → IsMu (t ^ 2 * ∏ i : Fin g, rowType X (idx i) h.det) := by
  first | exact @GlobalTheory.Phase.Mult.isMu_multiplier_sq_mul_det | exact GlobalTheory.Phase.Mult.isMu_multiplier_sq_mul_det | (intros; apply GlobalTheory.Phase.Mult.isMu_multiplier_sq_mul_det <;> assumption)
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

theorem GlobalTheory.Dict.conjI_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (l : Geo.Tor.Level H) : conjI (Mfr l) = l.Mb := by
  have hb : ∀ a : 𝓞 E, Lev.bar a = H.bar a := fun a => by
    apply IsFractionRing.injective (𝓞 E) E
    exact (H.bar_eq a).symm
  ext a
  rw [Lev.mem_conjI, hb, Mfr,
    Ideal.mem_map_iff_of_surjective (H.bar : 𝓞 E →+* 𝓞 E) H.bar.surjective]
  exact ⟨fun ⟨y, hy, e⟩ => H.bar.injective e ▸ hy, fun h => ⟨a, h, rfl⟩⟩

theorem GlobalTheory.Dict.mult_eq_one_on_stab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (D : SW.Level X) (hn : r ≤ n) (ph : (Fin n → LaJ Xo c d) → c.F), IsSympl X bas → Even n → LevTie d σ ph D hn → ∀ (D' : Datum H) (φ : D'.La →ₗ[𝓞 E] (Fin r → E)), r = D'.p + D'.q → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a b, ((D'.EF a b : ℤ) : ℚ) = EF X (φ a) (φ b)) → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → ∀ L ∈ D.lats, ∀ ga ∈ D.grp, mapL ga L = L → mu ga L = 1 ∧ ∀ u ∈ L, ∃ u' ∈ L, (ga : Matrix (Fin r) (Fin r) E) *ᵥ u = u + l.M • u' := by
  intro E _ _ _ H Dw l Xo c n d σ r g X bas idx D hn ph hs hev hT D' φ hr hinj hsp hEF v₀ hv mu hmu L hL ga
    hga hfix
  have hle : D.𝔪 ≤ Mfr l := by rw [hT.prod]; exact Ideal.mul_le.2 fun a ha b _ => Ideal.mul_mem_right b _ ha
  have hN : Mfr l * conjI (Mfr l) = Ideal.span {(l.M : 𝓞 E)} := by
    rw [conjI_half, mul_comm]; exact l.prod
  obtain ⟨h1, h2, h3⟩ := (stab_trivial_mod E r X g bas idx n hs hev D (Mfr l) l.M hle hN
    (fun k hk => (hT.grp k).1 hk) ga hga).2 L hL hfix
  refine ⟨?_, h1⟩
  obtain ⟨-, -, hgrp, hlat, -⟩ := GlobalTheory.SW.level_laws E r X g bas idx n hs hev D hn
  obtain ⟨hu, k, hk, hred⟩ := (hgrp ga).1 hga
  obtain ⟨hsd, -, -, hsh⟩ := hlat L hL
  have hfix' : mapL ga (D.sh L) = D.sh L := by rw [← (hsh ga hga).2, hfix]
  have hvac := hv L hL
  have hw := GlobalTheory.T.vacuumMultiplier_trivial_principalCongruence E r X g bas idx n hs hev H D' φ hr hinj hsp hEF (D.sh L) hsd l.M l.three_le ga hu
    hfix' h2 (v₀ L) (hT.w ▸ hvac)
  have hlam : D.lam ⟨k, hk⟩ = 1 := hT.det _ (h3 ⟨k, hk⟩ hred l.three_le)
  have e := hmu ga hga L hL ⟨k, hk⟩ hred
  rw [hw, hlam, hfix, Units.val_one, _root_.mul_one] at e
  have hne : v₀ L ≠ 0 := fun h0 => by
    have := hvac.2.1
    rw [h0] at this
    simp [ip, haar, haarAt] at this
  have : (mu ga L - 1) • v₀ L = 0 := by rw [sub_smul, one_smul, ← e, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 this).resolve_right hne)
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

theorem _root_.GlobalTheory.T.prod_levelOne_theta_eq_vacuum_theta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : E, IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ x ∈ X.dom, ∀ θ : (Fin g → ℂ) → ℂ, IsTheta1 X bas idx w x L θ → ∃ κ : ℂ, ∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z := by
  first | exact @GlobalTheory.Dict.VacProd.prod_eq_mul_thA | exact GlobalTheory.Dict.VacProd.prod_eq_mul_thA | (intros; apply GlobalTheory.Dict.VacProd.prod_eq_mul_thA <;> assumption)
end

section

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.doubledThetaTestFunction_sesquilinear_heisenberg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ φ₁ φ₂ : TF n g, IsSB φ₁ → IsSB φ₂ → (∀ ψ, IsSB ψ → dbl X bas idx (φ₁ + ψ) φ₂ = dbl X bas idx φ₁ φ₂ + dbl X bas idx ψ φ₂ ∧ dbl X bas idx φ₁ (φ₂ + ψ) = dbl X bas idx φ₁ φ₂ + dbl X bas idx φ₁ ψ) ∧ (∀ a b : ℂ, dbl X bas idx (a • φ₁) (b • φ₂) = (a * conj b) • dbl X bas idx φ₁ φ₂) ∧ ∀ y₁ y₂ : Matrix (Fin n) (Fin r) E, dbl X bas idx (heisG X bas y₁ φ₁) (heisG X bas y₂ φ₂) = heisH (Matrix.fromCols y₁ y₂ * dblT X).toCols₁ (Matrix.fromCols y₁ y₂ * dblT X).toCols₂ (dbl X bas idx φ₁ φ₂) := by
  first | exact @GlobalTheory.SW.DblLin.dbl_lin | exact GlobalTheory.SW.DblLin.dbl_lin | (intros; apply GlobalTheory.SW.DblLin.dbl_lin <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicZakTheta_exists_unique : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ x ∈ C.X.dom, ∀ φ : TF S.rank C.g, SW.IsSB φ → C.IsZak x φ (C.Th x φ) ∧ ∀ f, C.IsZak x φ f → f = C.Th x φ := by
  first | exact @GlobalTheory.Ker.ZakEx.isZak_Th | exact GlobalTheory.Ker.ZakEx.isZak_Th | (intros; apply GlobalTheory.Ker.ZakEx.isZak_Th <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockPolynomialVector_origin_eq_polyDeriv : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ (G : WO S T → ℂ) (θ : (Fin S.rank → Fin C.g → ℂ) → ℂ), Differentiable ℂ θ → (∀ w, IsRealPt w → G w = gaussR C.X C.bas C.idx (C.xB B) (C.zOf (C.xB B) w) * θ (C.zOf (C.xB B) w)) → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.fvec B G Q 0 = polyDeriv (C.toH Q) (letterDir C.X C.hr C.idx) θ 0 := by
  first | exact @GlobalTheory.Ker.FockOrigin.fvec_zero_eq_polyDeriv | exact GlobalTheory.Ker.FockOrigin.fvec_zero_eq_polyDeriv | (intros; apply GlobalTheory.Ker.FockOrigin.fvec_zero_eq_polyDeriv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockPolynomialVector_laws : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ B, C.IsB B → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, ∀ f, C.IsTh f → ∀ Q : MvPolynomial (FVar D T.rank S.rank) ℂ, C.IsTh (pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f Q) ∧ (∀ v, pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f (MvPolynomial.X v * Q) = aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) BS B v (pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f Q)) ∧ pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) BS B f 1 = f ∧ (∀ f', C.IsTh f' → C.fvec B (f + f') Q = C.fvec B f Q + C.fvec B f' Q) ∧ (∀ a : ℂ, C.fvec B (a • f) Q = a • C.fvec B f Q) ∧ ∀ u, IsFinPt u → C.fvec B (C.rho u f) Q = C.rho u (C.fvec B f Q) := by
  first | exact @GlobalTheory.Ker.FockAlg.fock_vec_laws | exact GlobalTheory.Ker.FockAlg.fock_vec_laws | (intros; apply GlobalTheory.Ker.FockAlg.fock_vec_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaInnerProduct_eq_realTorusMean : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ f f', C.IsTh f → C.IsTh f' → ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → (∃ Fd : Set (WR C.X S.rank), IsAddFundamentalDomain (latR C.X S.rank N) Fd volume) ∧ ∀ Fd : Set (WR C.X S.rank), IsAddFundamentalDomain (latR C.X S.rank N) Fd volume → ∀ F : WR C.X S.rank → ℂ, (∀ w, IsRealPt w → f w * conj (f' w) = F (C.realPt w)) → ipO μ 𝓕 f f' = ((volume Fd).toReal : ℂ)⁻¹ * ∫ v in Fd, F v := by
  first | exact @GlobalTheory.Ker.TorusMean.ipO_eq_mean | exact GlobalTheory.Ker.TorusMean.ipO_eq_mean | (intros; apply GlobalTheory.Ker.TorusMean.ipO_eq_mean <;> assumption)
end
