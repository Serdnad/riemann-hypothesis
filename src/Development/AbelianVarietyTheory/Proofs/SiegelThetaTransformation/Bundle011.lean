module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle008
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledRowTestFunctionProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real


open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
theorem _root_.GlobalTheory.SW.thH_summable_and_inj : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ)
    (φ : Matrix (Fin n) (Fin N) E → ℂ), _root_.GlobalTheory.SW.IsSB φ →
    ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N,
      (∀ z z', Summable fun x => ‖φ x * cexp (2 * π * I * _root_.GlobalTheory.SW.expo Ψ x Z z z')‖) ∧
      ∀ ψ, _root_.GlobalTheory.SW.IsSB ψ →
        (∀ z z', _root_.GlobalTheory.SW.thH Ψ φ Z z z' = _root_.GlobalTheory.SW.thH Ψ ψ Z z z') → φ = ψ := by
  intro E _ _ _ Ψ hΨ n N φ hφ Z hZ
  obtain ⟨hbij, hup, hsurj, hdict, hSB⟩ := _root_.GlobalTheory.SW.thH_eq_thS_dictionary E Ψ hΨ n N
  classical
  have hexp : ∀ (z z' : _root_.GlobalTheory.SW.CM Ψ n N)
      (m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ),
      cexp (2 * π * I * _root_.GlobalTheory.SW.expo Ψ (_root_.GlobalTheory.SW.ofQ m) Z z z') =
        cexp (π * I * ∑ k, (_root_.GlobalTheory.SW.qv (m k) ⬝ᵥ
          (_root_.GlobalTheory.SW.tauOf Ψ Z) *ᵥ _root_.GlobalTheory.SW.qv (m k) +
          2 * _root_.GlobalTheory.SW.qv (m k) ⬝ᵥ (_root_.GlobalTheory.SW.zetaOf Ψ z z') k)) := by
    intro z z' m
    have h := hdict (fun x => if x = _root_.GlobalTheory.SW.ofQ m then 1 else 0) Z z z'
    unfold _root_.GlobalTheory.SW.thH _root_.GlobalTheory.SW.thS at h
    rw [tsum_eq_single (_root_.GlobalTheory.SW.ofQ m), tsum_eq_single m] at h
    · simpa using h
    all_goals (intro b hb; simp [hbij.1.eq_iff, hb])
  refine ⟨fun z z' => ?_, fun ψ hψ hθ => ?_⟩
  · rw [← (Equiv.ofBijective _ hbij).summable_iff]
    have hs := _root_.GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm _ _ (fun m => φ (_root_.GlobalTheory.SW.ofQ m)) ((hSB φ).1 hφ) _ (hup Z hZ)
      (_root_.GlobalTheory.SW.zetaOf Ψ z z')
    refine hs.congr fun m => ?_
    simp only [Function.comp_apply, Equiv.ofBijective_apply, hexp]
  · have h := _root_.GlobalTheory.SW.eq_of_thS_eq _ _ (fun m => φ (_root_.GlobalTheory.SW.ofQ m))
      (fun m => ψ (_root_.GlobalTheory.SW.ofQ m)) ((hSB φ).1 hφ) ((hSB ψ).1 hψ) _ (hup Z hZ)
      (fun ζ => by
        obtain ⟨z, z', rfl⟩ := hsurj ζ
        rw [← hdict, ← hdict]
        exact hθ z z')
    funext x
    obtain ⟨m, rfl⟩ := hbij.2 x
    exact congrFun h m
end

section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.HermComp

variable {N : ℕ}


open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {N : ℕ} in
theorem _root_.GlobalTheory.SW.HermComp.row_rel (g : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℂ)
    (h : gᴴ * Matrix.J (Fin N) ℂ * g = Matrix.J (Fin N) ℂ) :
    g.toBlocks₁₁ * g.toBlocks₂₂ᴴ - g.toBlocks₁₂ * g.toBlocks₂₁ᴴ = 1 ∧
      g.toBlocks₂₂ * g.toBlocks₂₁ᴴ = g.toBlocks₂₁ * g.toBlocks₂₂ᴴ := by
  set J := Matrix.J (Fin N) ℂ
  have hJJ : J * J = -1 := Matrix.J_squared _ _
  have hleft : (-(J * gᴴ * J)) * g = 1 := by
    have : J * gᴴ * J * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
    rw [Matrix.neg_mul, this, h, hJJ, neg_neg]
  have hright : g * (-(J * gᴴ * J)) = 1 := mul_eq_one_comm.mp hleft
  have hgJ : g * J * gᴴ = J := by
    have h1 : g * J * gᴴ * J = -1 := by
      have := congrArg Neg.neg hright
      simpa [Matrix.mul_neg, Matrix.mul_assoc] using this
    calc g * J * gᴴ = g * J * gᴴ * J * (-J) := by
            rw [Matrix.mul_assoc (g * J * gᴴ), Matrix.mul_neg, hJJ, neg_neg, Matrix.mul_one]
      _ = J := by rw [h1, Matrix.neg_mul, Matrix.one_mul, neg_neg]
  rw [← Matrix.fromBlocks_toBlocks g] at hgJ
  simp only [J, Matrix.J, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj] at hgJ
  obtain ⟨-, h12, -, h22⟩ := hgJ
  simp only [Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, zero_add, add_zero,
    Matrix.neg_mul] at h12 h22
  constructor
  · rw [← neg_inj, neg_sub, ← h12]; abel
  · rw [← sub_eq_zero, ← h22]; abel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end GlobalTheory.SW.HermComp

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private theorem inv_denominator_mul_lower_left_cocycle {N : ℕ}
    {A B C D C' D' Z : Matrix (Fin N) (Fin N) ℂ}
    (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hdet0 : (C * Z + D).det ≠ 0)
    (hdet1 : (C' * ((A * Z + B) * (C * Z + D)⁻¹) + D').det ≠ 0) :
    ((C' * ((A * Z + B) * (C * Z + D)⁻¹) + D') * (C * Z + D))⁻¹ * (C' * A + D' * C) =
      (C * Z + D)⁻¹ * ((C' * ((A * Z + B) * (C * Z + D)⁻¹) + D')⁻¹ * C') * (Z * Cᴴ + Dᴴ)⁻¹ +
        (C * Z + D)⁻¹ * C := by
  set W := (A * Z + B) * (C * Z + D)⁻¹ with hW
  have hadj : (Z * Cᴴ + Dᴴ) * W = Z * Aᴴ + Bᴴ :=
    _root_.GlobalTheory.SW.HAct.den'_act h1 h2 h3 h4 hdet0
  have hinv : (Z * Cᴴ + Dᴴ)⁻¹ = A - W * C := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hadj]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h3]
    abel
  have hunit : IsUnit (C' * W + D').det := isUnit_iff_ne_zero.mpr hdet1
  have hC : (C * Z + D)⁻¹ * C = (C * Z + D)⁻¹ * (C' * W + D')⁻¹ * ((C' * W + D') * C) := by
    rw [Matrix.mul_assoc ((C * Z + D)⁻¹), ← Matrix.mul_assoc ((C' * W + D')⁻¹),
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mul]
  rw [hinv, Matrix.mul_inv_rev, hC]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
private theorem matrix_of_apply_row {m r : Type} {α : Type} (f : m → r → α) (k : m) :
    Matrix.of f k = f k := rfl


open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
theorem _root_.GlobalTheory.SW.transH_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (γ γ' : _root_.GlobalTheory.SW.M2 E N), γ ∈ _root_.GlobalTheory.SW.UU E N → γ' ∈ _root_.GlobalTheory.SW.UU E N → (∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n N, _root_.GlobalTheory.SW.hFac Ψ (γ' * γ) Z z z' = _root_.GlobalTheory.SW.hFac Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) (fun τ => Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) (fun τ => Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) * _root_.GlobalTheory.SW.hFac Ψ γ Z z z') ∧ ∀ φ ψ χ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.TransH Ψ γ φ ψ → _root_.GlobalTheory.SW.TransH Ψ γ' ψ χ → _root_.GlobalTheory.SW.TransH Ψ (γ' * γ) φ χ := by
  intro E _ _ _ Ψ n N γ γ' hγ hγ'
  have key : ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, ∀ z z' : _root_.GlobalTheory.SW.CM Ψ n N,
      _root_.GlobalTheory.SW.hFac Ψ (γ' * γ) Z z z' =
        _root_.GlobalTheory.SW.hFac Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z)
          (fun τ => Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k)
          (fun τ => Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) *
        _root_.GlobalTheory.SW.hFac Ψ γ Z z z' := by
    intro Z hZ z z'
    obtain ⟨hτ, hmem, -, hcomp⟩ := (_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
    obtain ⟨-, hden, -⟩ := hcomp γ' hγ'
    have hτ' := ((_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ' hγ').2 _ hmem).1
    unfold _root_.GlobalTheory.SW.hFac
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hlow := (_root_.GlobalTheory.SW.HAct.mul_blocks (E := E) (τ : E →+* ℂ) γ γ').2.2.1
    obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.SW.HAct.blocks (by
      rw [← _root_.GlobalTheory.SW.HAct.map_blocks (E := E) (τ : E →+* ℂ) γ]
      exact _root_.GlobalTheory.SW.HAct.map_mem (τ : E →+* ℂ) hγ)
    have hM := inv_denominator_mul_lower_left_cocycle (C' := (toBlocks₂₁ γ').map (τ : E →+* ℂ))
      (D' := (toBlocks₂₂ γ').map (τ : E →+* ℂ)) (Z := Z τ) h1 h2 h3 h4 (hτ τ).1 (hτ' τ).1
    rw [hden τ, Matrix.det_mul, mul_pow, hlow]
    simp only [_root_.GlobalTheory.SW.hDen, _root_.GlobalTheory.SW.hDen',
      _root_.GlobalTheory.SW.hAct] at hM ⊢
    rw [hM]
    simp only [matrix_of_apply_row, Matrix.add_mulVec, dotProduct_add, Finset.sum_add_distrib,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_add,
      Complex.exp_add]
    ring
  refine ⟨key, fun φ ψ χ hφ hψ Z hZ z z' => ?_⟩
  obtain ⟨-, hmem, -, hcomp⟩ := (_root_.GlobalTheory.SW.unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  obtain ⟨hact, hden, hadj⟩ := hcomp γ' hγ'
  have hvar : (fun τ => Matrix.of fun k =>
        (_root_.GlobalTheory.SW.hDen' Ψ (γ' * γ) Z τ)⁻¹ *ᵥ z τ k) =
      fun τ => Matrix.of fun k =>
        (_root_.GlobalTheory.SW.hDen' Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) τ)⁻¹ *ᵥ
          (Matrix.of fun k => (_root_.GlobalTheory.SW.hDen' Ψ γ Z τ)⁻¹ *ᵥ z τ k) k := by
    funext τ
    congr 1
    funext k
    rw [hadj τ, Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec]
    rfl
  have hvar' : (fun τ => Matrix.of fun k =>
        z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ (γ' * γ) Z τ)⁻¹) =
      fun τ => Matrix.of fun k =>
        (Matrix.of fun k => z' τ k ᵥ* (_root_.GlobalTheory.SW.hDen Ψ γ Z τ)⁻¹) k ᵥ*
          (_root_.GlobalTheory.SW.hDen Ψ γ' (_root_.GlobalTheory.SW.hAct Ψ γ Z) τ)⁻¹ := by
    funext τ
    congr 1
    funext k
    rw [hden τ, Matrix.mul_inv_rev, ← Matrix.vecMul_vecMul]
    rfl
  rw [hact, hvar, hvar', hψ _ hmem, hφ Z hZ z z', key Z hZ z z', mul_assoc]
end

section

open Matrix Complex NumberField GlobalTheory.SW
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.GaussDict

variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

theorem exists_emb_comb_transpose (w : (E →+* ℂ) → ℂ) :
    ∃ c : Fin (Module.finrank ℚ E) → ℂ, ∀ σ : E →+* ℂ,
      ∑ j, σ (Module.finBasis ℚ E j) * c j = w σ := by
  classical
  let e : (E →+* ℂ) ≃ Fin (Module.finrank ℚ E) :=
    Fintype.equivFinOfCardEq (NumberField.Embeddings.card E ℂ)

  let A : Matrix (Fin (Module.finrank ℚ E)) (Fin (Module.finrank ℚ E)) ℂ :=
    Matrix.of fun i j => e.symm i (Module.finBasis ℚ E j)
  have hT : Function.Surjective Aᵀ.mulVec := by
    intro c
    obtain ⟨w', hw'⟩ := GlobalTheory.SW.Dict.exists_emb_comb (E := E) c
    refine ⟨fun i => w' (e.symm i), funext fun j => ?_⟩
    rw [← hw' j]
    exact e.symm.sum_comp (fun σ => σ (Module.finBasis ℚ E j) * w' σ)
  have hA : IsUnit A := by
    have h := Matrix.mulVec_surjective_iff_isUnit.mp hT
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose] at h
    exact (Matrix.isUnit_iff_isUnit_det _).mpr h
  obtain ⟨c, hc⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hA (fun i => w (e.symm i))
  refine ⟨c, fun σ => ?_⟩
  have h := congrFun hc (e σ)
  simpa [Matrix.mulVec, dotProduct, A] using h

theorem exists_coords {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (v v' : Ψ → Fin N → ℂ) :
    ∃ u : QI E N → ℂ, ∀ (τ : Ψ) (a : Fin N),
      ∑ j, τ.1 (Module.finBasis ℚ E j) * u (a, j) = v τ a ∧
      ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (a, j) = v' τ a := by
  classical
  have hc : ∀ σ : E →+* ℂ, σ ∉ Ψ → ComplexEmbedding.conjugate σ ∈ Ψ := fun σ hσ => by
    rw [hΨ, ComplexEmbedding.involutive_conjugate E σ]
    exact hσ

  let w : Fin N → (E →+* ℂ) → ℂ := fun a σ =>
    if h : σ ∈ Ψ then v ⟨σ, h⟩ a else v' ⟨_, hc σ h⟩ a
  choose c hc' using fun a => exists_emb_comb_transpose (w a)
  refine ⟨fun p => c p.1 p.2, fun τ a => ⟨?_, ?_⟩⟩
  · rw [hc' a τ.1]
    simp [w, τ.2]
  · have hn : ComplexEmbedding.conjugate τ.1 ∉ Ψ := (hΨ τ.1).mp τ.2
    have h := hc' a (ComplexEmbedding.conjugate τ.1)
    simp only [ComplexEmbedding.conjugate_coe_eq] at h
    rw [h]
    simp only [w, dif_neg hn]
    exact congrArg (fun t => v' t a) (Subtype.ext (ComplexEmbedding.involutive_conjugate E τ.1))

theorem im_tauOf (Ψ : Finset (E →+* ℂ)) (Z : CM Ψ N N) :
    ((tauOf Ψ Z).map fun t => (t.im : ℂ)) = tauOf Ψ (fun τ => imH (Z τ)) := by
  ext p q
  simp only [Matrix.map_apply, tauOf, Matrix.of_apply]

  rw [Complex.im_eq_sub_conj, map_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [imH, Matrix.smul_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
    Complex.star_def, smul_eq_mul, map_add, map_mul, Complex.conj_conj]
  ring

theorem tauOf_mulVec (Ψ : Finset (E →+* ℂ)) (Y : CM Ψ N N) (u : QI E N → ℂ) (p : QI E N) :
    (tauOf Ψ Y *ᵥ u) p = ∑ τ : Ψ, (τ.1 (Module.finBasis ℚ E p.2) *
      (Y τ *ᵥ fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) p.1 +
      conj (τ.1 (Module.finBasis ℚ E p.2)) *
      ((Y τ)ᵀ *ᵥ fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) p.1) := by
  simp only [Matrix.mulVec, dotProduct, tauOf, Matrix.of_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [add_mul, Finset.sum_add_distrib, Fintype.sum_prod_type, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_ <;> ring

theorem zetaOf_dot (Ψ : Finset (E →+* ℂ)) (z z' : CM Ψ n N) (k : Fin n) (u : QI E N → ℂ) :
    zetaOf Ψ z z' k ⬝ᵥ u = ∑ τ : Ψ,
      (z τ k ⬝ᵥ (fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) +
      z' τ k ⬝ᵥ fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) := by
  simp only [dotProduct, zetaOf, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [add_mul, Finset.sum_add_distrib, Fintype.sum_prod_type, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_ <;> ring

end GlobalTheory.SW.GaussDict

private theorem exists_tauOf_mulVec_eq_zetaOf {E : Type} [Field E] [NumberField E] {Ψ : Finset (E →+* ℂ)}
    (hΨ : IsType Ψ) {m N : ℕ} (Y : CM Ψ N N) (hY : ∀ τ, IsUnit (Y τ)) (z z' : CM Ψ m N)
    (k : Fin m) :
    ∃ u : QI E N → ℂ, tauOf Ψ Y *ᵥ u = zetaOf Ψ z z' k ∧
      zetaOf Ψ z z' k ⬝ᵥ u = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ (Y τ)⁻¹ *ᵥ z τ k := by
  obtain ⟨u, hu⟩ := GlobalTheory.SW.GaussDict.exists_coords hΨ (fun τ => ((Y τ)ᵀ)⁻¹ *ᵥ z' τ k)
    (fun τ => (Y τ)⁻¹ *ᵥ z τ k)
  have h1 : ∀ τ : Ψ, (fun c => ∑ j, τ.1 (Module.finBasis ℚ E j) * u (c, j)) =
      ((Y τ)ᵀ)⁻¹ *ᵥ z' τ k := fun τ => funext fun a => (hu τ a).1
  have h2 : ∀ τ : Ψ, (fun c => ∑ j, conj (τ.1 (Module.finBasis ℚ E j)) * u (c, j)) =
      (Y τ)⁻¹ *ᵥ z τ k := fun τ => funext fun a => (hu τ a).2
  have hY1 : ∀ τ, Y τ * (Y τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hY τ))
  have hY2 : ∀ τ, (Y τ)ᵀ * ((Y τ)ᵀ)⁻¹ = 1 := fun τ => Matrix.mul_nonsing_inv _ (by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).mp (hY τ))
  refine ⟨u, funext fun p => ?_, ?_⟩
  · rw [GlobalTheory.SW.GaussDict.tauOf_mulVec]
    simp only [h1, h2, Matrix.mulVec_mulVec, hY1, hY2, Matrix.one_mulVec, zetaOf]
    exact Finset.sum_congr rfl fun τ _ => by ring
  · rw [GlobalTheory.SW.GaussDict.zetaOf_dot]
    simp only [h1, h2]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Matrix.transpose_nonsing_inv, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      dotProduct_comm]
    ring

theorem GlobalTheory.SW.gauss_form_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), ∀ Z ∈ Hn Ψ N, ∀ (z z' : CM Ψ n N) (k : Fin n), zetaOf Ψ z z' k ⬝ᵥ ((tauOf Ψ Z).map fun t => (t.im : ℂ))⁻¹ *ᵥ zetaOf Ψ z z' k = 2 * ∑ τ : Ψ, z' τ k ⬝ᵥ (imH (Z τ))⁻¹ *ᵥ z τ k := by
  intro E _ _ _ Ψ hΨ n N Z hZ z z' k
  rw [GlobalTheory.SW.GaussDict.im_tauOf]
  have hY : ∀ τ : Ψ, IsUnit (imH (Z τ)) := fun τ =>
    ((show ∀ τ : Ψ, (imH (Z τ)).PosDef from hZ) τ).isUnit
  have hsurj : Function.Surjective (tauOf Ψ fun τ => imH (Z τ)).mulVec := fun ξ => by
    obtain ⟨w, w', hw⟩ := GlobalTheory.SW.Dict.zetaOf_surj (n := 1) hΨ (fun _ => ξ)
    obtain ⟨u, hu, -⟩ := exists_tauOf_mulVec_eq_zetaOf hΨ (fun τ => imH (Z τ)) hY w w' 0
    exact ⟨u, by rw [hu, hw]⟩
  have hU := Matrix.mulVec_surjective_iff_isUnit.mp hsurj
  obtain ⟨u, hu, hdot⟩ := exists_tauOf_mulVec_eq_zetaOf hΨ (fun τ => imH (Z τ)) hY z z' k
  have hinv : (tauOf Ψ fun τ => imH (Z τ))⁻¹ *ᵥ zetaOf Ψ z z' k = u := by
    rw [← hu, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU), Matrix.one_mulVec]
  rw [hinv, hdot]
end

section

open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.siegelTheta_mul_conj_eq_blockTheta : ∀ (κ ι₁ ι₂ : Type) [Fintype κ] [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] (φ₁ : Matrix κ ι₁ ℚ → ℂ) (φ₂ : Matrix κ ι₂ ℚ → ℂ), IsSB φ₁ → IsSB φ₂ → IsSB (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) ∧ ∀ τ₁ ∈ Siegel ι₁, ∀ τ₂ ∈ Siegel ι₂, Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj)) ∈ Siegel (ι₁ ⊕ ι₂) ∧ ∀ (ζ₁ : κ → ι₁ → ℂ) (ζ₂ : κ → ι₂ → ℂ), thS φ₁ τ₁ ζ₁ * conj (thS φ₂ τ₂ ζ₂) = thS (fun m : Matrix κ (ι₁ ⊕ ι₂) ℚ => φ₁ m.toCols₁ * conj (φ₂ (-m.toCols₂))) (Matrix.fromBlocks τ₁ 0 0 (-(τ₂.map conj))) (fun k => Sum.elim (ζ₁ k) (star (ζ₂ k))) := by
  first | exact @GlobalTheory.SW.ThetaProd.thS_mul_conj_thS | exact GlobalTheory.SW.ThetaProd.thS_mul_conj_thS | (intros; apply GlobalTheory.SW.ThetaProd.thS_mul_conj_thS <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.complex_phase_calculus_rootOfUnity : (∀ a b : ℂ, Ph a → Ph b → Ph (a * b)) ∧ (∀ a : ℂ, Ph a → Ph (conj a) ∧ Ph a⁻¹) ∧ (∀ t : ℝ, Ph (t : ℂ)) ∧ (∀ a : ℂ, IsMu a → Ph a ∧ ‖a‖ = 1) ∧ (∀ a : ℂ, Ph a → ‖a‖ = 1 → IsMu a) ∧ (∀ a b : ℂ, IsMu a → IsMu b → IsMu (a * b) ∧ IsMu a⁻¹ ∧ IsMu (conj a)) ∧ (∀ (a : ℂ) (k : ℕ), 0 < k → (IsMu (a ^ k) → IsMu a) ∧ (Ph (a ^ k) → Ph a)) ∧ (∀ q : ℚ, IsMu (cexp (π * I * (q : ℂ)))) ∧ ∀ a b : ℂ, b ≠ 0 → Ph b → Ph (a * b) → Ph a := by
  first | exact @GlobalTheory.Phase.Calc.calculus | exact GlobalTheory.Phase.Calc.calculus | (intros; apply GlobalTheory.Phase.Calc.calculus <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.isZeroOrPosMulRootOfUnity_finite_gaussSum : ∀ (M : Type) [AddCommGroup M] [Fintype M] (f : M → ℂ), Quad ⊤ f → Ph (∑ x, f x) := by
  first | exact @GlobalTheory.Phase.GaussSum.ph_sum | exact GlobalTheory.Phase.GaussSum.ph_sum | (intros; apply GlobalTheory.Phase.GaussSum.ph_sum <;> assumption)
end

section

open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

theorem _root_.GlobalTheory.T.doubledRowTestFunction_properties : ∀ (n g : ℕ) (φ : Matrix (Fin n) (Fin g) ℚ → ℂ), (PV φ → PV (dup φ)) ∧ (φ ≠ 0 → dup φ ≠ 0) ∧ (IsSB φ → IsSB (dup φ)) ∧ (∀ u : ℂ, dup (u • φ) = u ^ 2 • dup φ) ∧ ∀ τ ∈ Siegel (Fin g), blk n τ ∈ Siegel (Fin n × Fin g) ∧ (IsSB φ → ∀ ζ : Fin 2 → Fin n × Fin g → ℂ, thS (dup φ) (blk n τ) ζ = thS φ τ (fun k i => ζ 0 (k, i)) * thS φ τ (fun k i => ζ 1 (k, i))) ∧ ((blk n τ).map fun z => (z.im : ℂ))⁻¹ = blk n ((τ.map fun z => (z.im : ℂ))⁻¹) := by
  first | exact @GlobalTheory.Phase.Doubling.doubling | exact GlobalTheory.Phase.Doubling.doubling | (intros; apply GlobalTheory.Phase.Doubling.doubling <;> assumption)
end
