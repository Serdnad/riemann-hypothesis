module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Statements
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLeviMatrices
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

section Transport

variable {h : HermitianForm F E W}

theorem sesq_unitary_smul (g : h.unitaryGroup) (x y : W) :
    h.toSesq (g • x) (g • y) = h.toSesq x y :=
  g.2 x y

theorem unitary_smul_scalar_smul (g : h.unitaryGroup) (a : E) (x : W) : g • (a • x) = a • (g • x) :=
  map_smul (g : W ≃ₗ[E] W) a x

theorem mem_inv_smul_iff {g : h.unitaryGroup} {La : AddSubgroup W} {x : W} :
    x ∈ g⁻¹ • La ↔ g • x ∈ La := by
  change x ∈ ((g⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) • La ↔ _
  rw [AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem lineCoeffs_inv_smul (g : h.unitaryGroup) (La : AddSubgroup W) (x : W) :
    lineCoeffs (E := E) (g⁻¹ • La) x = lineCoeffs (E := E) La (g • x) := by
  ext a
  change a • x ∈ g⁻¹ • La ↔ a • (g • x) ∈ La
  rw [mem_inv_smul_iff, unitary_smul_scalar_smul]

theorem dualLattice_inv_smul (g : h.unitaryGroup) (La : AddSubgroup W) :
    dualLattice h (g⁻¹ • La) = g⁻¹ • dualLattice h La := by
  ext y
  rw [mem_inv_smul_iff]
  change (∀ x ∈ g⁻¹ • La, h.toSesq y x ∈ integralClosure ℤ E) ↔
    ∀ x ∈ La, h.toSesq (g • y) x ∈ integralClosure ℤ E
  constructor
  · intro hy x hx
    have hx' : g⁻¹ • x ∈ g⁻¹ • La := by rw [mem_inv_smul_iff, smul_inv_smul]; exact hx
    have := hy _ hx'
    rwa [← sesq_unitary_smul g, smul_inv_smul] at this
  · intro hy x hx
    rw [mem_inv_smul_iff] at hx
    rw [← sesq_unitary_smul g]
    exact hy _ hx

theorem isDIntegral_inv_smul (g : h.unitaryGroup) {D : ℕ} {La : AddSubgroup W}
    (hLa : IsDIntegral h D La) : IsDIntegral h D (g⁻¹ • La) := by
  set γ : W ≃ₗ[E] W := ((g⁻¹ : h.unitaryGroup) : W ≃ₗ[E] W) with hγ
  have hinj : Function.Injective (DistribMulAction.toAddMonoidEnd (W ≃ₗ[E] W) W γ) :=
    fun x y hxy => γ.injective hxy
  have hrel : (g⁻¹ • La).relIndex (dualLattice h (g⁻¹ • La)) =
      La.relIndex (dualLattice h La) := by
    rw [dualLattice_inv_smul]
    change (γ • La).relIndex (γ • dualLattice h La) = _
    rw [AddSubgroup.pointwise_smul_def, AddSubgroup.pointwise_smul_def]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a x hx
    rw [mem_inv_smul_iff] at hx ⊢
    rw [unitary_smul_scalar_smul]
    exact hLa.isLattice.smul_mem a _ hx
  · have hfg := hLa.isLattice.fg
    change (γ • La).FG
    rw [AddSubgroup.pointwise_smul_def]
    rw [AddSubgroup.fg_iff_exists_fin_addMonoidHom] at hfg ⊢
    obtain ⟨k, f, hf⟩ := hfg
    exact ⟨k, γ.toLinearMap.toAddMonoidHom.comp f, by
      rw [AddMonoidHom.range_comp, hf]
      rfl⟩
  · have hset : ((g⁻¹ • La : AddSubgroup W) : Set W) =
        γ.toLinearMap '' (La : Set W) := by
      ext y
      constructor
      · intro hy
        exact ⟨g • y, mem_inv_smul_iff.1 hy, inv_smul_smul g y⟩
      · rintro ⟨x, hx, rfl⟩
        change g⁻¹ • x ∈ g⁻¹ • La
        rw [mem_inv_smul_iff, smul_inv_smul]
        exact hx
    rw [hset, Submodule.span_image, hLa.isLattice.span_eq_top, Submodule.map_top,
      LinearMap.range_eq_top]
    exact LinearEquiv.surjective _
  · intro x hx y hy
    rw [mem_inv_smul_iff] at hx hy
    rw [← sesq_unitary_smul g]
    exact hLa.integral _ hx _ hy
  · rw [hrel]
    exact hLa.index_ne_zero
  · rw [hrel]
    exact hLa.index_le

end Transport

theorem AdaptedReduction.proof (h : HermitianForm F E W) [FiniteDimensional E W]
    (h₁ : HyperbolicPairTransitive.Statement h) (h₂ : LineNormalForm.Statement h)
    (h₃ : ComplementLattice.Statement h) : AdaptedReduction.Statement h := by
  intro v₀ w₀ hp h' hh' D
  obtain ⟨KK, hKK, n, hn, H⟩ := h₂ D
  obtain ⟨D', hD'⟩ := h₃ v₀ w₀ hp h' hh' D n hn
  refine ⟨KK, hKK, n, D', hn, fun La l hLa hl => ?_⟩
  obtain ⟨v, w, hvl, hvw, hK, hdec⟩ := H La l hLa hl
  obtain ⟨g, hgv, hgw⟩ := h₁ v₀ w₀ v w hp hvw
  have hI : lineCoeffs (E := E) (g⁻¹ • La) v₀ = lineCoeffs (E := E) La v := by
    rw [lineCoeffs_inv_smul, hgv]
  have hJ : lineCoeffs (E := E) (g⁻¹ • La) w₀ = lineCoeffs (E := E) La w := by
    rw [lineCoeffs_inv_smul, hgw]
  have hwv : h.toSesq w v = 1 := by
    rw [← h.isSymm.eq v w, hvw.2.2, map_one]
  have hsplit : ∀ x ∈ g⁻¹ • La, ∃ a ∈ lineCoeffs (E := E) (g⁻¹ • La) v₀,
      ∃ b ∈ lineCoeffs (E := E) (g⁻¹ • La) w₀,
        n • x - a • v₀ - b • w₀ ∈ hypComplement h v₀ w₀ := by
    intro x hx
    rw [mem_inv_smul_iff] at hx
    obtain ⟨ha, hb⟩ := hdec _ hx
    refine ⟨(n : E) * h.toSesq w (g • x), by rw [hI]; exact ha,
      (n : E) * h.toSesq v (g • x), by rw [hJ]; exact hb, ?_⟩
    rw [mem_hypComplement, ← sesq_unitary_smul g v₀, ← sesq_unitary_smul g w₀, hgv, hgw,
      ← Nat.cast_smul_eq_nsmul E, smul_sub, smul_sub, unitary_smul_scalar_smul, unitary_smul_scalar_smul,
      unitary_smul_scalar_smul, hgv, hgw]
    simp only [map_sub, map_smul, smul_eq_mul, hvw.1, hvw.2.1, hvw.2.2, hwv]
    constructor <;> ring
  refine ⟨g, g⁻¹ • La, smul_inv_smul g La, hgv ▸ hvl, ?_, hsplit,
    hD' _ (isDIntegral_inv_smul g hLa) hsplit⟩
  rw [hI, hJ]
  exact hK

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ParabolicDecomposition.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : KTransitive.Statement ι) (h₂ : HermAtPlace.Statement h v)
    (h₃ : GramAtData.Statement h v) (h₄ : ArchInvariant.Statement h v)
    (h₅ : VecAtNeZero.Statement v) : ParabolicDecomposition.Statement h v := by
  intro M x₀ hx₀ hiso g
  have hz : ∀ w, vecAt v x₀ w ≠ 0 := h₅ x₀ hx₀
  have hzi : ∀ w, star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 := fun w => by
    rw [← h₂, hiso, map_zero]
  have hzi' : ∀ w, star (invApply g (vecAt v x₀) w) ⬝ᵥ
      (gramAt h v w *ᵥ invApply g (vecAt v x₀) w) = 0 := fun w => by
    rw [h₄, hzi]

  have hginv : ∀ w, (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      ((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) := fun w => rfl
  have hz' : ∀ w, invApply g (vecAt v x₀) w ≠ 0 := by
    intro w hw
    apply hz w
    have e : ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ invApply g (vecAt v x₀) w =
        vecAt v x₀ w := by
      rw [invApply, hginv, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← e, hw, Matrix.mulVec_zero]
  have hmaj : ∀ w, IsMajorantOf (gramAt h v w) (M.P w) := fun w =>
    ⟨M.posDef w, (h₃ w).1, (h₃ w).2, M.siegel w⟩
  choose k hkH hkP c hc using fun w =>
    h₁ _ _ (hmaj w) _ _ (hz w) (hz' w) (hzi w) (hzi' w)
  have hkA : k ∈ archUnitary h v := (Subgroup.mem_pi _).2 fun w _ => hkH w
  set kk : archUnitary h v := ⟨k, hkA⟩ with hkk
  have hkS : kk ∈ M.stab := by
    rw [Majorant.stab, Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_pi _).2 fun w _ => hkP w
  refine ⟨g * kk⁻¹, kk, hkS, by group, fun w => ⟨(c w)⁻¹, ?_⟩⟩
  have hcw : c w ≠ 0 := by
    intro h0
    apply hz' w
    have e := congrArg (fun y => (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ y) (hc w)
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, h0, zero_smul, Matrix.mulVec_zero] at e
    exact e

  have hk : (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      (c w)⁻¹ • invApply g (vecAt v x₀) w := by
    have e := congrArg (fun y => (c w)⁻¹ • ((((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ y)) (hc w)
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hcw, one_smul] at e
    exact e.symm
  have hp : (((g * kk⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) * (((k w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) := rfl
  rw [hp, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_smul, invApply, hginv, Matrix.mulVec_mulVec,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def colMat (v : Basis ι E W) {κ : Type*} (u : κ → W) (w : InfinitePlace E) : Matrix ι κ ℂ :=
  Matrix.of fun i k => vecAt v (u k) w i

theorem vecAt_add (v : Basis ι E W) (x y : W) (w : InfinitePlace E) :
    vecAt v (x + y) w = vecAt v x w + vecAt v y w := by
  funext i; simp [vecAt]

theorem vecAt_smul (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by
  funext i; simp [vecAt]

theorem vecAt_basis (v : Basis ι E W) (i : ι) (w : InfinitePlace E) :
    vecAt v (v i) w = Pi.single i 1 := by
  funext j; simp [vecAt, Finsupp.single_apply, Pi.single_apply, eq_comm]

theorem vecAt_sum_smul (v : Basis ι E W) {κ : Type*} [Fintype κ] (c : κ → E) (u : κ → W)
    (w : InfinitePlace E) :
    vecAt v (∑ k, c k • u k) w = colMat v u w *ᵥ fun k => w.embedding (c k) := by
  funext i

  simp [vecAt, colMat, mulVec, dotProduct, map_sum, mul_comm]

theorem vecAt_coe {W' : Submodule E W} {n : ℕ} (v : Basis ι E W) (v' : Basis (Fin n) E W') (x : W')
    (w : InfinitePlace E) :
    vecAt v (x : W) w = colMat v (fun k => (v' k : W)) w *ᵥ vecAt v' x w := by
  conv_lhs => rw [← v'.sum_repr x]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul]
  exact vecAt_sum_smul v _ _ w

theorem conjTranspose_mulVec_colMat (v : Basis ι E W) {κ : Type*} [Fintype κ] (u : κ → W)
    (w : InfinitePlace E) (z : ι → ℂ) (k : κ) :
    ((colMat v u w)ᴴ *ᵥ z) k = star (vecAt v (u k) w) ⬝ᵥ z := rfl

theorem conjT_eq {m n : Type*} (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
  ext i j
  simp [conjTranspose_apply]

theorem archEmbed_apply (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (w : InfinitePlace E) :
    (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
  rw [← unitaryGroupEquivMatrix_apply]
  rfl

theorem map_toMatrix_mulVec_vecAt (v : Basis ι E W) (f : W →ₗ[E] W) (x : W)
    (w : InfinitePlace E) :
    (LinearMap.toMatrix v v f).map w.embedding *ᵥ vecAt v x w = vecAt v (f x) w := by
  funext i
  change _ = w.embedding (v.repr (f x) i)
  rw [← LinearMap.toMatrix_mulVec_repr v v, RingHom.map_mulVec]
  rfl

variable {h : HermitianForm F E W} {x₀ w₀ : W} {n : ℕ}

theorem gramAt_complement (v : Basis ι E W) (h' : HermitianForm F E (hypComplement h x₀ w₀))
    (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y) (v' : Basis (Fin n) E (hypComplement h x₀ w₀))
    (w : InfinitePlace E) :
    gramAt h' v' w = (colMat v (fun k => (v' k : W)) w)ᴴ * gramAt h v w *
      colMat v (fun k => (v' k : W)) w := by
  ext k l
  have e := sesq_mul (gramAt h v w) (colMat v (fun k => (v' k : W)) w)
    (colMat v (fun k => (v' k : W)) w) (Pi.single k 1) (Pi.single l 1)
  rw [← vecAt_basis v' k w, ← vecAt_basis v' l w, ← vecAt_coe, ← vecAt_coe,
    ← HermAtPlace.proof, ← hh', vecAt_basis, vecAt_basis] at e
  change w.embedding (h'.toSesq (v' k) (v' l)) = _
  rw [← e]
  simp [dotProduct, Pi.single_apply]

theorem frame (v : Basis ι E W) (hp : IsHyperbolicPair h x₀ w₀)
    (h' : HermitianForm F E (hypComplement h x₀ w₀)) (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y)
    (v' : Basis (Fin n) E (hypComplement h x₀ w₀)) (w : InfinitePlace E) :
    (gramAt h v w)ᴴ = gramAt h v w ∧
    IsUnit ((colMat v (fun k => (v' k : W)) w)ᴴ * gramAt h v w *
      colMat v (fun k => (v' k : W)) w).det ∧
    (colMat v (fun k => (v' k : W)) w)ᴴ *ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 ∧
    (colMat v (fun k => (v' k : W)) w)ᴴ *ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 ∧
    star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 ∧
    star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 ∧
    star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 1 ∧
    ∀ z, ∃ (a b : ℂ) (c : Fin n → ℂ), z = a • vecAt v x₀ w + b • vecAt v w₀ w +
      colMat v (fun k => (v' k : W)) w *ᵥ c := by
  refine ⟨(GramAtData.proof h v w).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← gramAt_complement v h' hh' v' w]
    exact (GramAtData.proof h' v' w).2
  · funext k
    rw [conjTranspose_mulVec_colMat, ← HermAtPlace.proof, Pi.zero_apply,
      ComplementExtension.toSesq_swap_eq_zero (mem_hypComplement.1 (v' k).2).1, map_zero]
  · funext k
    rw [conjTranspose_mulVec_colMat, ← HermAtPlace.proof, Pi.zero_apply,
      ComplementExtension.toSesq_swap_eq_zero (mem_hypComplement.1 (v' k).2).2, map_zero]
  · rw [← HermAtPlace.proof, hp.1, map_zero]
  · rw [← HermAtPlace.proof, hp.2.1, map_zero]
  · rw [← HermAtPlace.proof, hp.2.2, map_one]
  · have hx : ∀ x : W, vecAt v x w = w.embedding (h.toSesq w₀ x) • vecAt v x₀ w +
        w.embedding (h.toSesq x₀ x) • vecAt v w₀ w +
        colMat v (fun k => (v' k : W)) w *ᵥ vecAt v' (ComplementExtension.proj hp x) w := by
      intro x
      conv_lhs => rw [← ComplementExtension.split hp x]
      rw [vecAt_add, vecAt_add, vecAt_smul, vecAt_smul, vecAt_coe v v']
      abel
    intro z
    have hz : z = ∑ i, z i • vecAt v (v i) w := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, vecAt_basis, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine ⟨∑ i, z i * w.embedding (h.toSesq w₀ (v i)), ∑ i, z i * w.embedding (h.toSesq x₀ (v i)),
      ∑ i, z i • vecAt v' (ComplementExtension.proj hp (v i)) w, ?_⟩
    have hx' : ∀ i, vecAt v (v i) w = _ := fun i => hx (v i)
    conv_lhs => rw [hz]
    simp only [hx', smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul, mulVec_sum,
      mulVec_smul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
end
