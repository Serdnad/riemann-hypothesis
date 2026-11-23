module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle391
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle675
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle842
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VacuumEntireAndNormalizedJetsAlgebraic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle876
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle596
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1684
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.Proj

variable {p q r : ℕ}

theorem Jpq_eq_diagonal (p q : ℕ) :
    Formalism.UG.Jpq p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem det_Jpq_ne (p q : ℕ) : (Formalism.UG.Jpq p q).det ≠ 0 := by
  rw [Jpq_eq_diagonal, Matrix.det_diagonal]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rcases i with i | i <;> simp

theorem star_det_mul_det (u : UpqT p q) : star (UpqT.mat u).det * (UpqT.mat u).det = 1 := by
  have h := congrArg Matrix.det (GlobalTheory.UpqExpChart.mat_unitary u)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ := det_Jpq_ne p q
  apply mul_left_cancel₀ hJ
  linear_combination h

theorem det_mat_ne (u : UpqT p q) : (UpqT.mat u).det ≠ 0 := by
  intro h
  have := star_det_mul_det u
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem dg_unitary (a₀ : Fin p ⊕ Fin q) (z : ℂ) (hz : star z * z = 1) :
    (dg a₀ z)ᴴ * Formalism.UG.Jpq p q * dg a₀ z = Formalism.UG.Jpq p q := by
  rw [Jpq_eq_diagonal, dg, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = a₀
  · subst h
    simp only [Pi.star_apply, Function.update_self]
    linear_combination (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i) * hz
  · simp [Function.update_of_ne h]

theorem det_sMat (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) : (sMat a₀ u).det = 1 := by
  rw [sMat, Matrix.det_mul, det_dg, mul_inv_cancel₀ (det_mat_ne u)]

theorem sMat_unitary (a₀ : Fin p ⊕ Fin q) (u : UpqT p q) :
    (sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u = Formalism.UG.Jpq p q := by
  have hz : star (UpqT.mat u).det⁻¹ * (UpqT.mat u).det⁻¹ = 1 := by
    rw [star_inv₀, ← mul_inv, star_det_mul_det, inv_one]
  have h1 := GlobalTheory.UpqExpChart.mat_unitary u
  have h2 := dg_unitary a₀ _ hz
  calc _ = (dg a₀ (UpqT.mat u).det⁻¹)ᴴ * ((UpqT.mat u)ᴴ * Formalism.UG.Jpq p q * UpqT.mat u) *
        dg a₀ (UpqT.mat u).det⁻¹ := by
        simp only [sMat, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]

theorem continuous_sMat (a₀ : Fin p ⊕ Fin q) : Continuous (sMat a₀ : UpqT p q → _) := by
  unfold sMat dg
  refine GlobalTheory.UpqExpChart.continuous_mat.matrix_mul (Continuous.matrix_diagonal ?_)
  exact continuous_const.update a₀
    (GlobalTheory.UpqExpChart.continuous_mat.matrix_det.inv₀ det_mat_ne)

theorem sMat_mul (a₀ : Fin p ⊕ Fin q) (u v : UpqT p q) (hu : (UpqT.mat u).det = 1) :
    sMat a₀ (u * v) = UpqT.mat u * sMat a₀ v := by
  have h : UpqT.mat (u * v) = UpqT.mat u * UpqT.mat v := rfl
  rw [sMat, sMat, h, Matrix.det_mul, hu, one_mul, Matrix.mul_assoc]

theorem det_conj {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin r) (A : Matrix ι (Fin r) ℂ)
    (B : Matrix (Fin r) ι ℂ) (hAB : A * B = 1) (S : Matrix ι ι ℂ) : (B * S * A).det = S.det := by
  have h1 : (B * S * A).submatrix e e = B.submatrix e id * S * A.submatrix id e := by
    ext i j
    simp [Matrix.mul_apply]
  have h2 : A.submatrix id e * B.submatrix e id = 1 := by
    rw [Matrix.submatrix_mul_equiv, hAB]
    rfl
  rw [← Matrix.det_submatrix_equiv_self e, h1, Matrix.det_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]

def gl (a₀ : Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin r) ℂ) (B : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1) (u : UpqT p q) : GL (Fin r) ℂ where
  val := B * sMat a₀ u * A
  inv := B * (sMat a₀ u).adjugate * A
  val_inv := by
    calc _ = B * (sMat a₀ u * (A * B) * (sMat a₀ u).adjugate) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, Matrix.mul_adjugate, det_sMat, one_smul, Matrix.mul_one, hBA]
  inv_val := by
    calc _ = B * ((sMat a₀ u).adjugate * (A * B) * sMat a₀ u) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hAB, Matrix.mul_one, Matrix.adjugate_mul, det_sMat, one_smul, Matrix.mul_one, hBA]

section
variable (a₀ : Fin p ⊕ Fin q) (A : Matrix (Fin p ⊕ Fin q) (Fin r) ℂ) (B : Matrix (Fin r) (Fin p ⊕ Fin q) ℂ)
    (hAB : A * B = 1) (hBA : B * A = 1)

theorem gl_val (u : UpqT p q) :
    (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = B * sMat a₀ u * A := rfl

theorem continuous_gl : Continuous (gl a₀ A B hAB hBA) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_const.matrix_mul (continuous_sMat a₀)).matrix_mul continuous_const
  · exact (continuous_const.matrix_mul (continuous_sMat a₀).matrix_adjugate).matrix_mul continuous_const

theorem mul_gl (u : UpqT p q) :
    A * (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = sMat a₀ u * A := by
  rw [gl_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.one_mul]

theorem gl_keeps (H : Matrix (Fin r) (Fin r) ℂ) (hH : Aᴴ * Formalism.UG.Jpq p q * A = -Hᵀ) (u : UpqT p q) :
    (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ)ᵀ * H *
      (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = H := by
  have hm := mul_gl a₀ A B hAB hBA u
  generalize (gl a₀ A B hAB hBA u : Matrix (Fin r) (Fin r) ℂ) = g at hm ⊢
  have h : gᴴ * (-Hᵀ) * g = -Hᵀ := by
    calc _ = (A * g)ᴴ * Formalism.UG.Jpq p q * (A * g) := by
          rw [← hH]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Aᴴ * ((sMat a₀ u)ᴴ * Formalism.UG.Jpq p q * sMat a₀ u) * A := by
          rw [hm]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [sMat_unitary, hH]
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  have h' := congrArg Matrix.transpose h
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at h'
  exact h'

end

theorem exists_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)), IsIdent p q Ψ G x σ A e → ∃ π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G, Continuous π ∧ IsProj p q Ψ G σ A a₀ π ∧ (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ hI
  let B : ∀ ρ, Matrix (Fin r) (Fin (p ρ) ⊕ Fin (q ρ)) ℂ := fun ρ => mat x (σ ρ) * (permM (e ρ))ᵀ
  have hAB : ∀ ρ, A ρ * B ρ = 1 := fun ρ => by
    simp only [B]
    rw [← Matrix.mul_assoc, (hI ρ).2, permM_mul_transpose]
  have hBA : ∀ ρ, B ρ * A ρ = 1 := fun ρ => (Matrix.mul_eq_one_comm_of_equiv (e ρ)).1 (hAB ρ)
  let F : (∀ ρ, UpqT (p ρ) (q ρ)) → κ → GL (Fin r) ℂ :=
    fun b ρ => gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ)
  have hF : ∀ b ρ, F b (σ.symm (σ ρ)) = gl (a₀ ρ) (A ρ) (B ρ) (hAB ρ) (hBA ρ) (b ρ) := fun b ρ => by
    rw [Equiv.symm_apply_apply]
  have hmem : ∀ b, (fun τ => F b (σ.symm τ)) ∈ realSU Ψ G := fun b => by
    rw [DensOne.mem_realSU_iff]
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    simp only [hF]
    exact ⟨gl_keeps _ _ _ _ _ _ (hI ρ).1 _, by rw [gl_val, det_conj (e ρ) _ _ (hAB ρ), det_sMat]⟩
  refine ⟨fun b => ⟨_, hmem b⟩, ?_, ?_, ?_⟩
  · refine Continuous.subtype_mk (continuous_pi fun τ => ?_) _
    exact (continuous_gl _ _ _ _ _).comp (continuous_apply _)
  · intro b ρ
    simp only [hF]
    exact mul_gl _ _ _ _ _ _
  · intro s b₀ hs b
    refine Subtype.ext (funext fun τ => ?_)
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    apply Units.ext
    change ((F (b₀ * b) (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (s.1 (σ ρ) : GL (Fin r) ℂ) * ((F b (σ.symm (σ ρ)) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
    have h1 : ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = B ρ * UpqT.mat (b₀ ρ) * A ρ := by
      rw [Matrix.mul_assoc, hs ρ, ← Matrix.mul_assoc, hBA, Matrix.one_mul]
    have h2 : (UpqT.mat (b₀ ρ)).det = 1 := by
      rw [← det_conj (e ρ) _ _ (hAB ρ), ← h1]
      exact (((DensOne.mem_realSU_iff Ψ G _).1 s.2) (σ ρ)).2
    rw [hF, hF, gl_val, gl_val, h1, Pi.mul_apply, sMat_mul _ _ _ h2]
    calc _ = B ρ * UpqT.mat (b₀ ρ) * (A ρ * B ρ) * sMat (a₀ ρ) (b ρ) * A ρ := by
          rw [hAB]; simp only [Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.CovTop.VolUp.Proj
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

def secMemLeftMul {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (g : H) : Module.End ℂ V ≃+ Module.End ℂ V where
  toFun f := ρ g * f
  invFun f := ρ g⁻¹ * f
  left_inv f := by
    simp only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  right_inv f := by
    simp only [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  map_add' a b := mul_add _ a b

theorem secM_mem_eqvM : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ι : H →* G) (ρ : Representation ℂ H V) (K' : Subgroup G) (x : G) (v : V),
    secM ι ρ K' x v ∈ eqvM ι ρ K' := by
  intro G H V _ _ _ _ ι ρ K' x v
  refine ⟨fun g y => ?_, fun k hk y => ?_⟩
  · change ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * (ι g * y) ∈ K' then ρ h else 0) v
      = ρ g (((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) v)
    have hsum : (∑ᶠ h : H, if (ι h * x)⁻¹ * (ι g * y) ∈ K' then ρ h else 0)
        = ρ g * (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) := by
      rw [← finsum_comp_equiv (Equiv.mulLeft g)]
      have hpt : ∀ h' : H, (fun h : H => if (ι h * x)⁻¹ * (ι g * y) ∈ K' then ρ h else 0)
          ((Equiv.mulLeft g) h') = secMemLeftMul ρ g (if (ι h' * x)⁻¹ * y ∈ K' then ρ h' else 0) := by
        intro h'
        have he : (ι (g * h') * x)⁻¹ * (ι g * y) = (ι h' * x)⁻¹ * y := by
          rw [map_mul]; group
        simp only [Equiv.coe_mulLeft, he]
        change _ = ρ g * _
        split_ifs
        · exact map_mul ρ g h'
        · exact (mul_zero _).symm
      simp_rw [hpt]
      exact (AddEquiv.map_finsum (secMemLeftMul ρ g) _).symm
    rw [hsum, map_smul]
    rfl
  · change ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * (y * k) ∈ K' then ρ h else 0) v
      = ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) v
    have hc : ∀ h : H, ((ι h * x)⁻¹ * (y * k) ∈ K' ↔ (ι h * x)⁻¹ * y ∈ K') := by
      intro h
      rw [← mul_assoc]
      exact Subgroup.mul_mem_cancel_right K' hk
    simp_rw [hc]

end GlobalTheory.BCT.TraceBlocks
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.TraceBlocks

theorem levOp_secM_apply_self : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G), Function.Injective ι → ∀ (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (x * k) = F x) → {q : G ⧸ K' | F q.out ≠ 0}.Finite → ∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G) → {h : H | F (x⁻¹ * ι h * x) ≠ 0}.Finite → ∀ v : V, levOp (rightReg ℂ G V) K K' F LinearMap.id (secM ι ρ K' x v) x = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ((stabCard ι K' x : ℂ))⁻¹ • ∑ᶠ h : H, F (x⁻¹ * ι h * x) • ρ h v := by
  intro G H V _ _ _ _ ι _ ρ K K' F hF hS x _ hT v
  have hout : ∀ y : G, F (y : G ⧸ K').out = F y := by
    intro y
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K' y
    rw [hk, hF _ k.2]
  have hcond : ∀ (q : G ⧸ K') (h : H),
      ((ι h * x)⁻¹ * (x * q.out) ∈ K') ↔ (((x⁻¹ * ι h * x : G) : G ⧸ K') = q) := by
    intro q h
    have e : (ι h * x)⁻¹ * (x * q.out) = (x⁻¹ * ι h * x)⁻¹ * q.out := by group
    rw [e]
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.symm
  have hreg : ∀ (g : G) (φ : G → V) (y : G), rightReg ℂ G V g φ y = φ (y * g) := fun _ _ _ => rfl
  have hsec : ∀ y, secM ι ρ K' x v y =
      ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) v := fun _ => rfl
  rw [GlobalTheory.BCT.LevOpTmul.levOp_apply _ K K' F LinearMap.id hS.toFinset (fun q hq => by simpa using hq)]
  rw [finsum_eq_sum_of_support_subset (f := fun h : H => F (x⁻¹ * ι h * x) • ρ h v) (s := hT.toFinset) (fun h hh => by
    rw [Set.Finite.coe_toFinset]
    intro h0; exact hh (by simp only [h0, zero_smul]))]
  simp only [Pi.smul_apply, Finset.sum_apply, LinearMap.id_apply, hreg, hsec]
  congr 1
  have hin : ∀ q ∈ hS.toFinset, (∑ᶠ h : H, if (ι h * x)⁻¹ * (x * q.out) ∈ K' then ρ h else 0) =
      ∑ h ∈ hT.toFinset, if (((x⁻¹ * ι h * x : G) : G ⧸ K') = q) then ρ h else 0 := by
    intro q hq
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hq
    rw [finsum_eq_sum_of_support_subset (s := hT.toFinset)]
    · exact Finset.sum_congr rfl fun h _ => by simp only [hcond]
    · intro h hh
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hh
      obtain ⟨hc, _⟩ := hh
      rw [Set.Finite.coe_toFinset]
      show _ ≠ _
      rw [hcond] at hc
      rw [← hout, hc]; exact hq
  rw [Finset.sum_congr rfl fun q hq => by rw [hin q hq]]
  simp only [LinearMap.sum_apply, Finset.sum_apply, ite_apply, LinearMap.zero_apply, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h hh => ?_
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hh
  have : ∀ q ∈ hS.toFinset, F q.out • ((stabCard ι K' x : ℂ))⁻¹ • (if (((x⁻¹ * ι h * x : G) : G ⧸ K') = q) then ρ h else 0) v
      = if (((x⁻¹ * ι h * x : G) : G ⧸ K') = q) then ((stabCard ι K' x : ℂ))⁻¹ • F (x⁻¹ * ι h * x) • ρ h v else 0 := by
    intro q _
    split_ifs with e
    · rw [← e, hout, smul_comm]
    · simp only [LinearMap.zero_apply, smul_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  rw [if_pos]
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hout]
  exact hh

end GlobalTheory.BCT.TraceBlocks
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

def leftEqv {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G)
    (ρ : Representation ℂ H V) : Submodule ℂ (G → V) where
  carrier := {φ | ∀ h x, φ (ι h * x) = ρ h (φ x)}
  add_mem' := by
    intro a b ha hb h x
    simp only [Pi.add_apply, ha h x, hb h x, map_add (f := _)]
  zero_mem' := fun _ _ => by simp
  smul_mem' := by
    intro c a ha h x
    simp only [Pi.smul_apply, ha h x, map_smul]

theorem eqvM_eq_inf {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G)
    (ρ : Representation ℂ H V) (K : Subgroup G) :
    eqvM ι ρ K = leftEqv ι ρ ⊓ fixed (rightReg ℂ G V) K := by
  ext φ
  simp only [Submodule.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k => ?_⟩
    funext x
    simpa [rightReg, LinearMap.funLeft] using h2 k k.2 x
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun k hk x => ?_⟩
    have := congrFun (h2 ⟨k, hk⟩) x
    simpa [rightReg, LinearMap.funLeft] using this

theorem levOp_rightReg_mem_eqvM : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G) (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ), (∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) → ∀ φ ∈ eqvM ι ρ K', levOp (rightReg ℂ G V) K K' F LinearMap.id φ ∈ eqvM ι ρ K' := by
  intro G H V _ _ _ _ ι ρ K K' F hF φ hφ
  rw [eqvM_eq_inf] at hφ ⊢
  refine levOp_id_mem_inf_fixed (rightReg ℂ G V) K K' F hF (leftEqv ι ρ) ?_ φ hφ
  intro g v hv h x
  simp only [rightReg, LinearMap.funLeft, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    Function.comp_apply]
  rw [mul_assoc]
  exact hv h (x * g)

end GlobalTheory.BCT.TraceBlocks
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_closedSubscheme_rigidifiedBundle_trivialLocus : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ U), TrivCond A N T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  first | exact @GlobalTheory.TrivLocusLocal.exists_closed_triv_local | exact GlobalTheory.TrivLocusLocal.exists_closed_triv_local | (intros; apply GlobalTheory.TrivLocusLocal.exists_closed_triv_local <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin

theorem _root_.GlobalTheory.T.eigenDecomposition_iff_shiftedProducts_kill_comaximal : ∀ (O T V : Type) [CommRing O] [CommRing T] [AddCommGroup V] [Module T V] (ψ : O →+* Module.End T V) (a : ℕ)
  (τ : Fin a → (O →+* T)), (∀ i j, i ≠ j → Ideal.span (Set.range fun x => τ i x - τ j x) = ⊤) → ∀ v : V,
    ((∃ w : Fin a → V, (∀ i, w i ∈ eigSub ψ (τ i)) ∧ v = ∑ i, w i) ↔
      ∀ c : Fin a → O, (List.ofFn fun i => ψ (c i) - algebraMap T (Module.End T V) (τ i (c i))).prod v = 0) := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.decomp_iff_kill) | (exact GlobalTheory.UPel.HT.LieLin.decomp_iff_kill) | (intros; apply GlobalTheory.UPel.HT.LieLin.decomp_iff_kill  <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.relativelyAcyclic_of_cech_vanishing_all_covers : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (P : LB A.left), (∀ j : ℕ, ¬ NV A P (j + 1)) → GlobalTheory.CxForm.IsRelAcyclic A.hom A.hom P := by
  first | exact @GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV | exact GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV | (intros; apply GlobalTheory.AmpleGen.isRelAcyclic_of_not_NV <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory.BaseVacuum

theorem pullback_basis_theta_eq_F0 : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), StandardLatticesGL3.pullB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') (GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) (B.ω₀ / 2)) z = F0 B.L B.ω₀ (Ix D n n') (phi B n n' z) := by
  intro D cc δ B n n' z
  have hth : GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) (B.ω₀ / 2) = Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) := by
    exact (GlobalTheory.Mem.Col2.JetAlgebraic.thetaZero_periodLattice_eq B _).symm
  simp only [StandardLatticesGL3.pullB, F0, prodFn, hth, GlobalTheory.T.blockVacuum_latticeBasis_coordinate_eq_coordinateEquiv]
  exact Fintype.prod_equiv (ixE D n n') _ _ (fun _ => rfl)

end GlobalTheory.BaseVacuum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.ExpFrame

theorem exists_isFactorAH_frame_of_isExp : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (e : (Fin g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsExp (𝟙 (Sp ℂ)) e → ∀ (M : LB A.left), M.IsLB → ∃ (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), (∀ z, u.ex z = e z) ∧ GlobalTheory.TorusRM.IsFactorAH u Hm χ := by
  intro A _ _ g hA hg e he M hM
  obtain ⟨Λ, hd, hf, hk⟩ := GlobalTheory.ExpKernel.kernel_isFullLattice (Sp ℂ) A g hA hg (𝟙 (Sp ℂ)) e he
  obtain ⟨L₀, u₀, hu₀⟩ := GlobalTheory.exists_holUnif_of_isExp A g e Λ he hd hf hk
  obtain ⟨u, Hm, χ, hu, hAH⟩ := GlobalTheory.exists_isFactorAH_frame_of_unif A hA L₀ g u₀ M hM
  exact ⟨u, Hm, χ, fun z => by rw [hu, hu₀], hAH⟩

end GlobalTheory.ExpFrame
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem _root_.GlobalTheory.T.mumfordBundleIso_of_same_appellHumbert_form : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M M' : LB A.left) (u : HolUnif A M g) (u' : HolUnif A M' g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), M.IsLB → M'.IsLB → u'.ex = u.ex →
    GlobalTheory.TorusRM.IsFactorAH u Hm χ → GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → LBIso (abelian₂ A M) (abelian₂ A M') := by
  first | exact @GlobalTheory.TorusRM.lbIso_lam_of_same_form | exact GlobalTheory.TorusRM.lbIso_lam_of_same_form | (intros; apply GlobalTheory.TorusRM.lbIso_lam_of_same_form <;> assumption)
end
