module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle147
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.SecondCapelliMinorLevel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapR
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle132
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

private theorem iotaLev_one_eq_blk3 (ρ : ℕ) (g : B.Mat k ρ) :
    ιLev k 1 ρ g = U.blk3 (j := 1) 1 0 0 0 g 0 0 0 1 := by
  ext p q
  obtain ⟨x, rfl⟩ := (U.eB k 1 ρ).surjective p
  obtain ⟨y, rfl⟩ := (U.eB k 1 ρ).surjective q
  rw [Ux3.block3_apply]
  have vX : ∀ x : Fin 1, ((U.eB k 1 ρ) (Sum.inl (Sum.inl x))).val = 0 := fun x => by
    simp [U.eB]
  have vV : ∀ v : Fin (2 * ρ + k + 1), ((U.eB k 1 ρ) (Sum.inl (Sum.inr v))).val = 1 + v.val := fun v => by
    simp [U.eB]
  have vS : ∀ b : Fin 1, ((U.eB k 1 ρ) (Sum.inr b)).val = 2 * ρ + k + 2 := fun b => by
    simp [U.eB] <;> omega
  rcases x with (x | x) | x <;> rcases y with (y | y) | y <;>
    simp only [Formalism.QuantumDeterminants.ιLev, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, Matrix.one_apply, vX, vV, vS, Equiv.apply_eq_iff_eq,
      Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | (congr <;> (try apply Fin.ext) <;> simp [vV])

theorem lev_mMap (ρ : ℕ) (g g' : B.Mat k ρ) (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) :
    ιLev k 1 ρ g * U.mMap k 1 ρ Z γ * ιLev k 1 ρ g' = U.mMap k 1 ρ Z (g * γ * g') := by
  rw [iotaLev_one_eq_blk3, iotaLev_one_eq_blk3]
  simp only [U.mMap]
  rw [Ux5.block3_mul_blocks, Ux5.block3_mul_blocks]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add]

theorem sgs_alg (ρ : ℕ) (h0 y h0' y' : B.Mat k ρ) (hh0 : IsUnit h0.det) (hy : IsUnit y.det) (hh0' : IsUnit h0'.det)
    (hy' : IsUnit y'.det) (a a' : B.Mat k (1 + ρ)) (Z : Matrix (Fin 1) (Fin 1) ℂ) (γ : B.Mat k ρ) :
    (ιLev k 1 ρ h0)⁻¹ * (a * ιLev k 1 ρ y)⁻¹ * U.mMap k 1 ρ Z γ * (a' * ιLev k 1 ρ y') * ιLev k 1 ρ h0' =
      ((ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0))⁻¹ *
        U.mMap k 1 ρ Z ((y * h0)⁻¹ * γ * (y' * h0')) * ((ιLev k 1 ρ (y' * h0'))⁻¹ * a' * ιLev k 1 ρ (y' * h0')) := by
  have hL0 := PI.QnLevBasicsW.level_group_homomorphism
  have hL := hL0
  unfold Formalism.QuantumDeterminants.LevHom at hL
  have ιmul : ∀ g h : B.Mat k ρ, ιLev k 1 ρ (g * h) = ιLev k 1 ρ g * ιLev k 1 ρ h := (hL k 1 ρ).2
  have ιone : ιLev k 1 ρ (1 : B.Mat k ρ) = 1 := (hL k 1 ρ).1
  have ιinv : ∀ g : B.Mat k ρ, IsUnit g.det → (ιLev k 1 ρ g)⁻¹ = ιLev k 1 ρ g⁻¹ :=
    fun g hg => PIQnLT.ιLev_inv hL0 g hg
  have hW : IsUnit (y * h0).det := by
    rw [Matrix.det_mul]
    exact hy.mul hh0
  have hW' : IsUnit (y' * h0').det := by
    rw [Matrix.det_mul]
    exact hy'.mul hh0'
  have hW1 : ∀ X, ιLev k 1 ρ (y * h0) * (ιLev k 1 ρ (y * h0)⁻¹ * X) = X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_nonsing_inv _ hW, ιone, one_mul]
  have hW2 : ∀ X, ιLev k 1 ρ (y' * h0') * (ιLev k 1 ρ (y' * h0')⁻¹ * X) = X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_nonsing_inv _ hW', ιone, one_mul]
  have hLw : ∀ X, ιLev k 1 ρ h0⁻¹ * (ιLev k 1 ρ y⁻¹ * X) = ιLev k 1 ρ (y * h0)⁻¹ * X := by
    intro X
    rw [← mul_assoc, ← ιmul, Matrix.mul_inv_rev]
  have hRw : ιLev k 1 ρ y' * ιLev k 1 ρ h0' = ιLev k 1 ρ (y' * h0') := (ιmul _ _).symm
  rw [Matrix.mul_inv_rev a, ιinv _ hh0, ιinv _ hy, ιinv _ hW, ιinv _ hW', ← lev_mMap]
  rw [Matrix.mul_inv_rev (ιLev k 1 ρ (y * h0)⁻¹ * a) (ιLev k 1 ρ (y * h0)),
    Matrix.mul_inv_rev (ιLev k 1 ρ (y * h0)⁻¹) a, ιinv _ hW, ιinv _ (Matrix.isUnit_nonsing_inv_det _ hW),
    Matrix.nonsing_inv_nonsing_inv _ hW]
  simp only [mul_assoc]
  rw [hLw, hRw, hW1, hW2]

theorem psi_Qm (ρ : ℕ) {z0 : Fin (2 * ρ + k + 1) → ℂ} (hz0 : inWb k ρ z0) {a : Mt k (1 + ρ)} {y : Mt k ρ}
    (ha : Matrix.of a ∈ Nset k (1 + ρ)) (hy : Matrix.of y ∈ Nset k ρ) :
    psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd (Matrix.of (Qm ρ (a, y))) =
      psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd (D.castM (Nat.add_comm 1 ρ) (Matrix.of a)) *
        psi k ρ z0 cStd (Matrix.of y) := by
  show psi k (ρ + 1) (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z0)) cStd
      (D.castM (Nat.add_comm 1 ρ) (Matrix.of a * ιLev k 1 ρ (Matrix.of y))) = _
  rw [psi_castM, psi_castM, Qx4.psi_mul (Qx4.lift_inWb hz0) ha (B2x6.lev_n hy), Qx4.psi_lev]

theorem psi_conjLev (ρ : ℕ) {z0 : Fin (2 * ρ + k + 1) → ℂ} (hz0 : inWb k ρ z0) {a : B.Mat k (1 + ρ)}
    {y h0 : B.Mat k ρ} (ha : a ∈ Nset k (1 + ρ)) (hy : y ∈ Nset k ρ) (hh0 : h0 ∈ UWset k ρ z0) :
    psi k (1 + ρ) (liftVec k 1 ρ z0) cStd ((ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0)) =
      psi k (1 + ρ) (liftVec k 1 ρ z0) cStd a := by
  have hz1 := Qx4.lift_inWb hz0
  have hyN : ιLev k 1 ρ y ∈ Nset k (1 + ρ) := B2x6.lev_n hy
  have hhW : ιLev k 1 ρ h0 ∈ UWset k (1 + ρ) (liftVec k 1 ρ z0) := Dx2.Tower.lev_UW 1 ρ z0 h0 hh0
  have hu : (ιLev k 1 ρ y)⁻¹ * a * ιLev k 1 ρ y ∈ Nset k (1 + ρ) :=
    WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv hyN) ha) hyN
  have e : (ιLev k 1 ρ (y * h0))⁻¹ * a * ιLev k 1 ρ (y * h0) =
      (ιLev k 1 ρ h0)⁻¹ * ((ιLev k 1 ρ y)⁻¹ * a * ιLev k 1 ρ y) * ιLev k 1 ρ h0 := by
    rw [Dx2.Tower.lev_mul, Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
  rw [e, Qx4.psi_conjW' hz1 hhW hu, Qx4.psi_conjN' hz1 hyN ha]

theorem heis_meas_conj_inv (ρ : ℕ) {g : B.Mat k ρ} (hg : g ∈ B.GV k ρ) :
    (B2.μHeis k ρ).map (conjM ((ιLev k 1 ρ g)⁻¹)) = B2.μHeis k ρ := by
  have hu : IsUnit g.det := HermitianFormFactor.UH_unit (Ux3.hpk_det k ρ) hg
  have hgi : g⁻¹ ∈ B.GV k ρ := HermitianFormFactor.UH_inv (Ux3.hpk_det k ρ) hg
  have h := Formalism.FourierDecayAlt.P.heisenberg_levi_conjugation_measure k ρ g⁻¹ hgi
  rwa [LongWeylElement.lev_inv _ hu] at h

end Formalism.FourierDecayAlt.P.PBH
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def rowsR (i : Fin (k + 1)) : Fin (r + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < r + i.val then j.val else j.val + 1, by have := j.isLt; have := i.isLt; split_ifs <;> omega⟩

def ginvH (g : Q.Mx k r) : Q.Mx k r := Hpk k r * gᴴ * Hpk k r

def colR (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1))
    (q : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h : q.val < r then ginvH k r g *ᵥ bvec (eI k r ⟨r - 1 - q.val, by omega⟩)
  else if h2 : q.val = r then ginvH k r g *ᵥ z
  else bvec (J ⟨q.val - r - 1, by have := q.isLt; omega⟩)

def beJ (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1)) : ℂ :=
  (Matrix.of fun p q => colR k r z g J q p).det


open Classical in
def jSetR : Finset (Fin (r + k) → Fin (2 * r + k + 1)) := Finset.univ.filter fun J => StrictMono J

def rhatOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ i : Fin (k + 1), ∑ J ∈ jSetR k r,
    (((-1 : ℂ) ^ (i : ℕ)) * herm (Hpk k r) (bvec (wI k r i)) z' * beJ k r z g J) •
      qminorOp (Q.EH k r) (rowsR k r i) J (Q.uC k r 0 Y) f g

end defs

def JDRRadP : Prop :=
  ∀ k r : ℕ, ∃ ε : ℂ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      Q.resG k r (Fin.last r) (fun x => ε • rhatOp k r z z' Y J x) c g = rhGrp k r z z' Y (Q.resG k r (Fin.last r) J) c g

def JDRRealInvP : Prop :=
  ∀ (ε : ℂ) (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
        ∀ (U : Set (Q.Mx S.G.k S.G.r)) (F : Q.Mx S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsOpen U →
          Q.SmoothLev S.G.k S.G.r 0 U F → ∀ g ∈ Q.Glev S.G.k S.G.r 0 ∩ U,
            B.opApply Θ F g = ε • rhatOp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) F g

private theorem isDom_OmP_levTower_base {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f) :
    Q.IsDom S.G.k S.G.r (T v).base.z (T v).base.z' 0 (OmP S T v) := by
  refine ⟨?_, ?_⟩
  · have hD : ∀ l, Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Dmin S.G.k S.G.r (T v).base.z (T v).base.z' g l := by
      intro l
      unfold Formalism.QuantumDeterminants.Dmin Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    have hG : Continuous fun g : Matrix (Fin (2 * S.G.r + S.G.k + 1)) (Fin (2 * S.G.r + S.G.k + 1)) ℂ =>
        Formalism.QuantumDeterminants.Gf S.G.k S.G.r (T v).base.z (T v).base.z' g := by
      unfold Formalism.QuantumDeterminants.Gf
      exact (Complex.continuous_normSq.comp (hD _)).sub
        (continuous_const.mul (Complex.continuous_normSq.comp (hD _)))
    unfold OmP
    rw [Set.setOf_and, Set.setOf_forall]
    exact (isOpen_lt continuous_const hG).inter
      (isOpen_iInter_of_finite fun a => isOpen_ne_fun (hD _) continuous_const)
  · rintro g ⟨-, hgD⟩ s ⟨h, hh, m, hm, rfl⟩ s' ⟨h', hh', m', hm', rfl⟩
    have hs : h * m ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z := ⟨h, hh, m, hm.1, rfl⟩
    have hs' : h' * m' ∈ Formalism.QuantumDeterminants.Sset S.G.k S.G.r (T v).base.z' := ⟨h', hh', m', hm'.1, rfl⟩
    refine ⟨?_, fun a => ?_⟩
    · rw [Formalism.QuantumDeterminants.gInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.1
    · rw [Formalism.QuantumDeterminants.dInv _ _ _ _ (T v).base.z_mem (T v).base.z'_mem _ hs _ hs']
      exact hgD.2 a

private theorem w1_mem_UH_Hpk_of_ne_zero {k r : ℕ} (l : Fin r) (x : ℂ) (hx : x ≠ 0) :
    Q.w1 k r l x ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  have hl := l.isLt
  have hes : eI k r l ≠ esI k r l := by
    simp only [eI, esI, ne_eq, Fin.ext_iff]
    omega
  have hcol : ∀ j q, Q.w1 k r l x j q =
      if j = (if q = eI k r l then esI k r l else if q = esI k r l then eI k r l else q) then
        (if q = eI k r l then x else if q = esI k r l then (star x)⁻¹ else 1) else 0 := by
    intro j q
    simp only [Q.w1]
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
      by_cases hj1 : j = eI k r l <;> by_cases hj2 : j = esI k r l <;> simp_all <;>
      (intro h; first | exact absurd h.symm hq1 | exact absurd h.symm hq2)
  have hHe : ∀ p, p ≠ esI k r l → Hpk k r p (eI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [esI] at hp
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs : ∀ p, p ≠ eI k r l → Hpk k r p (esI k r l) = 0 := by
    intro p hp
    rw [Ne, Fin.ext_iff] at hp
    simp only [eI] at hp
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHe' : ∀ q, q ≠ esI k r l → Hpk k r (eI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [esI] at hq
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHs' : ∀ q, q ≠ eI k r l → Hpk k r (esI k r l) q = 0 := by
    intro q hq
    rw [Ne, Fin.ext_iff] at hq
    simp only [eI] at hq
    simp only [Hpk, esI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hHes : Hpk k r (eI k r l) (esI k r l) = 1 := by
    have h1 : (l : ℕ) + (2 * r + k - l) = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h1]
  have hHse : Hpk k r (esI k r l) (eI k r l) = 1 := by
    have h2 : ¬ (2 * r + k - (l : ℕ) < r) := by omega
    have h3 : 2 * r + k - (l : ℕ) + l = 2 * r + k := by omega
    simp [Hpk, eI, esI, hl, h2, h3]
  show (Q.w1 k r l x)ᴴ * Hpk k r * Q.w1 k r l x = Hpk k r
  ext p q
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol, apply_ite star, star_zero, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hp1 : p = eI k r l <;> by_cases hp2 : p = esI k r l <;>
    by_cases hq1 : q = eI k r l <;> by_cases hq2 : q = esI k r l <;>
    first
    | exact absurd (hp1.symm.trans hp2) hes
    | exact absurd (hq1.symm.trans hq2) hes
    | simp [hp1, hp2, hq1, hq2, hes, hes.symm, hHe, hHs, hHe', hHs', hHes, hHse, hx]

private theorem mul_mem_UH_of_mem_of_mem {n : ℕ} {H g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH H)
    (hh : h ∈ Formalism.QuantumDeterminants.UH H) : g * h ∈ Formalism.QuantumDeterminants.UH H := by
  have hg' : gᴴ * H * g = H := hg
  have hh' : hᴴ * H * h = H := hh
  show (g * h)ᴴ * H * (g * h) = H
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h by simp only [Matrix.mul_assoc], hg', hh']

private theorem wCell_mem_UH_Hpk_of_ne_zero {k r : ℕ} (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) (i : Fin (r + 1)) :
    Q.wCell k r i c ∈ Formalism.QuantumDeterminants.UH (Hpk k r) := by
  unfold Q.wCell
  induction ((List.finRange r).filter fun a => a.val < i.val) with
  | nil =>
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  | cons a L ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem_UH_of_mem_of_mem (w1_mem_UH_Hpk_of_ne_zero a (c a) (hc a)) ih

private theorem wCell_last_mul_mem_Glev_zero {k r : ℕ} (c : Fin r → ℂ) (hc : c ∈ OmX r) (g : Q.Mx k r)
    (hg : g ∈ Q.Glev k r (Fin.last r)) : Q.wCell k r (Fin.last r) c * g ∈ Q.Glev k r 0 :=
  ⟨mul_mem_UH_of_mem_of_mem (wCell_mem_UH_Hpk_of_ne_zero c hc _) hg.1, fun a ha => absurd ha (by simp)⟩

theorem jDRGrpP_of_parts (hR : JDRRadP) (hI : JDRRealInvP) : JDRGrpP := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨ε, hε⟩ := hR S.G.k S.G.r
  obtain ⟨Θ, hP, hC, hA⟩ := hI ε Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, hP, hC, ?_⟩
  intro J hJ c hc g hg hx
  have key := hε (Wp (S.pl v)) (Wq (S.pl v)) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'
    (OmP S T v) (y : ℂ) (T v).base.z_mem (T v).base.z'_mem (isDom_OmP_levTower_base S T v) J hJ c hc g hg hx
  rw [← key]
  have hx0 := wCell_last_mul_mem_Glev_zero c hc g hg
  obtain ⟨U, F, hU, hxU, hF, hFJ⟩ := hJ.1 _ ⟨hx0, hx⟩
  have hS : Q.SmoothLev S.G.k S.G.r 0 U J := fun g₀ hg₀ => ⟨U, F, hU, hg₀.2, hF, hFJ⟩
  have := hA U J hU hS _ ⟨hx0, hxU⟩
  simp only [Q.resG, this]

end

end Formalism.FourierDecayAlt.P.CutMP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def vABm (r : ℕ) (Y : ℂ) : ℕ → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X) × (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0 => (id, fun _ => 0)
  | i + 1 =>
    if h : i < r then
      (fun f => Y • (vABm r Y i).1 f - pbOp ⟨i, h⟩ ((vABm r Y i).1 f) - cbOp ⟨i, h⟩ ((vABm r Y i).2 f),
        fun f => cbiOp ⟨i, h⟩ ((vABm r Y i).1 f))
    else vABm r Y i

end defs

def JDAGrp : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℂ),
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ J) c g =
                dMul (drF S.G.r) (Q.crd (Q.cmp (Q.vAB S.G.r y S.G.r) 0)
                  (Q.resG S.G.k S.G.r (Fin.last S.G.r) J)) c g ∧
              Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θv J) c g =
                dMul (drbF S.G.r) (Q.crd (Q.cmp (vABm S.G.r y S.G.r) 0)
                  (Q.resG S.G.k S.G.r (Fin.last S.G.r) J)) c g

def JDAVTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
    ∀ y : ℂ,
      (Gauge.FamR P Bs Dc (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) Φ) ∧
        Gauge.VLem.trR P Bs.μsec e (Q.crd (Q.cmp (Q.vAB P.r y P.r) 0) Φ) =
          MA.actA P (L.Ar y) (Gauge.VLem.trR P Bs.μsec e Φ)) ∧
      (Gauge.FamR P Bs Dc (Q.crd (Q.cmp (vABm P.r y P.r) 0) Φ) ∧
        Gauge.VLem.trR P Bs.μsec e (Q.crd (Q.cmp (vABm P.r y P.r) 0) Φ) =
          MA.actA P (L.Avr y) (Gauge.VLem.trR P Bs.μsec e Φ))

theorem jDCapA_of_parts (hG : JDAGrp) (hV : JDAVTr) (hD : JDRDrTr) : JDCapA := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hL y
  obtain ⟨Θ, Θv, h1, h2, h3, h4, hR⟩ := hG Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, Θv, h1, h2, h3, h4, fun J hJ => ?_⟩
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -, -, -, -, -, -, hk, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  have hF := Gauge.tc_famR (D.parOf S v) (T v).base hpl J hJ
  obtain ⟨⟨hA, tA⟩, ⟨hAv, tAv⟩⟩ := hV _ _ (D.parOf S v) (T v).base hpl hk e hFr L hL _ _ hF y
  have hJR : trJ S T v e J = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e
      (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) := by
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e J ρ) = _
    rw [Gauge.tc_rawJ]
    rfl
  have hpt : ∀ (Θ' : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (F : Q.Fn S.G.k S.G.r (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
      (∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
        Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
        Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ' J) c g = F c g) →
      trJ S T v e (B.opApply Θ' J) = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e F := by
    intro Θ' F hF'
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e (B.opApply Θ' J) ρ) = _
    rw [Gauge.tc_rawJ]
    show MA.toSm _ _ = MA.toSm _ _
    congr 1
    funext q
    have hmu := Gauge.tc_mu (D.parOf S v) (T v).base hpl q
    simp only [Gauge.rawR]
    rw [hF' q.1.1 q.2.1 _ hmu.1 hmu.2]
  constructor
  · rw [hpt Θ _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).1), hJR]
    funext ρ
    show MA.toSm _ (Gauge.rawR _ _ e (dMul (drF _) _) ρ) = _
    rw [(hD _ _ (D.parOf S v) (T v).base hpl hk e hFr L hL _ _ hA).2 ρ, R.LevelData.Ahat, Gauge.actA_mul, ← tA]
    rfl
  · rw [hpt Θv _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).2), hJR]
    funext ρ
    show MA.toSm _ (Gauge.rawR _ _ e (dMul (drbF _) _) ρ) = _
    rw [(hD _ _ (D.parOf S v) (T v).base hpl hk e hFr L hL _ _ hAv).1 ρ, R.LevelData.Ahatv, Gauge.actA_mul, ← tAv]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP
end
