module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadCorrespondenceOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SingleMulVecOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle074
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle123
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.HermitianCurvature.StatementPN
public import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe
public import Formalism.FlagUnipotentLattices.Bundle003
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBI

open Finset Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

noncomputable section

section lev

variable {k : ℕ}

theorem castV_mulVec' {a b : ℕ} (h : a = b) (M : B.Mat k a) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h (M *ᵥ v) = D.castM h M *ᵥ D.castV h v := by
  subst h
  rw [Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl, Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl]

theorem zL_lift {o ρ r : ℕ} (h : o + ρ = r) (v : Fin (2 * ρ + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h (D.castV h (liftVec k o ρ v)) = v := by
  subst h
  rw [Formalism.FourierDecayAlt.P.Dx2.Tower.castV_rfl]
  funext i
  have := Formalism.FourierDecayAlt.P.Dx2.Tower.liftVec_levPos_gen (k := k) o ρ v i
  simpa [Formalism.FourierDecayAlt.P.Dx2.Tower.zL, levPos] using this

theorem zL_smul {o ρ r : ℕ} (h : o + ρ = r) (c : ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h (c • v) = c • Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h v := by
  funext i; simp [Formalism.FourierDecayAlt.P.Dx2.Tower.zL]

theorem hermitian_form_anisotropic_part {m : ℕ} (v w : Fin (2 * m + k + 1) → ℂ) (hv : inWb k m v) (hw : inWb k m w) :
    herm (Hpk k m) v w = herm (Hb k) (wbPart k m v) (wbPart k m w) := by
  have := Formalism.FourierDecayAlt.P.TwoByOneBlock.herm_jV (k := k) (r := m) (wbPart k m v) (wbPart k m w)
  rwa [Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hv, Formalism.FourierDecayAlt.P.TwoByOneBlock.jV_wbPart hw] at this

theorem herm_zL {o ρ r : ℕ} (h : o + ρ = r) (v w : Fin (2 * r + k + 1) → ℂ) (hv : inWb k r v) (hw : inWb k r w) :
    herm (Hpk k ρ) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h v) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL o ρ h w) = herm (Hpk k r) v w := by
  rw [hermitian_form_anisotropic_part _ _ (Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wb o ρ h v hv) (Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wb o ρ h w hw),
    Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wbPart, Formalism.FourierDecayAlt.P.Dx2.Tower.zL_wbPart, hermitian_form_anisotropic_part v w hv hw]

theorem inWb_last {r : ℕ} (v : Fin (2 * (r - r) + k + 1) → ℂ) : inWb k (r - r) v := by
  intro i hi; exfalso; have := i.isLt; omega

theorem inWb_liftLast {r : ℕ} (h : r + (r - r) = r) (v : Fin (2 * (r - r) + k + 1) → ℂ) :
    inWb k r (D.castV h (liftVec k r (r - r) v)) := by
  intro i hi
  simp only [D.castV]
  apply Formalism.FourierDecayAlt.P.Dx2.Tower.liftVec_out_gen
  simp only [Fin.val_cast]
  omega

end lev

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def nuR (p : KB.Pl P Wp Wq) : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ :=
  Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) (by omega) p.ν'

def m0R (p : KB.Pl P Wp Wq) : B.Mat P.k (P.r - P.r) :=
  fun i j => p.m₀ ⟨i.val + P.r, by have := i.isLt; omega⟩ ⟨j.val + P.r, by have := j.isLt; omega⟩

theorem base_point_block_eq (p : KB.Pl P Wp Wq) :
    D.castM (by omega : P.r + (P.r - P.r) = P.r) (ιLev P.k P.r (P.r - P.r) (m0R p)) = p.m₀ := by
  obtain ⟨-, -, -, ⟨hmU, hmfix⟩, -⟩ := p.hF
  have hme : ∀ a : Fin P.r, p.m₀ *ᵥ ee P.k P.r a = ee P.k P.r a := fun a => (hmfix a a.isLt).1
  have hms : ∀ a : Fin P.r, p.m₀ *ᵥ es P.k P.r a = es P.k P.r a := fun a => (hmfix a a.isLt).2
  have hcol : ∀ (i j : Fin (2 * P.r + P.k + 1)), (j.val < P.r ∨ P.r + P.k < j.val) →
      p.m₀ i j = if i = j then 1 else 0 := by
    intro i j hj
    rcases hj with hj | hj
    · have e : bvec j = ee P.k P.r ⟨j.val, hj⟩ := by simp [ee, eI]
      have := congrFun (hme ⟨j.val, hj⟩) i
      rw [← e] at this
      simp only [mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      rw [this, eq_comm]
    · have hj2 := j.isLt
      have e : bvec j = es P.k P.r ⟨2 * P.r + P.k - j.val, by omega⟩ := by
        simp only [es, esI]; congr 1; ext; simp; omega
      have := congrFun (hms ⟨2 * P.r + P.k - j.val, by omega⟩) i
      rw [← e] at this
      simp only [mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      rw [this, eq_comm]
  have hrow : ∀ (i j : Fin (2 * P.r + P.k + 1)), (i.val < P.r ∨ P.r + P.k < i.val) →
      (P.r ≤ j.val ∧ j.val ≤ P.r + P.k) → p.m₀ i j = 0 := by
    intro i j hi hj
    have hmj : (p.m₀ *ᵥ bvec j) i = p.m₀ i j := by
      simp [mulVec, dotProduct, bvec, Pi.single_apply]
    rcases hi with hi | hi
    · have h1 := herm_es (k := P.k) (r := P.r) (p.m₀ *ᵥ bvec j) ⟨i.val, hi⟩
      rw [← hms ⟨i.val, hi⟩, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, herm_es] at h1
      have hi' : eI P.k P.r ⟨i.val, hi⟩ = i := by ext; simp [eI]
      rw [hi', hmj] at h1
      rw [← h1]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; omega
    · have hi2 := i.isLt
      have h1 := herm_ee (k := P.k) (r := P.r) (p.m₀ *ᵥ bvec j) ⟨2 * P.r + P.k - i.val, by omega⟩
      rw [← hme ⟨2 * P.r + P.k - i.val, by omega⟩, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU, herm_ee] at h1
      have hi' : esI P.k P.r ⟨2 * P.r + P.k - i.val, by omega⟩ = i := by ext; simp [esI]; omega
      rw [hi', hmj] at h1
      rw [← h1]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; omega
  ext i j
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_apply]
  unfold ιLev
  by_cases hi : P.r ≤ i.val ∧ i.val ≤ P.r + P.k <;> by_cases hj : P.r ≤ j.val ∧ j.val ≤ P.r + P.k
  · rw [dite_eq_left (by simp; omega), dite_eq_left (by simp; omega)]
    simp only [m0R]
    congr 1 <;> ext <;> simp <;> omega
  · rw [dite_eq_left (by simp; omega), dite_eq_right (by simp; omega), hcol i j (by omega)]
    rw [if_neg]; intro h; rw [h] at hi; exact hj hi
  · rw [dite_eq_right (by simp; omega)]
    rw [hrow i j (by omega) hj, if_neg]
    · intro h; apply hi; have := congrArg Fin.val h; simp at this; omega
  · rw [dite_eq_right (by simp; omega), hcol i j (by omega)]
    congr 1
    apply propext; constructor
    · intro h; ext; have := congrArg Fin.val h; simpa using this
    · intro h; subst h; rfl

theorem levFrame_nuR (p : KB.Pl P Wp Wq) : LevFrame p (nuR p) (m0R p) := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := p.hF
  have h : P.r + (P.r - P.r) = P.r := by omega
  have hZ : (p.T.bs P.r).z = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h p.T.base.z := by
    show (p.T.bs P.r).z = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.T.bs 0).z
    rw [← p.T.z_lev P.r le_rfl, zL_lift]
  have hZ' : (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h p.T.base.z' := by
    show (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.T.bs 0).z'
    rw [← p.T.z'_lev P.r le_rfl, zL_lift]
  have hz := p.T.base.z_mem
  have hz' := p.T.base.z'_mem
  have hblk := base_point_block_eq p

  set Lf : (Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) → (Fin (2 * P.r + P.k + 1) → ℂ) :=
    fun v => D.castV h (liftVec P.k P.r (P.r - P.r) v) with hLf
  have hLm : ∀ v, Lf (m0R p *ᵥ v) = p.m₀ *ᵥ Lf v := by
    intro v
    simp only [hLf]
    rw [← Formalism.FourierDecayAlt.P.Dx2.Tower.lev_mulVec_lift, castV_mulVec', hblk]
  have hLh : ∀ v w, herm (Hpk P.k (P.r - P.r)) v w = herm (Hpk P.k P.r) (Lf v) (Lf w) := by
    intro v w
    rw [← herm_zL h (Lf v) (Lf w) (inWb_liftLast h v) (inWb_liftLast h w), zL_lift, zL_lift]
  refine ⟨Formalism.FourierDecayAlt.P.Dx2.Tower.lift_zL P.r (P.r - P.r) h p.ν' hν, hblk, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact inWb_last _
  · rw [hZ', nuR, herm_zL h _ _ hν hz', hνz]
  · rw [nuR, herm_zL h _ _ hν hν, hνν]
  · apply B2x4.mem_UH_of_herm
    intro x y
    rw [hLh, hLh x y, hLm, hLm, Formalism.FourierDecayAlt.P.Dx2.DF.herm_m0_mulVec_invariant p.m₀ hmU]
  · intro a _; exact absurd a.isLt (by omega)
  · have e1 : m0R p *ᵥ (p.T.bs P.r).z' = Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h (p.m₀ *ᵥ p.T.base.z') := by
      have := congrArg (Formalism.FourierDecayAlt.P.Dx2.Tower.zL P.r (P.r - P.r) h) (hLm (p.T.bs P.r).z')
      rw [zL_lift] at this
      rw [this, hZ']
      simp only [hLf]
      rw [Formalism.FourierDecayAlt.P.Dx2.Tower.lift_zL P.r (P.r - P.r) h _ hz']
    rw [e1, hmz, zL_smul, ← hZ, hZ', hZ, Formalism.FourierDecayAlt.P.Dx2.Tower.zL_Tz _ _ h _ hz,
      Formalism.FourierDecayAlt.P.Dx2.Tower.zL_Tz _ _ h _ hz']

end place

end

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem levFrameExists_statement : PBI.LevFrameExists := by
  intro Wp Wq _ _ _ _ _ _ P p
  exact ⟨PBI.nuR p, PBI.m0R p, PBI.levFrame_nuR p⟩

end Formalism.FourierDecayAlt.P
end

section

open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrCap

theorem not_cdom_raise_of_lt {k : ℕ} {Λ : Fin k → ℝ} {a b : Fin k} (hab : a < b)
    (h : PI.UpqRep.CDom (PI.UpqRep.allPos k)
      (fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) Λ) : False := by
  obtain ⟨c, hc, heq⟩ := h
  have hsing : ∀ p : Fin k, ∑ j : Fin k, ((j : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : Fin k → ℝ) j = ((p : ℕ) : ℝ) := by
    intro p
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  have e1 : ∑ j : Fin k, ((j : ℕ) : ℝ) *
      (Λ - fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) j =
      ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    have hj : ∀ j : Fin k,
        (Λ - fun c => Λ c + (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) j =
          (Pi.single b (1 : ℝ) : Fin k → ℝ) j - (Pi.single a (1 : ℝ) : Fin k → ℝ) j := by
      intro j
      simp only [Pi.sub_apply, Pi.single_apply]
      ring
    simp only [hj, mul_sub, Finset.sum_sub_distrib, hsing]
  have e2 : ∑ j : Fin k, ((j : ℕ) : ℝ) *
      (∑ p, ∑ q, (c p q : ℝ) • PI.UpqRep.root p q) j ≤ 0 := by
    have hj : ∀ j : Fin k, ((j : ℕ) : ℝ) * (∑ p, ∑ q, (c p q : ℝ) • PI.UpqRep.root p q) j =
        ∑ p, ∑ q, (c p q : ℝ) * (((j : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : Fin k → ℝ) j -
          ((j : ℕ) : ℝ) * (Pi.single q (1 : ℝ) : Fin k → ℝ) j) := by
      intro j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PI.UpqRep.root, Pi.sub_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    apply Finset.sum_nonpos
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_nonpos
    intro q _
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsing, hsing]
    by_cases h0 : c p q = 0
    · simp [h0]
    · have hpq : ((p : ℕ) : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast (hc p q h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  rw [heq] at e1
  linarith

theorem core {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} {g : Mx k r} {u : Fin k → ℝ}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : IsRepW k r z π) (hgU : g ∈ UH (Hpk k r))
    (hgfix : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (s : ℂ) (hgz : g *ᵥ (s • bvec (wI k r (Fin.last k))) = z)
    (hK : PI.UpqRep.IsKTypeOf (PI.UpqRep.allPos k) (fun h => π (g * PI.UpqRep.blockW k r h * g⁻¹))
      (PI.UpqRep.lowK (PI.UpqRep.allPos k) u) ⊤) (w : ℂ) (v : W) :
    qdet (EB π (fr k r g)) w v =
      cpol (fun j : Fin k => ((PI.UpqRep.lowK (PI.UpqRep.allPos k) u j : ℝ) : ℂ) - ((j : ℕ) : ℂ)) w • v := by
  set Bs := fr k r g with hBs
  have hB : IsFrameOf k r [z] Bs := fr_frame hgU hgfix s hgz
  set Λ := PI.UpqRep.lowK (PI.UpqRep.allPos k) u with hΛ
  set E := EB π Bs with hE
  have hgl : GlRel E := (frame_general_linear W k r k z π Bs hR hB).1
  set Ec : Fin k → (W →L[ℂ] W) := fun c => ecOp π (unitB (Hpk k r) Bs c c) with hEc
  have hEE : ∀ c x, E c c x = Ec c x := fun c x => rfl
  have hσ : ∀ θ : Fin k → ℝ, π (g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹) =
      NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • Ec c) := by
    intro θ
    rw [← torus hgU θ]
    exact op_torus hR hB θ
  obtain ⟨-, -, hirr, ⟨v₀, -, hv0, hwt⟩, hdom⟩ := hK

  have hdiag : ∀ c, E c c v₀ = (Λ c : ℂ) • v₀ := by
    intro c
    set A := hpart2 (Hpk k r) (unitB (Hpk k r) Bs c c) with hAdef
    have hA : InLieW k r z A := (QrD.frame_lie hB c c).2
    have hAe : A = (-Complex.I) • unitB (Hpk k r) Bs c c := hpart2_self Bs c
    have hf : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • A)) v₀) =
        fun t : ℝ => Complex.exp (((-t * Λ c : ℝ) : ℂ) * Complex.I) • v₀ := by
      funext t
      set θ : Fin k → ℝ := fun c' => if c' = c then -t else 0 with hθ
      have h1 : (t : ℂ) • A = ∑ c', ((θ c' : ℂ) * Complex.I) • unitB (Hpk k r) Bs c' c' := by
        rw [Finset.sum_eq_single c (fun b _ hb => by simp [hθ, hb]) (fun h => absurd (Finset.mem_univ c) h)]
        rw [hAe, smul_smul]
        congr 1
        simp only [hθ, if_pos rfl]
        push_cast
        ring
      have hsθ : ∑ a, Λ a * θ a = -t * Λ c := by
        rw [Finset.sum_eq_single c (fun b _ hb => by simp [hθ, hb]) (fun h => absurd (Finset.mem_univ c) h)]
        simp only [hθ, if_pos rfl]
        ring
      rw [h1, torus hgU θ]
      refine (hwt θ (Dg_mem θ)).trans ?_
      rw [hsθ]
    have hd : dOp π A v₀ = (-(Λ c : ℂ) * Complex.I) • v₀ := by
      rw [← QrD.dRep_eq hR.1 hR.2 hA v₀]
      unfold dRep
      rw [hf]
      exact (deriv_cexp (Λ c) v₀).deriv
    rw [hEE]
    show ecOp π (unitB (Hpk k r) Bs c c) v₀ = _
    unfold ecOp
    rw [hpart1_self, SkewHermitianParts.dOp_zero, zero_add, _root_.smul_apply, hd, smul_smul]
    congr 1
    linear_combination (-(Λ c : ℂ)) * Complex.I_sq

  have hup : ∀ a b, a < b → E a b v₀ = 0 := by
    intro a b hab
    by_contra hne
    set x := E a b v₀ with hx
    have hxw : ∀ c, Ec c x = (((fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) c : ℝ) : ℂ) • x := by
      intro c
      rw [← hEE, hx, CommonEigenvectors.diag_move hgl c a b v₀, hdiag c, map_smul]
      by_cases hca : c = a <;> by_cases hcb : c = b
      · exact absurd (hca.symm.trans hcb) hab.ne
      · rw [if_pos hca, if_neg (fun h => hcb h.symm)]
        simp only [if_pos hca, if_neg hcb]
        push_cast
        module
      · rw [if_neg hca, if_pos hcb.symm]
        simp only [if_neg hca, if_pos hcb]
        push_cast
        module
      · rw [if_neg hca, if_neg (fun h => hcb h.symm)]
        simp only [if_neg hca, if_neg hcb]
        push_cast
        module
    have hwx : PI.UpqRep.IsWtOn (PI.UpqRep.Kset (PI.UpqRep.allPos k)) (fun h => π (g * PI.UpqRep.blockW k r h * g⁻¹))
        (fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) x := by
      intro θ _
      show π (g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹) x = _
      rw [hσ θ]
      exact exp_sum_eig Ec θ _ x hxw
    exact not_cdom_raise_of_lt hab (hdom _ x Submodule.mem_top hne hwx)

  have hHW : IsHW E (fun j => (Λ j : ℂ)) v₀ := ⟨hdiag, hup⟩
  set m : Fin k → ℂ := fun j => (Λ j : ℂ) - ((j : ℕ) : ℂ) with hm
  have hq0 : ∀ w', qdet E w' v₀ = cpol m w' • v₀ := by
    intro w'
    rw [quantumDetHighestWeight_holds W k E _ v₀ hgl hHW w']
    congr 1
    unfold cpol
    apply Finset.prod_congr rfl
    intro j _
    simp only [hm]
    ring
  have hmem : v₀ ∈ CapSp E m := mem_CapSp.2 hq0
  have hstab : Stab E (CapSp E m) := (capelli_stabilizer W k E m hgl).1
  have hirrE : ∀ S : Submodule ℂ W, Stab E S → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hU := lie_stabilizer W k r z π Bs hz hT hR hB S hS
    refine hirr S le_top ?_
    intro h hh y hy
    have hu : hᴴ * h = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.1 hh.1
      rwa [Matrix.star_eq_conjTranspose] at this
    exact hU _ (emb_uw hgU hgfix s hgz hu) y hy
  have htop : CapSp E m = ⊤ := by
    rcases hirrE _ hstab with h | h
    · exfalso
      rw [h] at hmem
      exact hv0 ((Submodule.mem_bot ℂ).1 hmem)
    · exact h
  have hv : v ∈ CapSp E m := by
    rw [htop]
    exact Submodule.mem_top
  exact mem_CapSp.1 hv w

end QrCap

end Formalism.FourierDecayAlt.P
end
end

section

namespace Formalism.FourierDecayAlt.P.NormChainLemmas

open Formalism.FourierDecayAlt.PN Finset NumberField

open scoped ComplexOrder ComplexConjugate

open Classical

theorem exactCores : Formalism.FourierDecayAlt.PN.ExactCores :=
  ⟨Formalism.HermitianLatticeCounting.Final.S4.step4, Formalism.HermitianLatticeCounting.Final.S4.omCount, Formalism.HermitianLatticeCounting.Final.S4.weightedCS,
   Formalism.HermitianLatticeCounting.Final.ExpansionTerms.component_total_sixty_four⟩

theorem loopCores : Formalism.FourierDecayAlt.PN.LoopCores :=
  ⟨Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.nonDegSum, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.degSum, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.single_row_lattice_sum_bound,
   Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.gainSqrt, Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.lattice_exp_sum_upper_bound, Formalism.FourierDecayAlt.Final.pb_loopsJoint,
   Formalism.FourierDecayAlt.Final.pb_loopsGiveRows⟩

theorem nGChain : Formalism.FourierDecayAlt.PN.NGChain :=
  ⟨exactCores, Formalism.FourierDecayAlt.Final.pn_classSquaresSum, Formalism.FourierDecayAlt.Final.pn_rowFromClasses,
   Formalism.FourierDecayAlt.Final.pn_classCS, Formalism.FourierDecayAlt.Final.pn_firstBracket, Formalism.FourierDecayAlt.Final.pn_secondBracket,
   Formalism.FourierDecayAlt.Final.pn_meanAmpJoint, Formalism.FourierDecayAlt.Final.pn_rowNGAbstract, Formalism.FourierDecayAlt.Final.pn_normBound,
   Formalism.FourierDecayAlt.Final.pn_framePassage, Formalism.FourierDecayAlt.Final.pn_normRe, Formalism.FourierDecayAlt.Final.pn_exponentSum,
   Formalism.FourierDecayAlt.Final.pn_nGNumbers⟩

end Formalism.FourierDecayAlt.P.NormChainLemmas

namespace Formalism.FourierDecayAlt.P

theorem loop_kernels : Formalism.FourierDecayAlt.PN.LoopCores := NormChainLemmas.loopCores

theorem norm_chain : Formalism.FourierDecayAlt.PN.NGChain := NormChainLemmas.nGChain

end Formalism.FourierDecayAlt.P
end
