module

public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfSt
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

section

noncomputable section

open Formalism.IndefR.Datum MeasureTheory Matrix Filter Topology
open scoped ContDiff ComplexOrder

namespace Formalism.IndefR.Tow.SobPf.Avg

variable {n : ℕ}

theorem isUnit_det_of_cartan {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsUnit G.det := by
  unfold Formalism.IndefR.Datum.IsCartanInv at hs
  obtain ⟨_, _, hp⟩ := hs
  have h : (G * s).det ≠ 0 := hp.det_pos.ne'
  rw [Matrix.det_mul] at h
  exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul h)

theorem isUnit_det_of_UH {G u : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hu : u ∈ Formalism.QuantumDeterminants.UH G) :
    IsUnit u.det := by
  have hu' : uᴴ * G * u = G := hu
  have h := congrArg Matrix.det hu'
  rw [Matrix.det_mul, Matrix.det_mul] at h
  rw [← h] at hG
  exact isUnit_of_mul_isUnit_right hG

theorem UH_inv_left {G u : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hu : u ∈ Formalism.QuantumDeterminants.UH G) :
    (u⁻¹)ᴴ * G = G * u := by
  have hu' : uᴴ * G * u = G := hu
  have hdu := isUnit_det_of_UH hG hu
  have hdh : IsUnit uᴴ.det := by rw [Matrix.det_conjTranspose]; exact hdu.star
  rw [Matrix.conjTranspose_nonsing_inv]
  calc (uᴴ)⁻¹ * G = (uᴴ)⁻¹ * (uᴴ * G * u) := by rw [hu']
    _ = G * u := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (uᴴ)⁻¹, Matrix.nonsing_inv_mul _ hdh, Matrix.one_mul]

theorem UH_inv_right {G u : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hu : u ∈ Formalism.QuantumDeterminants.UH G) :
    G * u⁻¹ = uᴴ * G := by
  have hu' : uᴴ * G * u = G := hu
  have hdu := isUnit_det_of_UH hG hu
  calc G * u⁻¹ = uᴴ * G * u * u⁻¹ := by rw [hu']
    _ = uᴴ * G := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdu, Matrix.mul_one]

theorem inv_mem_UH {G u : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hu : u ∈ Formalism.QuantumDeterminants.UH G) :
    u⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  show (u⁻¹)ᴴ * G * u⁻¹ = G
  rw [UH_inv_left hG hu, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_det_of_UH hG hu),
    Matrix.mul_one]

theorem conj_mem_lieG {G u X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hu : u ∈ Formalism.QuantumDeterminants.UH G)
    (hX : X ∈ lieG G) : u⁻¹ * X * u ∈ lieG G := by
  have hX' : Xᴴ * G + G * X = 0 := hX
  have h1 := UH_inv_left hG hu
  have h2 := UH_inv_right hG hu
  show (u⁻¹ * X * u)ᴴ * G + G * (u⁻¹ * X * u) = 0
  have e : (u⁻¹ * X * u)ᴴ * G + G * (u⁻¹ * X * u) = uᴴ * (Xᴴ * G + G * X) * u := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul]
    congr 1
    · simp only [Matrix.mul_assoc]
      rw [h1]
    · simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc G u⁻¹, h2, Matrix.mul_assoc]
  rw [e, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem exp_conj_inv {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit u.det) (Y : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) :
    u⁻¹ * NormedSpace.exp (r • Y) * u = NormedSpace.exp (r • (u⁻¹ * Y * u)) := by
  rw [← Matrix.exp_conj' u (r • Y) ((Matrix.isUnit_iff_isUnit_det u).2 hu)]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem oneProd_succ {d : ℕ} (Y : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) (t : Fin (d + 1) → ℝ) :
    oneProd Y t = NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) := by
  simp only [oneProd, List.ofFn_succ, List.prod_cons]

theorem oneProd_conj {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit u.det) :
    ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℝ),
      u⁻¹ * oneProd Y t * u = oneProd (fun i => u⁻¹ * Y i * u) t := by
  intro d
  induction d with
  | zero =>
    intro Y t
    simp [oneProd, Matrix.nonsing_inv_mul _ hu]
  | succ d ih =>
    intro Y t
    have e := ih (fun i => Y i.succ) (fun i => t i.succ)
    rw [oneProd_succ, oneProd_succ, ← e, ← exp_conj_inv hu]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]

theorem oneProd_mul {u : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit u.det) {d : ℕ}
    (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℝ) :
    oneProd Y t * u = u * oneProd (fun i => u⁻¹ * Y i * u) t := by
  rw [← oneProd_conj hu Y t, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mul]

theorem oneProd_append {d d' : ℕ} (X : Fin d → Matrix (Fin n) (Fin n) ℂ) (Y : Fin d' → Matrix (Fin n) (Fin n) ℂ)
    (t : Fin d → ℝ) (s : Fin d' → ℝ) :
    oneProd (Fin.append X Y) (Fin.append t s) = oneProd X t * oneProd Y s := by
  have e : (fun i => NormedSpace.exp (Fin.append t s i • Fin.append X Y i)) =
      Fin.append (fun i => NormedSpace.exp (t i • X i)) (fun j => NormedSpace.exp (s j • Y j)) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right]
  simp only [oneProd]
  rw [e, List.ofFn_fin_append, List.prod_append]

def appL (d d' : ℕ) : (Fin d → ℝ) →L[ℝ] (Fin (d + d') → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun t => Fin.append t 0
      map_add' := fun a b => by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp
      map_smul' := fun c a => by
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp }

end Formalism.IndefR.Tow.SobPf.Avg

end
end

section

noncomputable section

open Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

namespace Chart

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

def cay (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 + 1) * Ring.inverse (g + 1) * (g - 1)

theorem isUnit_two : IsUnit (1 + 1 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨⟨1 + 1, (1 / 2 : ℂ) • 1, ?_, ?_⟩, rfl⟩
  · rw [add_mul, one_mul, ← add_smul]
    norm_num
  · rw [mul_add, mul_one, ← add_smul]
    norm_num

theorem cay_eq (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit (g + 1)) :
    cay g = (1 + 1) - (1 + 1) * Ring.inverse (g + 1) * (1 + 1) := by
  unfold cay
  have h1 : Ring.inverse (g + 1) * (g + 1) = 1 := Ring.inverse_mul_cancel _ hg
  have h2 : g - 1 = (g + 1) - (1 + 1) := by abel
  rw [h2, mul_sub, mul_assoc (1 + 1) (Ring.inverse (g + 1)) (g + 1), h1, mul_one]

theorem cay_inj {a b : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit (a + 1)) (hb : IsUnit (b + 1))
    (h : cay a = cay b) : a = b := by
  rw [cay_eq a ha, cay_eq b hb] at h
  have h2 := sub_right_inj.1 h
  have h3 : Ring.inverse (a + 1) = Ring.inverse (b + 1) :=
    isUnit_two.mul_left_cancel (isUnit_two.mul_right_cancel h2)
  calc a = (a + 1) - 1 := by abel
    _ = (a + 1) * (Ring.inverse (b + 1) * (b + 1)) - 1 := by rw [Ring.inverse_mul_cancel _ hb, mul_one]
    _ = ((a + 1) * Ring.inverse (a + 1)) * (b + 1) - 1 := by
        rw [h3, mul_assoc (a + 1) (Ring.inverse (b + 1)) (b + 1)]
    _ = b := by rw [Ring.mul_inverse_cancel _ ha, one_mul]; abel

theorem cay_mem (G g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hu : IsUnit (g + 1)) :
    cay g ∈ lieG G := by
  have h : gᴴ * G * g = G := hg
  have hcomm : (g - 1) * (g + 1) = (g + 1) * (g - 1) := by noncomm_ring
  have hR : Ring.inverse (g + 1) * (g + 1) = 1 := Ring.inverse_mul_cancel _ hu
  have hcT : cay g * (g + 1) = (1 + 1) * (g - 1) := by
    unfold cay
    rw [mul_assoc ((1 + 1) * Ring.inverse (g + 1)) (g - 1) (g + 1), hcomm,
      ← mul_assoc ((1 + 1) * Ring.inverse (g + 1)) (g + 1) (g - 1),
      mul_assoc (1 + 1) (Ring.inverse (g + 1)) (g + 1), hR, mul_one]
  have hTH : (g + 1)ᴴ * (cay g)ᴴ = ((1 + 1) * (g - 1))ᴴ := by
    rw [← Matrix.conjTranspose_mul, hcT]
  have key : (g + 1)ᴴ * ((cay g)ᴴ * G + G * cay g) * (g + 1) = 0 := by
    have e : (g + 1)ᴴ * ((cay g)ᴴ * G + G * cay g) * (g + 1) =
        ((g + 1)ᴴ * (cay g)ᴴ) * G * (g + 1) + (g + 1)ᴴ * G * (cay g * (g + 1)) := by noncomm_ring
    rw [e, hTH, hcT]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one]
    calc _ = (1 + 1 + 1 + 1) * (gᴴ * G * g - G) := by noncomm_ring
      _ = 0 := by rw [h, sub_self, mul_zero]
  have hTu : IsUnit (g + 1)ᴴ := hu.star
  show (cay g)ᴴ * G + G * cay g = 0
  have k2 : (g + 1)ᴴ * ((cay g)ᴴ * G + G * cay g) = (g + 1)ᴴ * 0 :=
    hu.mul_right_cancel (by rw [key, mul_zero, zero_mul])
  exact hTu.mul_left_cancel k2

theorem hasStrictFDerivAt_cay :
    HasStrictFDerivAt (cay : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) 1 := by
  have hT : HasStrictFDerivAt (fun g : Matrix (Fin n) (Fin n) ℂ => g + 1)
      (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 :=
    (hasStrictFDerivAt_id (𝕜 := ℝ) (1 : Matrix (Fin n) (Fin n) ℂ)).add_const 1
  have hI := (hasStrictFDerivAt_ringInverse (𝕜 := ℝ) (isUnit_two (n := n)).unit).comp
    (1 : Matrix (Fin n) (Fin n) ℂ) hT
  have ha := hI.const_mul (1 + 1 : Matrix (Fin n) (Fin n) ℂ)
  have hb : HasStrictFDerivAt (fun g : Matrix (Fin n) (Fin n) ℂ => g - 1)
      (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 :=
    (hasStrictFDerivAt_id (𝕜 := ℝ) (1 : Matrix (Fin n) (Fin n) ℂ)).sub_const 1
  have hm := ha.mul' hb
  show HasStrictFDerivAt (fun g : Matrix (Fin n) (Fin n) ℂ => (1 + 1) * Ring.inverse (g + 1) * (g - 1)) _ _
  refine hm.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun h => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.one_apply, sub_self, smul_zero, add_zero, smul_eq_mul,
    Function.comp_apply]
  rw [Ring.mul_inverse_cancel _ isUnit_two]
  simp
  first
    | exact one_mul h
    | erw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.id_apply,
        smul_eq_mul, one_mul]

end Chart

end Formalism.IndefR.Tow.SobPf

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Mult
  MeasureTheory Matrix Filter Topology

namespace Formalism.IndefR.Tow.SobPf

namespace KFin

variable {n : ℕ}

def KS (G s : Matrix (Fin n) (Fin n) ℂ) : Set (Fin n → Fin n → ℂ) := {k | Matrix.of k ∈ KAt G s}

theorem isCompact_KS {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCompact (KS G s) := isCompact_KAt hs

section Int

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuousOn_avg {G s : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hπ : IsGRep G π) {p : (Fin n → Fin n → ℂ) → ℂ} (hp : Continuous p) (w : H) :
    ContinuousOn (fun k => p k • π (Matrix.of k) w) (KS G s) := by

  have hmaps : Set.MapsTo (fun k : Fin n → Fin n → ℂ => Matrix.of k) (KS G s) (Formalism.QuantumDeterminants.UH G) :=
    fun k hk => (show Matrix.of k ∈ Formalism.QuantumDeterminants.UH G ∧ Matrix.of k * s = s * Matrix.of k from hk).1
  have hof : ContinuousOn (fun k : Fin n → Fin n → ℂ => Matrix.of k) (KS G s) :=
    continuous_id.continuousOn
  have h1 : ContinuousOn (fun k : Fin n → Fin n → ℂ => π (Matrix.of k) w) (KS G s) :=
    (hπ.2.2.2 w).comp hof hmaps
  exact hp.continuousOn.smul h1

theorem integrable_avg {G s : Matrix (Fin n) (Fin n) ℂ} {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hs : IsCartanInv G s) (hπ : IsGRep G π) {μ : Measure (Fin n → Fin n → ℂ)} (hμ : IsHaarK G s μ)
    {p : (Fin n → Fin n → ℂ) → ℂ} (hp : Continuous p) (w : H) :
    Integrable (fun k => p k • π (Matrix.of k) w) μ := by

  haveI := hμ.1
  have hae : ∀ᵐ k ∂μ, k ∈ KS G s := hμ.2.1
  have h := (continuousOn_avg (s := s) hπ hp w).integrableOn_compact (μ := μ) (isCompact_KS hs)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at h

end Int

abbrev Var (n : ℕ) := (Fin n × Fin n) ⊕ (Fin n × Fin n)

def subst (A : Matrix (Fin n) (Fin n) ℂ) : Var n → MvPolynomial (Var n) ℂ
  | Sum.inl ij => ∑ l, MvPolynomial.C (A ij.1 l) * MvPolynomial.X (Sum.inl (l, ij.2))
  | Sum.inr ij => ∑ l, MvPolynomial.C (starRingEnd ℂ (A ij.1 l)) * MvPolynomial.X (Sum.inr (l, ij.2))

theorem evalMatrix_bind₁_mulLeft (A : Matrix (Fin n) (Fin n) ℂ) (q : MvPolynomial (Var n) ℂ) (k : Fin n → Fin n → ℂ) :
    evP (MvPolynomial.bind₁ (subst A) q) k = evP q (Matrix.of.symm (A * Matrix.of k)) := by

  induction q using MvPolynomial.induction_on
  next a =>
    simp [evP]
  next p r hp hr =>
    simp only [evP, map_add (f := _)] at hp hr ⊢
    rw [hp, hr]
  next p v hp =>
    simp only [evP, map_mul, MvPolynomial.bind₁_X_right, MvPolynomial.eval_X] at hp ⊢
    rw [hp]
    congr 1
    rcases v with ⟨i, j⟩ | ⟨i, j⟩
    · simp [subst, Matrix.mul_apply, Matrix.of_apply, MvPolynomial.eval_X, MvPolynomial.eval_C]

    · simp [subst, Matrix.mul_apply, Matrix.of_apply, MvPolynomial.eval_X, MvPolynomial.eval_C, map_sum]

theorem totalDegree_subst (A : Matrix (Fin n) (Fin n) ℂ) (v : Var n) : (subst A v).totalDegree ≤ 1 := by

  rcases v with ij | ij <;>
  · simp only [subst]
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    simp

theorem totalDegree_bind_le (A : Matrix (Fin n) (Fin n) ℂ) (q : MvPolynomial (Var n) ℂ) :
    (MvPolynomial.bind₁ (subst A) q).totalDegree ≤ q.totalDegree := by

  conv_lhs => rw [q.as_sum]

  rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
    (Nat.mul_le_mul le_rfl (totalDegree_subst A i))) ?_
  simp only [mul_one]
  exact MvPolynomial.le_totalDegree hm

def Mon (n N : ℕ) : Set (Var n →₀ ℕ) := {m | (m.sum fun _ e => e) ≤ N}

theorem finite_Mon (n N : ℕ) : (Mon n N).Finite := by

  refine (Set.finite_range (fun f : Var n → Fin (N + 1) =>
    Finsupp.equivFunOnFinite.symm (fun v => (f v : ℕ)))).subset ?_
  intro m hm
  have hm' : ∑ v ∈ m.support, m v ≤ N := hm
  have hle : ∀ v, m v ≤ N := by
    intro v
    by_cases hv : v ∈ m.support
    · exact le_trans (Finset.single_le_sum (f := fun v => m v) (fun _ _ => Nat.zero_le _) hv) hm'
    · have h0 : m v = 0 := by simpa using hv
      rw [h0]; exact Nat.zero_le _
  refine ⟨fun v => ⟨m v, Nat.lt_succ_of_le (hle v)⟩, ?_⟩
  ext v
  simp

theorem evalMatrix_eq_sum_monomial (q : MvPolynomial (Var n) ℂ) (k : Fin n → Fin n → ℂ) :
    evP q k = ∑ m ∈ q.support, q.coeff m * evP (MvPolynomial.monomial m 1) k := by

  simp only [evP]
  conv_lhs => rw [q.as_sum]

  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show MvPolynomial.monomial m (q.coeff m) =
      MvPolynomial.C (q.coeff m) * MvPolynomial.monomial m (1 : ℂ) by
    rw [MvPolynomial.C_mul_monomial, mul_one], map_mul, MvPolynomial.eval_C]

end KFin

end Formalism.IndefR.Tow.SobPf

end
end
