module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle144
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle156
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle147
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle158
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle157
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle161
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
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
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle053

@[expose] public section

section

open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def TopG {ι X : Type} [DecidableEq ι] (Eop : ι → ι → (X → E) → (X → E)) (u : ℂ) (a b : ι) (f : X → E) : X → E :=
  fun g => (if a = b then u • f g else 0) + Eop a b f g

def qminG {ι X : Type} [DecidableEq ι] {t : ℕ} (Eop : ι → ι → (X → E) → (X → E)) (a b : Fin t → ι) (u : ℂ)
    (f : X → E) : X → E :=
  ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun k : Fin t => TopG Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).foldr (fun T h => T h) f)

def EopZ (k r j : ℕ) (p q : Fin (2 * r + k + 1)) : (MJ j → E) → MJ j → E :=
  if hp : p.val < j then (if hq : q.val < j then EZ ⟨p.val, hp⟩ ⟨q.val, hq⟩ else fun _ _ => 0)
  else if hp' : 2 * r + k < p.val + j then
    (if hq' : 2 * r + k < q.val + j then
      EZs ⟨2 * r + k - p.val, by omega⟩ ⟨2 * r + k - q.val, by omega⟩ else fun _ _ => 0)
  else fun _ _ => 0

def cZ {j N : ℕ} (Z : MJ j) (p : Fin N) (a : Fin j) : ℂ := if hp : p.val < j then Z a ⟨p.val, hp⟩ else 0

def cvZ (k r : ℕ) {j : ℕ} (Z : MJ j) (p : Fin (2 * r + k + 1)) (a : Fin j) : ℂ :=
  if hp : 2 * r + k < p.val + j then conj (Z a ⟨2 * r + k - p.val, by omega⟩) else 0


open scoped Classical in
def AZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (u : ℂ) (h : MJ j → E) : MJ j → E := fun Z =>
  ∑ c : Fin m → Fin (2 * r + k + 1),
    if StrictMono c then
      (Matrix.of fun a l : Fin m => cZ Z (c l) (Fin.castLE hmj a)).det •
        qminG (EopZ (E := E) k r j) (C3.xR k r m hm) c u h Z
    else 0


open scoped Classical in
def AvZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (ell : ℂ) (h : MJ j → E) : MJ j → E := fun Z =>
  ∑ B : Fin m → Fin (2 * r + k + 1),
    if StrictMono (fun l => C3.keyS k r (B l)) then
      (Matrix.of fun a l : Fin m => cvZ k r Z (B l) (Fin.castLE hmj a)).det •
        qminG (EopZ (E := E) k r j) B (C3.sR k r m hm) (ell + (m : ℂ) - 1) h Z
    else 0

def Aform (k r j : ℕ) (hj : j + 1 ≤ r) (l : C.Letter) (e : Fin 2) (h : MJ j → E) : MJ j → E := fun Z =>
  if e = 1 ∧ j = 0 then 0 else
  if l.1 then
    (Z.det)⁻¹ • AZ k r j (j - e) (by omega) (by omega) ((l.2 : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) h Z
  else
    (conj Z.det)⁻¹ • AvZ k r j (j - e) (by omega) (by omega) ((l.2 : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) h Z

section zop

variable (hR : ZOpRd)
include hR

theorem zop_EZ {j : ℕ} (a b : Fin j) : ZOp (E := E) (EZ a b) :=
  (hR j E _).add' ((hR j E _).csmul Complex.I)

theorem zop_EZs {j : ℕ} (a b : Fin j) : ZOp (E := E) (EZs a b) :=
  (hR j E _).add' ((hR j E _).csmul Complex.I)

theorem zop_EopZ (k r j : ℕ) (p q : Fin (2 * r + k + 1)) : ZOp (E := E) (EopZ k r j p q) := by
  unfold EopZ
  split_ifs
  · exact zop_EZ hR _ _
  · exact zop_zero
  · exact zop_EZs hR _ _
  · exact zop_zero
  · exact zop_zero

theorem zop_TopG (k r j : ℕ) (u : ℂ) (p q : Fin (2 * r + k + 1)) :
    ZOp (E := E) (TopG (EopZ k r j) u p q) := by
  have h1 : ZOp (E := E) (j := j) (fun f g => if p = q then u • f g else 0) := by
    split_ifs
    · exact zop_id.csmul u
    · exact zop_zero
  exact h1.add' (zop_EopZ hR k r j p q)

theorem zop_qminG (k r j : ℕ) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    ZOp (E := E) (qminG (EopZ k r j) a b u) := by
  have e : (qminG (E := E) (EopZ k r j) a b u) = fun h Z => ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin t))),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun k' : Fin t =>
        TopG (EopZ (E := E) k r j) (u - ((k' : ℕ) : ℂ)) (a (σ k')) (b k')).foldr (fun T h => T h) h Z) := by
    funext h Z
    simp [qminG, Finset.sum_apply]
  rw [e]
  refine zop_sum _ (fun σ _ => ?_)
  refine ZOp.csmul ?_ _
  refine zop_foldr _ (fun T hT => ?_)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
  exact zop_TopG hR k r j _ _ _

end zop

theorem contDiff_entry {j : ℕ} (a b : Fin j) : ContDiff ℝ ∞ fun Z : MJ j => Z a b :=
  (contDiff_apply ℝ (fun _ => ℂ) b).comp (contDiff_apply ℝ (fun _ => (Fin j → ℂ)) a)

theorem contDiff_det_of {j m : ℕ} (M : MJ j → Matrix (Fin m) (Fin m) ℂ) (hM : ∀ a b, ContDiff ℝ ∞ fun Z => M Z a b) :
    ContDiff ℝ ∞ fun Z => (M Z).det := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum (fun σ _ => ?_)
  simp only [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod (fun i _ => hM _ _))

theorem contDiff_cZ {j N : ℕ} (p : Fin N) (a : Fin j) : ContDiff ℝ ∞ fun Z : MJ j => cZ Z p a := by
  unfold cZ
  split_ifs
  · exact contDiff_entry _ _
  · exact contDiff_const

theorem contDiff_cvZ (k r : ℕ) {j : ℕ} (p : Fin (2 * r + k + 1)) (a : Fin j) :
    ContDiff ℝ ∞ fun Z : MJ j => cvZ k r Z p a := by
  unfold cvZ
  split_ifs
  · exact Complex.conjCLE.contDiff.comp (contDiff_entry _ _)
  · exact contDiff_const

theorem contDiffOn_invDet {j : ℕ} : ContDiffOn ℝ ∞ (fun Z : MJ j => (Z.det)⁻¹) {Z | Z.det ≠ 0} :=
  (contDiff_det_of (fun Z => Z) (fun a b => contDiff_entry a b)).contDiffOn.inv (fun Z hZ => hZ)

theorem contDiffOn_invConjDet {j : ℕ} :
    ContDiffOn ℝ ∞ (fun Z : MJ j => (conj Z.det)⁻¹) {Z | Z.det ≠ 0} :=
  (Complex.conjCLE.contDiff.comp (contDiff_det_of (fun Z => Z) (fun a b => contDiff_entry a b))).contDiffOn.inv
    (fun Z hZ => by simpa using hZ)

section zop2

variable (hR : ZOpRd)
include hR

theorem zop_AZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (u : ℂ) : ZOp (E := E) (AZ k r j m hm hmj u) := by
  classical
  unfold AZ
  refine zop_sum _ (fun c _ => ?_)
  split_ifs
  · exact (zop_qminG hR k r j _ _ u).cmul
      (contDiff_det_of _ (fun a l => contDiff_cZ _ _)).contDiffOn
  · exact zop_zero

theorem zop_AvZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (ell : ℂ) : ZOp (E := E) (AvZ k r j m hm hmj ell) := by
  classical
  unfold AvZ
  refine zop_sum _ (fun c _ => ?_)
  split_ifs
  · exact (zop_qminG hR k r j _ _ _).cmul
      (contDiff_det_of _ (fun a l => contDiff_cvZ k r _ _)).contDiffOn
  · exact zop_zero

theorem zop_Aform (k r j : ℕ) (hj : j + 1 ≤ r) (l : C.Letter) (e : Fin 2) :
    ZOp (E := E) (Aform k r j hj l e) := by
  unfold Aform
  split_ifs
  · exact zop_zero
  · exact (zop_AZ hR _ _ _ _ _ _ _).cmul contDiffOn_invDet
  · exact (zop_AvZ hR _ _ _ _ _ _ _).cmul contDiffOn_invConjDet

end zop2
end Formalism.FourierDecayAlt.P.WirtingerOperators
end
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

variable {k : ℕ}

def psiInt {ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (B1 : B.RealPlaceData k (ρ + 1) Wp Wq) (f1 : B.Mat k (ρ + 1) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (γ : B.Mat k ρ) (b b' : B.Mat k (1 + ρ)) : Wq →L[ℂ] Wp :=
  (psi k (ρ + 1) B1.z cStd (D.castM (Nat.add_comm 1 ρ) b) *
      star (psi k (ρ + 1) B1.z' cStd (D.castM (Nat.add_comm 1 ρ) b'))) •
    f1 ((D.castM (Nat.add_comm 1 ρ) b)⁻¹ * D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) *
      D.castM (Nat.add_comm 1 ρ) b')

theorem levA_inv (ρ : ℕ) {h : B.Mat k ρ} (hh : IsUnit h.det) :
    (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ h))⁻¹ = D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ h⁻¹) := by
  rw [← castM_inv', LongWeylElement.lev_inv _ hh]

theorem pt_eq {ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (B1 : B.RealPlaceData k (ρ + 1) Wp Wq) (B0 : B.RealPlaceData k ρ Wp Wq)
    (hz : B1.z = D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z))
    (hz' : B1.z' = D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ B0.z'))
    (hπ : ∀ y : B.Mat k ρ, B0.π y = B1.π (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ y)))
    (hπ' : ∀ y : B.Mat k ρ, B0.π' y = B1.π' (D.castM (Nat.add_comm 1 ρ) (ιLev k 1 ρ y)))
    (f1 : B.Mat k (ρ + 1) → (Wq →L[ℂ] Wp)) (c : ℂ) (γ : B.Mat k ρ)
    (h0 y h0' y' : Mt k ρ) (a a' : Mt k (1 + ρ))
    (hh0 : Matrix.of h0 ∈ UWset k ρ B0.z) (hy : Matrix.of y ∈ Nset k ρ)
    (hh0' : Matrix.of h0' ∈ UWset k ρ B0.z') (hy' : Matrix.of y' ∈ Nset k ρ)
    (ha : Matrix.of a ∈ Nset k (1 + ρ)) (ha' : Matrix.of a' ∈ Nset k (1 + ρ)) :
    JF.integrand B1 f1 (D.castM (Nat.add_comm 1 ρ) (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ))
        ((levA ρ h0, Qm ρ (a, y)), (levA ρ h0', Qm ρ (a', y'))) =
      (psi k ρ B0.z cStd (Matrix.of y) * star (psi k ρ B0.z' cStd (Matrix.of y'))) •
        (B0.π (Matrix.of h0)).comp
          ((psiInt B1 f1 c ((Matrix.of y * Matrix.of h0)⁻¹ * γ * (Matrix.of y' * Matrix.of h0'))
              (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) a))
              (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) a'))).comp
            (B0.π' (Matrix.of h0')⁻¹)) := by
  set κ : 1 + ρ = ρ + 1 := Nat.add_comm 1 ρ with hκ
  have hH := Ux3.hpk_det k ρ
  have hu0 : IsUnit (Matrix.of h0).det := HermitianFormFactor.UH_unit hH hh0.1
  have hu0' : IsUnit (Matrix.of h0').det := HermitianFormFactor.UH_unit hH hh0'.1
  have huy : IsUnit (Matrix.of y).det := HermitianFormFactor.UH_unit hH hy.1
  have huy' : IsUnit (Matrix.of y').det := HermitianFormFactor.UH_unit hH hy'.1
  have hg : IsUnit (ιLev k 1 ρ (Matrix.of y * Matrix.of h0)).det :=
    LongWeylElement.lev_unit _ (by rw [Matrix.det_mul]; exact huy.mul hu0)
  have hg' : IsUnit (ιLev k 1 ρ (Matrix.of y' * Matrix.of h0')).det :=
    LongWeylElement.lev_unit _ (by rw [Matrix.det_mul]; exact huy'.mul hu0')

  have hconj : ∀ (g : B.Mat k (1 + ρ)) (hg : IsUnit g.det) (x : Mt k (1 + ρ)),
      (Matrix.of (conjM g⁻¹ x) : B.Mat k (1 + ρ)) = g⁻¹ * Matrix.of x * g := by
    intro g hg x
    show g⁻¹ * Matrix.of x * g⁻¹⁻¹ = _
    rw [Matrix.nonsing_inv_nonsing_inv _ hg]

  have hψ1 : psi k (ρ + 1) B1.z cStd (Matrix.of (Qm ρ (a, y))) =
      psi k (ρ + 1) B1.z cStd (D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) a))) *
        psi k ρ B0.z cStd (Matrix.of y) := by
    rw [hz, psi_Qm ρ B0.z_mem ha hy, psi_castM, psi_castM, hconj _ hg, psi_conjLev ρ B0.z_mem ha hy hh0]
  have hψ2 : psi k (ρ + 1) B1.z' cStd (Matrix.of (Qm ρ (a', y'))) =
      psi k (ρ + 1) B1.z' cStd (D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) a'))) *
        psi k ρ B0.z' cStd (Matrix.of y') := by
    rw [hz', psi_Qm ρ B0.z'_mem ha' hy', psi_castM, psi_castM, hconj _ hg', psi_conjLev ρ B0.z'_mem ha' hy' hh0']

  have hπa : B1.π (Matrix.of (levA ρ h0)) = B0.π (Matrix.of h0) := (hπ _).symm
  have hπb : B1.π' (Matrix.of (levA ρ h0'))⁻¹ = B0.π' (Matrix.of h0')⁻¹ := by
    rw [levA_apply, levA_inv ρ hu0', ← hπ']

  have hpt : (Matrix.of (levA ρ h0))⁻¹ * (Matrix.of (Qm ρ (a, y)))⁻¹ *
        D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) * Matrix.of (Qm ρ (a', y')) * Matrix.of (levA ρ h0') =
      (D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y * Matrix.of h0))⁻¹) a)))⁻¹ *
        D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c)
          ((Matrix.of y * Matrix.of h0)⁻¹ * γ * (Matrix.of y' * Matrix.of h0'))) *
        D.castM κ (Matrix.of (conjM ((ιLev k 1 ρ (Matrix.of y' * Matrix.of h0'))⁻¹) a')) := by
    rw [hconj _ hg, hconj _ hg']
    show (D.castM κ (ιLev k 1 ρ (Matrix.of h0)))⁻¹ * (D.castM κ (Matrix.of a * ιLev k 1 ρ (Matrix.of y)))⁻¹ *
        D.castM κ (U.mMap k 1 ρ (Matrix.of fun _ _ => c) γ) * D.castM κ (Matrix.of a' * ιLev k 1 ρ (Matrix.of y')) *
        D.castM κ (ιLev k 1 ρ (Matrix.of h0')) = _
    rw [← castM_inv', ← castM_inv', ← castM_inv', ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul,
      ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul, ← Dx2.Tower.castM_mul,
      sgs_alg ρ _ _ _ _ hu0 huy hu0' huy']
  unfold JF.integrand JF.xiP B.rho B.sgs psiInt
  rw [hψ1, hψ2, hπa, hπb, hpt]
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul]
  congr 1
  rw [star_mul']
  ring

end Formalism.FourierDecayAlt.P.PBH
end
end

section

namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section poly

variable {k r : ℕ} {Wq Wq' : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']

theorem ckOn_of_polyOp {d : ℕ} {A : B.Mat k r → (Wq' →L[ℂ] Wq)} (hA : PolyOp d A) : B.CkOn ⊤ (B.GV k r) A := by
  obtain ⟨n, c, L, hc, hAe⟩ := hA
  have hconst : ∀ i, B.CkOn ⊤ (B.GV k r) (fun _ : B.Mat k r => L i) := fun i _ _ =>
    ⟨Set.univ, fun _ => L i, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hterm : ∀ i, B.CkOn ⊤ (B.GV k r) (fun g => c i g • L i) := fun i =>
    (Formalism.FourierDecayAlt.P.CutBP.pd_good_of_poly (Wp := Wq) (Wq := Wq') (hc i)).1 _ (hconst i)
  have hsum : ∀ s : Finset (Fin n), B.CkOn ⊤ (B.GV k r) (fun g => ∑ i ∈ s, c i g • L i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun g _ _ => by simp⟩
    | insert a s ha ih =>
      have e : (fun g => ∑ i ∈ insert a s, c i g • L i) = (fun g => c a g • L a) + fun g => ∑ i ∈ s, c i g • L i := by
        funext g; simp [Finset.sum_insert ha]
      rw [e]; exact Formalism.FourierDecayAlt.P.B4.ckOn_add (hterm a) ih
  have e : A = fun g => ∑ i, c i g • L i := funext hAe
  rw [e]; exact hsum Finset.univ

end poly

structure ShiftAt {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) where
  up : ℕ → ℝ
  up' : ℕ → ℝ
  um : ℕ → ℝ
  um' : ℕ → ℝ
  Wqp : Type
  Wqm : Type
  [iNp : NormedAddCommGroup Wqp]
  [iIp : InnerProductSpace ℂ Wqp]
  [iFp : FiniteDimensional ℂ Wqp]
  [iNm : NormedAddCommGroup Wqm]
  [iIm : InnerProductSpace ℂ Wqm]
  [iFm : FiniteDimensional ℂ Wqm]
  pp : KB.Pl (shP P up up') Wp Wqp
  pm : KB.Pl (shP P um um') Wp Wqm
  Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)
  Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq)
  ApPt : C.LPt → (Wqp →L[ℂ] Wq)
  AmPt : C.LPt → (Wqm →L[ℂ] Wq)
  hzp : pp.T.base.z = p.T.base.z
  hzp' : pp.T.base.z' = p.T.base.z'
  hzm : pm.T.base.z = p.T.base.z
  hzm' : pm.T.base.z' = p.T.base.z'
  polyP : PolyOp n₀ Ap
  polyM : PolyOp n₀ Am
  amaps : AmapsSh p pp pm f Ap Am ApPt AmPt b n₀

attribute [instance] ShiftAt.iNp ShiftAt.iIp ShiftAt.iFp ShiftAt.iNm ShiftAt.iIm ShiftAt.iFm

end

end Formalism.FourierDecayAlt.P.CutBPEq
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

noncomputable section

section defs

variable (k r : ℕ)

def rowsN (l : Fin (r + 1)) (s : Fin (k + 1)) : Fin (r - l.val + k) → Fin (2 * r + k + 1) :=
  fun j => ⟨if j.val < r - l.val + s.val then l.val + j.val else l.val + j.val + 1, by
    have := j.isLt; have := s.isLt; have := l.isLt; split_ifs <;> omega⟩

def NL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1))
    (u : ℂ) (f : Q.Mx k r → E) : Q.Mx k r → E :=
  fun g => ∑ s : Fin (k + 1), ∑ t : Fin (k + 1),
    (((-1 : ℂ) ^ ((s : ℕ) + (t : ℕ))) * herm (Hpk k r) (bvec (wI k r s)) z' * (g⁻¹ *ᵥ z) (wI k r t)) •
      qminorOp (Q.EH k r) (rowsN k r l s) (rowsN k r l t) u f g

def FN {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (J : Q.Mx k r → E) (l : Fin (r + 1)) : Q.Fn k r E :=
  Q.resG k r (Fin.last r) (NL k r z z' l (Q.uC k r l Y) J)

end defs

def JDRBeta : Prop :=
  ∀ k r : ℕ, ∃ σ : ℂ, σ ≠ 0 ∧ ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (z z' : Fin (2 * r + k + 1) → ℂ)
    (Y : ℂ) (f : Q.Mx k r → E), inWb k r z → ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
      rhatOp k r z z' Y f (Q.wCell k r (Fin.last r) c * g) =
        (σ * starRingEnd ℂ (∏ a, c a)) • NL k r z z' 0 (Q.uC k r 0 Y) f (Q.wCell k r (Fin.last r) c * g)

def JDRTop : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J (Fin.last r) c g = -Q.QL k r z z' (Fin.last r) Y 1 0 (Q.resG k r (Fin.last r) J) c g

def JDRStepA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (hr : 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J ⟨r - 1, by omega⟩ c g =
        (Y • FN k r z z' Y J (Fin.last r) + Q.crd (Formalism.QuantumDeterminants.pOp ⟨r - 1, by omega⟩) (FN k r z z' Y J (Fin.last r)) -
          Q.crd (Formalism.QuantumDeterminants.ciOp ⟨r - 1, by omega⟩) (Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J))) c g

def JDRStepB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ (l : ℕ) (hl : l + 2 ≤ r),
    ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J ⟨l, by omega⟩ c g =
        (Y • FN k r z z' Y J ⟨l + 1, by omega⟩ + Q.crd (Formalism.QuantumDeterminants.pOp ⟨l, by omega⟩) (FN k r z z' Y J ⟨l + 1, by omega⟩) -
          Q.crd (Formalism.QuantumDeterminants.cOp ⟨l + 1, by omega⟩) (Q.crd (Formalism.QuantumDeterminants.ciOp ⟨l, by omega⟩) (FN k r z z' Y J ⟨l + 2, by omega⟩))) c g

def JDRChainP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq))
    (D : Set (Q.Mx k r)) (Y : ℂ), inWb k r z → inWb k r z' → Q.IsDom k r z z' 0 D →
    ∀ J ∈ Q.FFl k r z z' π π' 0 D, ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r), Q.wCell k r (Fin.last r) c * g ∈ D →
      FN k r z z' Y J 0 c g =
        -(Q.QL k r z z' (Fin.last r) Y 1 0 (Q.crd (Q.cmp (Q.vAB r Y r) 0) (Q.resG k r (Fin.last r) J)) +
          Q.QL k r z z' (Fin.last r) Y 1 1 (Q.crd (Q.cmp (Q.vAB r Y r) 1) (Q.resG k r (Fin.last r) J))) c g

def JDRConseq : Prop := JDRTop → JDRStepA → JDRStepB → JDRChainP

theorem jDRRadP_of_parts (hB : JDRBeta) (hT : JDRTop) (hA : JDRStepA) (hS : JDRStepB) (hC : JDRConseq) :
    JDRRadP := by
  have hCh := hC hT hA hS
  intro k r
  obtain ⟨σ, hσ, hBσ⟩ := hB k r
  refine ⟨-σ⁻¹, ?_⟩
  intro Wp Wq _ _ _ _ z z' π π' D Y hz hz' hD J hJ c hc g hg hx
  have h1 := hBσ (Wq →L[ℂ] Wp) z z' Y J hz c hc g hg
  have h2 := congrArg Neg.neg (hCh Wp Wq k r z z' π π' D Y hz hz' hD J hJ c hc g hg hx)
  clear hBσ hCh hB hT hA hS hC
  simp only [Pi.neg_apply, neg_neg] at h2
  simp only [rhGrp, dMul, drbF, Pi.add_apply] at h2 ⊢
  rw [← h2]
  simp only [FN, Q.resG, h1]
  simp only [smul_smul, smul_neg, neg_smul]
  match_scalars <;> field_simp <;> ring

end

end Formalism.FourierDecayAlt.P.CutMP
end
