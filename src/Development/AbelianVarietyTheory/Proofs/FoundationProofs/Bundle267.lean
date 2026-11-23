module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle258
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle257
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle094
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTransvectionVectorsNeighbour
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle252
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle259
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.translate_modifiedSigma_two_mul_at_zero : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ, P ∉ Λ → U1 Λ (2 * P) (sgStar Λ) 0 = -(wpD Λ P) * U1 Λ P (sgStar Λ) 0 ^ 4 := by
  first | exact @GlobalTheory.SigmaDuplication.U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four | exact GlobalTheory.SigmaDuplication.U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four | (intros; apply GlobalTheory.SigmaDuplication.U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_weierstrassPSeries_and_sigmaStarQuotientSeries : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∃ P : PowerSeries ℂ, IsWpSer (g2 Λ) (g3 Λ) P ∧ ∀ v, v ∉ Λ → PowerSeries.X ^ 2 * PowerSeries.mk (coef1 (sqTh Λ v)) = PowerSeries.mk (coef1 (sgStar Λ)) ^ 2 * lineSer P (wpF Λ v) := by
  first | exact @GlobalTheory.WpSeries.exists_wpSer | exact GlobalTheory.WpSeries.exists_wpSer | (intros; apply GlobalTheory.WpSeries.exists_wpSer <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

theorem sgStar_cube_det_cplx : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0) := by
  intro Λ hΛ v hv z
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hΛL : Λ = L.lattice.toAddSubgroup := AddSubgroup.ext hL
  have hσ : sgStar Λ = Formalism.L2.Th1.F.sgStar L := by rw [hΛL]; exact GlobalTheory.JetsGenusOne.sgStar_eq L
  have hwp : wpF Λ = L.weierstrassP := funext (GlobalTheory.OddTheta.wpF_eq L Λ hL)
  have hsd : Differentiable ℂ (sgStar Λ) := hΛ.differentiable
  have hopen : IsOpen ((Λ : Set ℂ)ᶜ) := by
    have : (Λ : Set ℂ) = (L.lattice : Set ℂ) := Set.ext fun w => hL w
    rw [this]; exact L.isClosed_lattice.isOpen_compl
  have hB : ∀ w, w ∉ Λ → colB Λ v w = sgStar Λ w ^ 3 * L.weierstrassP w := by
    intro w hw
    rw [colB, hΛ.sqTh_eq hv hw, ← hwp]
    ring
  have hC : ∀ w, w ∉ Λ → colC Λ v w = sgStar Λ w ^ 3 * L.derivWeierstrassP w := by
    intro w hw
    have hwL : w ∉ L.lattice := fun h => hw ((hL w).2 h)
    have hpd : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
      have h1 : DifferentiableAt ℂ L.weierstrassP w :=
        L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hwL)
      have h2 := h1.hasDerivAt
      rwa [L.deriv_weierstrassP] at h2
    have hev : sqTh Λ v =ᶠ[nhds w] fun u => sgStar Λ u ^ 2 * (L.weierstrassP u - wpF Λ v) := by
      filter_upwards [hopen.mem_nhds hw] with u hu
      rw [hΛ.sqTh_eq hv hu, hwp]
    have hd : HasDerivAt (fun u => sgStar Λ u ^ 2 * (L.weierstrassP u - wpF Λ v))
        ((2 : ℕ) * sgStar Λ w ^ (2 - 1) * deriv (sgStar Λ) w * (L.weierstrassP w - wpF Λ v) +
          sgStar Λ w ^ 2 * L.derivWeierstrassP w) w :=
      ((hsd w).hasDerivAt.pow 2).mul (hpd.sub_const _)
    rw [colC, hev.deriv_eq, hd.deriv, hΛ.sqTh_eq hv hw, hwp]
    push_cast
    ring
  have hoff : ∀ y : Fin 3 → ℂ, (∀ i, y i ∉ Λ) →
      Matrix.det (Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j (y i)) =
        2 * sgStar Λ (y 0 + y 1 + y 2) * sgStar Λ (y 0 - y 1) * sgStar Λ (y 1 - y 2) * sgStar Λ (y 2 - y 0) := by
    intro y hy
    have h := Formalism.L2.Th1.F.sgStarThree L (y 0) (y 1) (y 2)
      (fun h => hy 0 ((hL _).2 h)) (fun h => hy 1 ((hL _).2 h)) (fun h => hy 2 ((hL _).2 h))
    rw [← hσ] at h
    rw [Matrix.det_fin_three] at h ⊢
    simp [Matrix.vecHead, Matrix.vecTail] at h ⊢
    rw [hB _ (hy 0), hB _ (hy 1), hB _ (hy 2), hC _ (hy 0), hC _ (hy 1), hC _ (hy 2)]
    simp only [colA]
    linear_combination h
  have hcA : Continuous (colA Λ) := by
    have := hsd.continuous
    unfold colA; fun_prop
  have hcB : Continuous (colB Λ v) := by
    have := (hΛ.differentiable_sqTh v).continuous
    have := hsd.continuous
    unfold colB; fun_prop
  have hcC : Continuous (colC Λ v) := by
    have h1 : Continuous (deriv (sqTh Λ v)) :=
      ((hΛ.differentiable_sqTh v).contDiff (n := 1)).continuous_deriv le_rfl
    have h2 : Continuous (deriv (sgStar Λ)) := (hsd.contDiff (n := 1)).continuous_deriv le_rfl
    have := (hΛ.differentiable_sqTh v).continuous
    have := hsd.continuous
    unfold colC; fun_prop
  have hcL : Continuous fun y : Fin 3 → ℂ =>
      Matrix.det (Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j (y i)) := by
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.of_apply]
    fin_cases j
    · exact hcA.comp (continuous_apply i)
    · exact hcB.comp (continuous_apply i)
    · exact hcC.comp (continuous_apply i)
  have hcR : Continuous fun y : Fin 3 → ℂ =>
      2 * sgStar Λ (y 0 + y 1 + y 2) * sgStar Λ (y 0 - y 1) * sgStar Λ (y 1 - y 2) * sgStar Λ (y 2 - y 0) := by
    have := hsd.continuous
    fun_prop
  have hdense : Dense {y : Fin 3 → ℂ | ∀ i, y i ∉ Λ} := by
    have := dense_pi (Set.univ : Set (Fin 3)) (s := fun _ => ((Λ : Set ℂ)ᶜ)) fun _ _ => hΛ.dense_compl
    convert this using 1
    ext y; simp
  exact congrFun (Continuous.ext_on hdense hcL hcR fun y hy => hoff y hy) z

end GlobalTheory.FrobStick
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

namespace GlobalTheory.FrobStick

theorem hasSubst_line {R : Type} [CommRing R] (t : Fin 3 → R) :
    MvPowerSeries.HasSubst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
    rw [map_mul]; exact mul_eq_zero_of_right _ (PowerSeries.constantCoeff_X (R := R))

theorem subst_line_subst {R : Type} [CommRing R] (t : Fin 3 → R) (a : MvPowerSeries (Fin 3) R)
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries R) :
    (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (PowerSeries.subst a f : MvPowerSeries (Fin 3) R) : PowerSeries R) =
      PowerSeries.subst (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) a : PowerSeries R) f := by
  have has : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => ha
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply has (hasSubst_line t)]
  rfl

theorem subst_C_mul_X {R : Type} [CommRing R] (c : R) (f : PowerSeries R) :
    PowerSeries.subst (PowerSeries.C c * PowerSeries.X : PowerSeries R) f = PowerSeries.rescale c f := by
  rw [PowerSeries.rescale_eq_subst, PowerSeries.smul_eq_C_mul]

end GlobalTheory.FrobStick

namespace GlobalTheory.FrobStick

theorem defect_line (R : Type) [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R)
    (t : Fin 3 → R) :
    (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (GlobalTheory.FrobStick.defect f s) : PowerSeries R) =
      Matrix.det (Matrix.of fun i j => PowerSeries.rescale (t i) (f j)) -
        2 * PowerSeries.rescale (t 0 + t 1 + t 2) s * PowerSeries.rescale (t 0 - t 1) s *
          PowerSeries.rescale (t 1 - t 2) s * PowerSeries.rescale (t 2 - t 0) s := by
  have hb := hasSubst_line t
  have hlin : ∀ (a : MvPowerSeries (Fin 3) R) (c : R), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) a =
        (PowerSeries.C c * PowerSeries.X : PowerSeries R) → ∀ g : PowerSeries R,
      (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
        (PowerSeries.subst a g : MvPowerSeries (Fin 3) R) : PowerSeries R) = PowerSeries.rescale c g := by
    intro a c ha h g
    rw [subst_line_subst t a ha, h, subst_C_mul_X]
  have hX : ∀ i, MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) = (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R) :=
    fun i => MvPowerSeries.subst_X hb i
  unfold defect
  rw [← MvPowerSeries.coe_substAlgHom hb]
  simp only [map_sub, map_mul, AlgHom.map_det]

  have hmat : (MvPowerSeries.substAlgHom hb).mapMatrix
      (Matrix.of fun i j => (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) (f j) :
        MvPowerSeries (Fin 3) R)) = Matrix.of fun i j => PowerSeries.rescale (t i) (f j) := by
    refine Matrix.ext fun i j => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPowerSeries.coe_substAlgHom]
    exact hlin _ _ (MvPowerSeries.constantCoeff_X i) (hX i) _
  rw [hmat, map_ofNat]
  simp only [MvPowerSeries.coe_substAlgHom]
  have h3 : MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) =
      (PowerSeries.C (t 0 + t 1 + t 2) * PowerSeries.X : PowerSeries R) := by
    rw [MvPowerSeries.subst_add hb, MvPowerSeries.subst_add hb, hX, hX, hX, map_add (f := _), map_add (f := _), add_mul, add_mul]
  have hd : ∀ i j : Fin 3, MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R))
      (MvPowerSeries.X i - MvPowerSeries.X j : MvPowerSeries (Fin 3) R) =
      (PowerSeries.C (t i - t j) * PowerSeries.X : PowerSeries R) := by
    intro i j
    rw [MvPowerSeries.subst_sub hb, hX, hX, map_sub, sub_mul]
  have c3 : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) = 0 := by
    simp
  have cd : ∀ i j : Fin 3, MvPowerSeries.constantCoeff
      (MvPowerSeries.X i - MvPowerSeries.X j : MvPowerSeries (Fin 3) R) = 0 := by
    intro i j; simp
  rw [hlin _ _ c3 h3, hlin _ _ (cd 0 1) (hd 0 1), hlin _ _ (cd 1 2) (hd 1 2), hlin _ _ (cd 2 0) (hd 2 0)]

end GlobalTheory.FrobStick
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

def entireRing : Subring (ℂ → ℂ) where
  carrier := {F | Differentiable ℂ F}
  mul_mem' := fun {F G} hF hG => by
    exact (hF.mul hG : Differentiable ℂ (fun z => F z * G z))
  one_mem' := by simpa using (differentiable_const (1 : ℂ) : Differentiable ℂ fun _ : ℂ => (1 : ℂ))
  add_mem' := fun {F G} hF hG => by
    exact (hF.add hG : Differentiable ℂ (fun z => F z + G z))
  zero_mem' := by simpa using (differentiable_const (0 : ℂ) : Differentiable ℂ fun _ : ℂ => (0 : ℂ))
  neg_mem' := fun {F} hF => by
    exact (hF.neg : Differentiable ℂ (fun z => -F z))

theorem tay_coeff (F : ℂ → ℂ) (n : ℕ) : PowerSeries.coeff n (tay F) = coef1 F n := by
  simp [tay, PowerSeries.coeff_mk]

def tayHom : entireRing →+* PowerSeries ℂ where
  toFun F := tay F
  map_one' := by
    ext n
    rw [tay_coeff, PowerSeries.coeff_one]
    exact GlobalTheory.SerTransport.taylorCoeff_const_function 1 n
  map_mul' F G := by
    ext n
    rw [tay_coeff, PowerSeries.coeff_mul]
    have := GlobalTheory.SerTransport.taylorCoeff_mul_entire F.2 G.2 n
    simp only [tay_coeff]
    exact this
  map_zero' := by
    ext n
    rw [tay_coeff, map_zero]
    have := GlobalTheory.SerTransport.taylorCoeff_const_function 0 n
    simp only [ite_self] at this
    exact this
  map_add' F G := by
    ext n
    rw [map_add (f := _), tay_coeff, tay_coeff, tay_coeff]
    exact GlobalTheory.SerTransport.taylorCoeff_add_entire F.2 G.2 n

def scaleE (β : ℂ) (F : entireRing) : entireRing :=
  ⟨fun z => F.1 (β * z), F.2.comp (differentiable_id.const_mul β)⟩

theorem rescale_tayHom (β : ℂ) (F : entireRing) :
    PowerSeries.rescale β (tayHom F) = tayHom (scaleE β F) := by
  ext n
  rw [PowerSeries.coeff_rescale]
  show β ^ n * PowerSeries.coeff n (tay F.1) = PowerSeries.coeff n (tay (fun z => F.1 (β * z)))
  rw [tay_coeff, tay_coeff, GlobalTheory.SerTransport.taylorCoeff_scale_entire F.2]

end GlobalTheory.FrobStick

namespace GlobalTheory.FrobStick

theorem tay_defect_eq_zero : (∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K), (∀ t : Fin 3 → K, (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) → Φ = 0) → (∀ (R : Type) [CommRing R] (f : Fin 3 → PowerSeries R) (s : PowerSeries R) (t : Fin 3 → R), (MvPowerSeries.subst (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries R)) (GlobalTheory.FrobStick.defect f s) : PowerSeries R) = Matrix.det (Matrix.of fun i j => PowerSeries.rescale (t i) (f j)) - 2 * PowerSeries.rescale (t 0 + t 1 + t 2) s * PowerSeries.rescale (t 0 - t 1) s * PowerSeries.rescale (t 1 - t 2) s * PowerSeries.rescale (t 2 - t 0) s) → (∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → ∀ z : Fin 3 → ℂ, Matrix.det (Matrix.of fun i j => ![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j (z i)) = 2 * sgStar Λ (z 0 + z 1 + z 2) * sgStar Λ (z 0 - z 1) * sgStar Λ (z 1 - z 2) * sgStar Λ (z 2 - z 0)) → ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ v : ℂ, v ∉ Λ → GlobalTheory.FrobStick.defect (fun j => GlobalTheory.FrobStick.tay (![GlobalTheory.FrobStick.colA Λ, GlobalTheory.FrobStick.colB Λ v, GlobalTheory.FrobStick.colC Λ v] j)) (GlobalTheory.FrobStick.tay (sgStar Λ)) = 0 := by
  intro hLine hRestr hId Λ hL v hv
  have hS : Differentiable ℂ (sgStar Λ) := hL.differentiable
  have hQ : Differentiable ℂ (sqTh Λ v) := hL.differentiable_sqTh v
  have hdS : Differentiable ℂ (deriv (sgStar Λ)) := fun z => ((hS.analyticAt z).deriv).differentiableAt
  have hdQ : Differentiable ℂ (deriv (sqTh Λ v)) := fun z => ((hQ.analyticAt z).deriv).differentiableAt
  have hA : Differentiable ℂ (colA Λ) :=
    (hS.pow 3 : Differentiable ℂ (fun z => sgStar Λ z ^ 3))
  have hB : Differentiable ℂ (colB Λ v) :=
    (hS.mul (hQ.add ((hS.pow 2).const_mul (wpF Λ v))) :
      Differentiable ℂ (fun z => sgStar Λ z * (sqTh Λ v z + wpF Λ v * sgStar Λ z ^ 2)))
  have hC : Differentiable ℂ (colC Λ v) :=
    ((hS.mul hdQ).sub ((hdS.const_mul 2).mul hQ) :
      Differentiable ℂ (fun z => sgStar Λ z * deriv (sqTh Λ v) z - 2 * deriv (sgStar Λ) z * sqTh Λ v z))
  let a : Fin 3 → entireRing := ![⟨colA Λ, hA⟩, ⟨colB Λ v, hB⟩, ⟨colC Λ v, hC⟩]
  let s : entireRing := ⟨sgStar Λ, hS⟩
  have ha : ∀ j, tay (![colA Λ, colB Λ v, colC Λ v] j) = tayHom (a j) := by
    intro j; fin_cases j <;> rfl
  apply hLine ℂ
  intro t
  rw [hRestr]
  have e1 : (Matrix.of fun i j => PowerSeries.rescale (t i) (tay (![colA Λ, colB Λ v, colC Λ v] j))) =
      tayHom.mapMatrix (Matrix.of fun i j => scaleE (t i) (a j)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, ha, rescale_tayHom]
  have es : tay (sgStar Λ) = tayHom s := rfl
  rw [e1, ← RingHom.map_det, es, rescale_tayHom, rescale_tayHom, rescale_tayHom, rescale_tayHom,
    show (2 : PowerSeries ℂ) = tayHom 2 from (map_ofNat tayHom 2).symm,
    ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_sub]
  convert map_zero tayHom
  refine Subtype.ext (funext fun z => ?_)
  let φ : entireRing →+* ℂ := (Pi.evalRingHom (fun _ : ℂ => ℂ) z).comp entireRing.subtype
  rw [ZeroMemClass.coe_zero, Pi.zero_apply]
  have hφ : ∀ x : entireRing, (x : ℂ → ℂ) z = φ x := fun x => rfl
  rw [hφ]
  rw [map_sub, RingHom.map_det, map_mul, map_mul, map_mul, map_mul, map_ofNat]
  have hm : φ.mapMatrix (Matrix.of fun i j => scaleE (t i) (a j)) =
      Matrix.of fun i j => ![colA Λ, colB Λ v, colC Λ v] j ((fun i => t i * z) i) := by
    ext i j; fin_cases j <;> rfl
  rw [hm, hId Λ hL v hv (fun i => t i * z)]
  change _ - 2 * sgStar Λ ((t 0 + t 1 + t 2) * z) * sgStar Λ ((t 0 - t 1) * z) * sgStar Λ ((t 1 - t 2) * z) *
    sgStar Λ ((t 2 - t 0) * z) = 0
  simp only [add_mul, sub_mul, sub_self]

end GlobalTheory.FrobStick
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick.SubstLog

variable {p : ℕ} [Fact p.Prime]

theorem cc_lg (g : GL3Theta.G1 p) {x : MvPowerSeries (Fin 3) ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) :
    MvPowerSeries.constantCoeff (g.lg x) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hx _ (GlobalTheory.SerTransport.const_l g)

theorem cc_pt {g : GL3Theta.G1 p} (hg : g.Ok) {x : MvPowerSeries (Fin 3) ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) : MvPowerSeries.constantCoeff (g.pt x) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hx _ hg.2.2.1

theorem lg_pt {g : GL3Theta.G1 p} (hg : g.Ok) {x : MvPowerSeries (Fin 3) ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) : g.lg (g.pt x) = x := by
  have hx' : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  have he : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hg.2.2.1
  unfold GL3Theta.G1.lg GL3Theta.G1.pt
  rw [← PowerSeries.subst_comp_subst_apply he hx', hg.2.2.2, PowerSeries.subst_X hx']

theorem cc_sum (g : GL3Theta.G1 p) {x y : MvPowerSeries (Fin 3) ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (g.lg x + g.lg y) = 0 := by
  rw [map_add (f := _), cc_lg g hx, cc_lg g hy, add_zero]

theorem cc_diff (g : GL3Theta.G1 p) {x y : MvPowerSeries (Fin 3) ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (g.lg x - g.lg y) = 0 := by
  rw [map_sub, cc_lg g hx, cc_lg g hy, sub_zero]

theorem cc_Cl (g : GL3Theta.G1 p) (c : ℂ_[p]) : PowerSeries.constantCoeff (PowerSeries.C c * g.l) = 0 := by
  rw [map_mul, GlobalTheory.SerTransport.const_l, mul_zero]

theorem subst_Cl (g : GL3Theta.G1 p) (c : ℂ_[p]) {w : MvPowerSeries (Fin 3) ℂ_[p]}
    (hw : MvPowerSeries.constantCoeff w = 0) (h : PowerSeries ℂ_[p]) :
    (PowerSeries.subst w (PowerSeries.subst (PowerSeries.C c * g.l) h : PowerSeries ℂ_[p]) :
        MvPowerSeries (Fin 3) ℂ_[p]) =
      PowerSeries.subst (MvPowerSeries.C c * g.lg w) h := by
  have hw' : PowerSeries.HasSubst w := PowerSeries.HasSubst.of_constantCoeff_zero hw
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' (cc_Cl g c)) hw',
    PowerSeries.subst_mul hw', PowerSeries.subst_C]
  rfl

theorem hom_subst {a : Fin 3 → MvPowerSeries (Fin 3) ℂ_[p]} (ha : MvPowerSeries.HasSubst a)
    {y : MvPowerSeries (Fin 3) ℂ_[p]} (hy : MvPowerSeries.constantCoeff y = 0) (h : PowerSeries ℂ_[p]) :
    MvPowerSeries.substAlgHom (R := ℂ_[p]) ha (PowerSeries.subst y h) =
      PowerSeries.subst (MvPowerSeries.substAlgHom (R := ℂ_[p]) ha y) h := by
  rw [MvPowerSeries.coe_substAlgHom]
  exact MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hy).const ha h

theorem formula_at {a : Fin 3 → MvPowerSeries (Fin 3) ℂ_[p]}
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : Fin 3 → PowerSeries ℂ_[p]) (s : PowerSeries ℂ_[p])
    (h : GlobalTheory.FrobStick.defect f s = 0) :
    Matrix.det (Matrix.of fun i j => (PowerSeries.subst (a i) (f j) : MvPowerSeries (Fin 3) ℂ_[p])) =
      2 * PowerSeries.subst (a 0 + a 1 + a 2) s * PowerSeries.subst (a 0 - a 1) s *
        PowerSeries.subst (a 1 - a 2) s * PowerSeries.subst (a 2 - a 0) s := by
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hX : ∀ i, MvPowerSeries.substAlgHom (R := ℂ_[p]) ha (MvPowerSeries.X i) = a i := fun i => by
    rw [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X ha]
  have h1 := congrArg (MvPowerSeries.substAlgHom (R := ℂ_[p]) ha) (sub_eq_zero.mp h)
  rw [AlgHom.map_det, map_mul, map_mul, map_mul, map_mul, map_ofNat, hom_subst ha (by simp),
    hom_subst ha (by simp), hom_subst ha (by simp), hom_subst ha (by simp)] at h1
  simp only [map_add (f := _), map_sub, hX] at h1
  rw [← h1]
  congr 1
  ext1 i j
  simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
  rw [hom_subst ha (by simp), hX]

theorem subst_log_formula : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → MvPowerSeries.constantCoeff (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 ∧ ∀ (c : ℂ_[p]) (f : Fin 3 → PowerSeries ℂ_[p]) (s : PowerSeries ℂ_[p]), GlobalTheory.FrobStick.defect f s = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) (f j) : PowerSeries ℂ_[p]) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 1) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) * PowerSeries.subst (g.sub (GL3Theta.Xv 2) (GL3Theta.Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) (PowerSeries.subst (PowerSeries.C c * g.l) s : PowerSeries ℂ_[p]) := by
  intro p _ g hg
  have hX : ∀ i : Fin 3, MvPowerSeries.constantCoeff (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have h01 : MvPowerSeries.constantCoeff
      (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := cc_pt hg (cc_sum g (hX 0) (hX 1))
  have hs : MvPowerSeries.constantCoeff
      (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    cc_pt hg (cc_sum g h01 (hX 2))
  have hd : ∀ i j : Fin 3, MvPowerSeries.constantCoeff
      (g.sub (GL3Theta.Xv i) (GL3Theta.Xv j) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    fun i j => cc_pt hg (cc_diff g (hX i) (hX j))
  refine ⟨hs, hd 0 1, hd 1 2, hd 2 0, fun c f s h => ?_⟩
  have ld : ∀ i j : Fin 3, g.lg (g.sub (GL3Theta.Xv i) (GL3Theta.Xv j) : MvPowerSeries (Fin 3) ℂ_[p]) =
      g.lg (GL3Theta.Xv i) - g.lg (GL3Theta.Xv j) := fun i j => lg_pt hg (cc_diff g (hX i) (hX j))
  have l01 : g.lg (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) =
      g.lg (GL3Theta.Xv 0) + g.lg (GL3Theta.Xv 1) := lg_pt hg (cc_sum g (hX 0) (hX 1))
  have ls : g.lg (g.add (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1)) (GL3Theta.Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) =
      g.lg (GL3Theta.Xv 0) + g.lg (GL3Theta.Xv 1) + g.lg (GL3Theta.Xv 2) := by
    rw [← l01]; exact lg_pt hg (cc_sum g h01 (hX 2))
  have key := formula_at (a := fun i => MvPowerSeries.C c * g.lg (GL3Theta.Xv i))
    (fun i => by rw [map_mul, cc_lg g (hX i), mul_zero]) f s h
  simp only [subst_Cl g c (hX _), subst_Cl g c hs, subst_Cl g c (hd _ _), ld, ls, mul_add, mul_sub]
  exact key

end GlobalTheory.FrobStick.SubstLog
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_local_component_unitary_matrix : ∀ (D : D7) (n q : ℕ), q.Prime → ∀ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 → ∃ g : GA D n, (∀ p : ℕ, p.Prime → p ≠ q → TrivAt D p (g : GL (Fin n) (AE D))) ∧ ∀ (h : GA D n) (B C : Lat D n), Moves D (h : GL (Fin n) (AE D)) B → EqAway D q B C → SAt D q s B C → Moves D ((g * h : GA D n) : GL (Fin n) (AE D)) C := by
  first | exact @GlobalTheory.LocalComponent.exists_local_component | exact GlobalTheory.LocalComponent.exists_local_component | (intros; apply GlobalTheory.LocalComponent.exists_local_component <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_transvection_vectors_neighbour : ∀ (D : D7) (n q : ℕ), q.Prime → ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal → (q : 𝓞 D.host.E) ∈ P → (∀ a ∈ P, sgO D a ∈ P) → ∀ (B : Lat D n) (x : Fin n → D.host.E), SD D B → NbD D P B x → ∃ (b x' : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), B = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {b} ∧ nbr D B x = nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {x'} ∧ (∀ p ∈ P, p • b ∈ nbM D B x ∧ p • x' ∈ nbM D B x) ∧ ¬ IntE D (hE D b x') ∧ NbD D P B (b + x') ∧ nbM D B (b + x') = nbM D B x ∧ lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x') (b + x') = 0 ∧ Nat.Coprime m q ∧ (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) ∧ ∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x')) = (p : D.host.E) := by
  first | exact @GlobalTheory.NbVec.exists_vectors | exact GlobalTheory.NbVec.exists_vectors | (intros; apply GlobalTheory.NbVec.exists_vectors <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

theorem _root_.GlobalTheory.T.torsionMap_carries_torus_lattices : ∀ (D : D7), admG1 D → galStar D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), FixK D M ρ → DataIn D (tor0 D cc δ) M → (∀ t, InRationalLattice (lamOf D cc δ) t → t ∉ (lamOf D cc δ) → wpF (lamOf D cc δ) t ∈ M ∧ wpD (lamOf D cc δ) t ∈ M) → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → ∀ n : ℕ, 0 < n → (∀ x x' y y', AdpB D (tor0 D cc δ) M ρ b n x x' → AdpB D (tor0 D cc δ) M ρ b n y y' → AdpB D (tor0 D cc δ) M ρ b n (x - y) (x' - y')) ∧ (∀ (t : VC D N N') (m : ℕ), 0 < m → m • t ∈ LaB D (tor0 D cc δ) b → ∃ t', AdpB D (tor0 D cc δ) M ρ b n t t') ∧ ∀ (k : ℕ) (Y : Set (Matrix (Fin N') (Fin N) D.host.E)), 0 < k → k ∣ n → Comm D b k Y → (∀ x ∈ LaS D (tor0 D cc δ) Y, ∃ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ (∀ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y, ∃ x ∈ LaS D (tor0 D cc δ) Y, AdpB D (tor0 D cc δ) M ρ b n x x') ∧ ∀ x x', AdpB D (tor0 D cc δ) M ρ b n x x' → (x ∈ LaS D (tor0 D cc δ) Y ↔ x' ∈ LaS D (torConj D (tor0 D cc δ) M ρ) Y) := by
  first | exact @GlobalTheory.ThetaConj.adpB_lattices | exact GlobalTheory.ThetaConj.adpB_lattices | (intros; apply GlobalTheory.ThetaConj.adpB_lattices <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

theorem _root_.GlobalTheory.T.weilOperator_conj_heisenberg_moved_lattice : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (h k : GA D N) (h' k' : GA D N') (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (k : GL (Fin N) (AE D)) L₁ → Moves D (k' : GL (Fin N') (AE D)) L₁' → Moves D ((h * k : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((h' * k' : GA D N') : GL (Fin N') (AE D)) L₂' → ∀ x ∈ La D (tor0 D cc δ) L₁ L₁', ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ x' ∈ La D (tor0 D cc δ) L₂ L₂', W.Om h h' (Wd D (tor0 D cc δ) x F) = Wd D (tor0 D cc δ) x' (W.Om h h' F) := by
  first | exact @GlobalTheory.WeilEquiv.om_wd_moved | exact GlobalTheory.WeilEquiv.om_wd_moved | (intros; apply GlobalTheory.WeilEquiv.om_wd_moved <;> assumption)
end
