module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SigROneTmul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle004
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MeasurePrjFPreimage
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

@[expose] public section

section

noncomputable section

open scoped TensorProduct
open Matrix NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

namespace MassDataMassesW.NRatW

def RatN {E : Type} [Field E] {n r : ℕ} (e K : Fin r → Fin n → E) (M : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ a : Fin r, (M - 1) *ᵥ e a ∈ Submodule.span E (e '' {b | b < a})) ∧
  ∀ y : Fin n → E, (∀ a, ∑ j, K a j * y j = 0) → (M - 1) *ᵥ y ∈ Submodule.span E (Set.range e)

section Spec

variable {D : D7} (X : HidaSetting D)

def Kf {r : ℕ} (x : Fin r → Fin X.B.I.n → X.B.I.E) : Fin r → Fin X.B.I.n → X.B.I.E :=
  fun a j => ∑ i, star (x a i) * X.B.I.J i j

theorem Kf_apply {r : ℕ} (x : Fin r → Fin X.B.I.n → X.B.I.E) (a : Fin r) (y : Fin X.B.I.n → X.B.I.E) :
    ∑ j, Kf X x a j * y j = hE X.B.I.cm.sig X.B.I.J (x a) y := by
  simp only [Kf, hE, Formalism.UG.hform, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem hE_swap (x y : Fin X.B.I.n → X.B.I.E) :
    hE X.B.I.cm.sig X.B.I.J x y = star (hE X.B.I.cm.sig X.B.I.J y x) := by
  have hJ : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := by
    intro i j
    have := congrFun (congrFun X.B.I.J_herm i) j
    simpa [Formalism.UG.cT, starRingEnd_apply] using this
  show (∑ i, ∑ j, star (x i) * X.B.I.J i j * y j) = star (∑ i, ∑ j, star (y i) * X.B.I.J i j * x j)
  rw [star_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul, star_mul, star_star, hJ]
  ring

theorem std (u : D.what₂.Word) : (frameOf X u).IsStd X.B.I.cm.sig X.B.I.J (((D.mem u).A.T : ℕ) : X.B.I.F) :=
  MassDataLevelSSteps.FrameW.frameOf_isStd X u

theorem hKf_f (u : D.what₂.Word) : ∀ a b, ∑ j, Kf X X.eR a j * X.fR b j = if a = b then 1 else 0 := by
  intro a b
  rw [Kf_apply]
  exact (std X u).2.2.1 a b

theorem hK_e (u : D.what₂.Word) : ∀ c b, ∑ j, Kf X X.fR c j * X.eR b j = if c = b then 1 else 0 := by
  intro c b
  rw [Kf_apply, hE_swap]
  have := (std X u).2.2.1 b c
  change hE _ _ (X.eR b) (X.fR c) = _ at this
  rw [this]
  by_cases h : c = b
  · subst h; simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, star_zero]

theorem sum_Kf_mul_zR_eq_zero (u : D.what₂.Word) : ∀ a, ∑ j, Kf X X.eR a j * X.zR u j = 0 := by
  intro a
  rw [Kf_apply]
  exact (std X u).2.2.2.1 a

theorem sigR_inclR (x : X.B.I.E) :
    sigR (AF X.B.I.F) X.B.I.cm.sig (inclR (AF X.B.I.F) x) = inclR (AF X.B.I.F) (X.B.I.cm.sig x) := by
  show (Algebra.TensorProduct.map (AlgHom.id X.B.I.F (AF X.B.I.F)) X.B.I.cm.sig)
      ((1 : AF X.B.I.F) ⊗ₜ[X.B.I.F] x) = (1 : AF X.B.I.F) ⊗ₜ[X.B.I.F] (X.B.I.cm.sig x)
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem hR_ratV_left (x : Fin X.B.I.n → X.B.I.E) (y : Fin X.B.I.n → AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    hR (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (AF X.B.I.F) x) y =
      ∑ j, inclR (AF X.B.I.F) (∑ i, star (x i) * X.B.I.J i j) * y j := by

  simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply, ratV, sigR_inclR, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem inclR_injective : Function.Injective (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) := by
  intro a b h
  obtain v := (inferInstance : Nonempty (InfinitePlace X.B.I.F)).some
  apply (X.B.I.φ v).injective
  rw [← thetaV_inclR X.B.I v a, ← thetaV_inclR X.B.I v b, h]

theorem sigA_inclE (x : X.B.I.E) :
    Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F) (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.B.I.cm.sig x) := by
  simp [Formalism.UG.sigR, Formalism.UG.inclE]

theorem hA_incl_left (x : Fin X.B.I.n → X.B.I.E) (y : Formalism.L2.SG.HidaSetting.VA X.B.I) :
    hA X.B.I (incl X.B.I x) y =
      ∑ j, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (∑ i, star (x i) * X.B.I.J i j) * y j := by

  simp only [hA, Formalism.UG.hform, Matrix.map_apply, incl, sigA_inclE, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem inclE_injective : Function.Injective (Formalism.UG.inclE (F := X.B.I.F) (E := X.B.I.E) (Af X.B.I.F)) :=
  Algebra.TensorProduct.includeLeft_injective (R := X.B.I.F) (S := X.B.I.F)
    (MassDataMassesW.inj_Af X.B.I.F)

end Spec

end MassDataMassesW.NRatW
end
end

section

noncomputable section

open NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace MassDataMassesW.NLev

section Grp

variable {I : AutInst}

theorem Kset_Lf {x : I.Gf} (hx : x ∈ I.Kset) : ∀ v ∈ I.Lf, I.fmat x *ᵥ v ∈ I.Lf := by
  intro v hv
  have h : ∀ w, w ∈ I.Lf ↔ I.fmat x *ᵥ w ∈ I.Lf := hx
  exact (h v).1 hv

theorem Kset_inv {x : I.Gf} (hx : x ∈ I.Kset) : x⁻¹ ∈ I.Kset := by
  show ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [InvMemClass.coe_inv]
  exact (Formalism.UG.stabGL I.Lf).inv_mem hx

theorem Kset_mul {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) : x * y ∈ I.Kset := by
  show ((x * y : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [MulMemClass.coe_mul]
  exact (Formalism.UG.stabGL I.Lf).mul_mem hx hy

theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp only [Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv, Units.inv_mul]

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp only [Formalism.MainNotions.S.AutInst.fmat, InvMemClass.coe_inv, Units.mul_inv]

def Tm (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v : VA I) : VA I :=
  Ai *ᵥ ((By - 1) *ᵥ (A *ᵥ v))

theorem Tm_add (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v w : VA I) :
    Tm Ai By A (v + w) = Tm Ai By A v + Tm Ai By A w := by
  simp only [Tm, Matrix.mulVec_add]

theorem Tm_sub (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (v w : VA I) :
    Tm Ai By A (v - w) = Tm Ai By A v - Tm Ai By A w := by
  simp only [Tm, Matrix.mulVec_sub]

theorem Tm_smul (Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (r : I.E ⊗[I.F] Af I.F) (v : VA I) :
    Tm Ai By A (r • v) = r • Tm Ai By A v := by
  simp only [Tm, Matrix.mulVec_smul]

theorem sub_one_Lf {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hM : ∀ v ∈ I.Lf, M *ᵥ v ∈ I.Lf) :
    ∀ v ∈ I.Lf, (M - 1) *ᵥ v ∈ I.Lf := by
  intro v hv
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact I.Lf.sub_mem (hM v hv) hv

theorem Tm_Lf {Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hAi : ∀ v ∈ I.Lf, Ai *ᵥ v ∈ I.Lf)
    (hBy : ∀ v ∈ I.Lf, By *ᵥ v ∈ I.Lf) (hA : ∀ v ∈ I.Lf, A *ᵥ v ∈ I.Lf) :
    ∀ v ∈ I.Lf, Tm Ai By A v ∈ I.Lf :=
  fun v hv => hAi _ (sub_one_Lf hBy _ (hA v hv))

theorem Tm_mL (m : ℕ) {Ai By A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)}
    (hAi : ∀ v ∈ I.Lf, Ai *ᵥ v ∈ I.Lf) (hBy : ∀ v ∈ I.Lf, By *ᵥ v ∈ I.Lf) (hA : ∀ v ∈ I.Lf, A *ᵥ v ∈ I.Lf) :
    ∀ v ∈ mL I m, Tm Ai By A v ∈ mL I m := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Tm_smul]
    exact Submodule.subset_span ⟨_, Tm_Lf hAi hBy hA x hx, rfl⟩
  | zero =>
    have h0 : Tm Ai By A 0 = 0 := by simp [Tm]
    rw [h0]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [Tm_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have h1 : Tm Ai By A (a • x) = a • Tm Ai By A x := by
      rw [Subring.smul_def, Subring.smul_def, Tm_smul]
    rw [h1]
    exact Submodule.smul_mem _ a hx

end Grp

variable {D : Formalism.BasicNotions.D7} (X : HidaSetting D)

theorem sig_eq : (starRingEnd X.B.I.E) = (X.B.I.cm.sig : X.B.I.E →+* X.B.I.E) := by
  first
  | rfl
  | exact RingHom.ext fun _ => rfl

theorem hA_e_f (a b : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I (X.fR b)) = if a = b then 1 else 0 := by
  rw [hA_incl, sig_eq]
  have h := MassDataLevelSSteps.FrameW.hE_crdOf X (X.eX a) (X.fY b)
  change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
    (crdOf X.B.I X.ιE X.bas (X.eX a)) (crdOf X.B.I X.ιE X.bas (X.fY b))) = _
  rw [h, X.ef]
  split_ifs <;> simp

theorem hA_f_e (b a : Fin D.R.rS) :
    hA X.B.I (incl X.B.I (X.fR b)) (incl X.B.I (X.eR a)) = if b = a then 1 else 0 := by
  rw [hA_incl, sig_eq]
  have h := MassDataLevelSSteps.FrameW.hE_crdOf X (X.fY b) (X.eX a)
  change Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hE X.B.I.cm.sig X.B.I.J
    (crdOf X.B.I X.ιE X.bas (X.fY b)) (crdOf X.B.I X.ιE X.bas (X.eX a))) = _
  rw [h, ← LinearMap.isSymm_def.1 (VS D).herm (X.eX a) (X.fY b), X.ef]
  by_cases hab : a = b
  · subst hab; simp
  · simp [hab, Ne.symm hab]

theorem key {c d : ℕ} (hfL : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I (X.fR b) ∈ X.B.I.Lf)
    (hec : ∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g)
    {s : Set (Fin D.R.rS)} {w : VA X.B.I}
    (hw : w ∈ Submodule.span (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ((fun b => incl X.B.I (X.eR b)) '' s))
    (hdw : (d : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈ X.B.I.Lf) :
    ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • w ∈
      Submodule.span (IntAf X.B.I.F X.B.I.E) (X.e0 '' s) ⊔ mL X.B.I X.B.g := by
  classical
  obtain ⟨l, hls, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination _).1 hw
  have hsum : Finsupp.linearCombination (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (fun b => incl X.B.I (X.eR b)) l =
      ∑ b, l b • incl X.B.I (X.eR b) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i; exact zero_smul _ _
  rw [hsum] at hdw ⊢
  have hcoef : ∀ b, ((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b ∈ IntAf X.B.I.F X.B.I.E := by
    intro b
    have h := hA_int X.B.I _ (hfL b) _ hdw
    rw [hA_nat_left, hA_smul_right, hA_sum_right] at h
    simp only [hA_smul_right, hA_f_e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at h
    convert h using 1
    push_cast; ring
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : l b = 0
  · rw [hb, zero_smul, smul_zero]; exact zero_mem _
  have hbs : b ∈ s := hls (Finsupp.mem_support_iff.2 hb)
  have heq : ((c * d * c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (l b • incl X.B.I (X.eR b)) =
      (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) • ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • X.e0 b) -
      (((c * d : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * l b) •
        ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b))) := by
    rw [← smul_sub, ← smul_sub, sub_sub_cancel]
    simp only [smul_smul]
    congr 1; push_cast; ring
  rw [heq]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (sm X.B.I (hcoef b) (hec b)))
  exact sm X.B.I (hcoef b) (sm X.B.I (natCast_int X.B.I c) (Submodule.subset_span ⟨b, hbs, rfl⟩))

theorem mults (u : D.what₂.Word) : ∃ c : ℕ, Nat.Coprime c X.B.g ∧
    (∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 b - incl X.B.I (X.eR b)) ∈ mL X.B.I X.B.g) ∧
    (∀ b, (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 b - incl X.B.I (X.fR b)) ∈ mL X.B.I X.B.g) ∧
    (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) ∈
      mL X.B.I X.B.g := by
  have h1 : ∀ a, ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.e0 a - incl X.B.I (X.eR a)) ∈ mL X.B.I X.B.g :=
    fun a => (X.basisApprox a).1
  have h2 : ∀ a, ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.f0 a - incl X.B.I (X.fR a)) ∈ mL X.B.I X.B.g :=
    fun a => (X.basisApprox a).2
  have h3 : ∃ c : ℕ, Nat.Coprime c X.B.g ∧
      (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u) - X.z0) ∈
        mL X.B.I X.B.g := X.xu_z u
  choose ce hce1 hce2 using h1
  choose cf hcf1 hcf2 using h2
  obtain ⟨cz, hcz1, hcz2⟩ := h3
  have hP : ∀ b, ce b * cf b ∣ ∏ a, ce a * cf a := fun b =>
    Finset.dvd_prod_of_mem (fun a => ce a * cf a) (Finset.mem_univ b)
  have hcop : Nat.Coprime ((∏ a, ce a * cf a) * cz) X.B.g :=
    Nat.Coprime.mul_left (Nat.Coprime.prod_left fun a _ => Nat.Coprime.mul_left (hce1 a) (hcf1 a)) hcz1
  have hd1 : ∀ b, ce b ∣ (∏ a, ce a * cf a) * cz := fun b =>
    Dvd.dvd.mul_right ((Dvd.intro (cf b) rfl).trans (hP b)) cz
  have hd2 : ∀ b, cf b ∣ (∏ a, ce a * cf a) * cz := fun b =>
    Dvd.dvd.mul_right ((Dvd.intro_left (ce b) rfl).trans (hP b)) cz
  have hd3 : cz ∣ (∏ a, ce a * cf a) * cz := Dvd.intro_left _ rfl
  exact ⟨(∏ a, ce a * cf a) * cz, hcop, fun b => dvd_smul X.B.I (hd1 b) (hce2 b),
    fun b => dvd_smul X.B.I (hd2 b) (hcf2 b), dvd_smul X.B.I hd3 hcz2⟩

end MassDataMassesW.NLev
end
end

section

noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

namespace MassDataMassesW

theorem massUnfoldGen_holds : PIW.MassDataColumns.MassUnfoldGen := by
  intro D X u hM _ U _ hUo hfin 𝓕 h𝓕
  exact massUnfold_gen (hCM := isCMExt_of_cmData X.B.I.cm) (hJ := isHermND_of_setting X) (M := X.measW u)
    (hM := hM) (U := U) (hU := hUo.measurableSet) (hfin := hfin) (𝓕 := 𝓕) (h𝓕 := h𝓕)

end MassDataMassesW
end
end
