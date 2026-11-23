module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Commensurated
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.SplitGL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.SplitIso
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

section Delta

variable {G : Type} [Group G]

def idxRatio (A B : Subgroup G) : ℚ := (B.relIndex A : ℚ) / (A.relIndex B : ℚ)

theorem idxRatio_eq_of_le (A B D : Subgroup G) (hDA : D ≤ A) (hDB : D ≤ B)
    (hA : D.relIndex A ≠ 0) :
    idxRatio A B = (D.relIndex A : ℚ) / (D.relIndex B : ℚ) := by
  have h1 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex A = D.relIndex A :=
    Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_left)
  have h2 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex B = D.relIndex B :=
    Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_right)
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right] at h2
  have hc0 : D.relIndex (A ⊓ B) ≠ 0 := by
    intro h0
    apply hA
    rw [← h1, h0, zero_mul]
  have hc : (D.relIndex (A ⊓ B) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc0
  unfold idxRatio
  rw [← h1, ← h2, Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hc]

theorem relIndex_inf_three_ne_zero {A B C L : Subgroup G} (hA : A.relIndex L ≠ 0)
    (hB : B.relIndex L ≠ 0) (hC : C.relIndex L ≠ 0) : (A ⊓ B ⊓ C).relIndex L ≠ 0 := by
  exact Subgroup.relIndex_inf_ne_zero (Subgroup.relIndex_inf_ne_zero hA hB) hC

theorem relIndex_self_ne_zero (A : Subgroup G) : A.relIndex A ≠ 0 := by
  rw [Subgroup.relIndex_self]
  exact one_ne_zero

theorem idxRatio_mul (A B C : Subgroup G)
    (hAB : B.relIndex A ≠ 0) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hBC : C.relIndex B ≠ 0) :
    idxRatio A B * idxRatio B C = idxRatio A C := by
  have hDA := relIndex_inf_three_ne_zero (relIndex_self_ne_zero A) hAB hAC
  have hDB := relIndex_inf_three_ne_zero hBA (relIndex_self_ne_zero B) hBC
  rw [idxRatio_eq_of_le A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hDA,
    idxRatio_eq_of_le B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right hDB,
    idxRatio_eq_of_le A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right hDA,
    div_mul_div_comm, mul_comm ((A ⊓ B ⊓ C).relIndex A : ℚ),
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hDB)]

private theorem relIndex_map_of_injective (X Y : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    (X.map f).relIndex (Y.map f) = X.relIndex Y := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq_self_of_injective hf]

theorem idxRatio_map (A B : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    idxRatio (A.map f) (B.map f) = idxRatio A B := by
  unfold idxRatio
  rw [relIndex_map_of_injective _ _ f hf, relIndex_map_of_injective _ _ f hf]

theorem map_conj_mul' (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one' (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map]

theorem relIndex_conj_conj_ne_zero (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    (K.map (MulAut.conj x).toMonoidHom).relIndex (K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  have h1 : K.map (MulAut.conj x).toMonoidHom =
      (K.map (MulAut.conj (y⁻¹ * x)).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [map_conj_mul', mul_inv_cancel_left]
  rw [h1, relIndex_map_of_injective _ _ _ (by intro a b h; simpa using h)]
  exact hK (y⁻¹ * x)

theorem relIndex_conj_right_ne_zero (K : Subgroup G) (hK : Commensurated K) (a : G) :
    K.relIndex (K.map (MulAut.conj a).toMonoidHom) ≠ 0 := by
  have h := relIndex_conj_conj_ne_zero K hK 1 a
  rwa [map_conj_one'] at h

theorem dIdx_inv_eq (K : Subgroup G) (x : G) :
    dIdx K x⁻¹ = K.relIndex (K.map (MulAut.conj x).toMonoidHom) := by
  unfold dIdx
  rw [← relIndex_map_of_injective _ _ (MulAut.conj x).toMonoidHom (by intro a b h; simpa using h),
    map_conj_mul', mul_inv_cancel, map_conj_one']

theorem modQ_eq_idxRatio (K : Subgroup G) (x : G) :
    modQ K x = idxRatio K (K.map (MulAut.conj x).toMonoidHom) := by
  unfold modQ idxRatio
  rw [dIdx_inv_eq]
  rfl

theorem dIdx_one (K : Subgroup G) : dIdx K 1 = 1 := by
  unfold dIdx
  rw [map_conj_one', Subgroup.relIndex_self]

theorem modQ_one (K : Subgroup G) : modQ K 1 = 1 := by
  unfold modQ
  simp [dIdx_one]

theorem modQ_mul (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    modQ K (x * y) = modQ K x * modQ K y := by
  rw [modQ_eq_idxRatio, modQ_eq_idxRatio, modQ_eq_idxRatio,
    ← idxRatio_map K (K.map (MulAut.conj y).toMonoidHom) (MulAut.conj x).toMonoidHom
      (by intro a b h; simpa using h), map_conj_mul']
  exact (idxRatio_mul K (K.map (MulAut.conj x).toMonoidHom) (K.map (MulAut.conj (x * y)).toMonoidHom)
    (hK x) (hK (x * y)) (relIndex_conj_right_ne_zero K hK x)
    (relIndex_conj_conj_ne_zero K hK (x * y) x)).symm

end Delta

end PI.UnitaryGroupMassFormula.AdIndexEq
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

def IsQRefl (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (s : Uv I v) : Prop :=
  ∃ (P : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E))
    (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E),
    P * P = P ∧ sigV I v α * α = 1 ∧
      (((s : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) = 1 + (α - 1) • P)

def QReflGen : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ g : Uv I v, g ∈ Subgroup.closure {s : Uv I v | IsQRefl I v s}

def QReflPow : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ s : Uv I v, IsQRefl I v s →
      ∃ m : ℕ, 1 ≤ m ∧ (((s ^ m : Uv I v) : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) ∈ Kv I v)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

def incL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E :=
  Algebra.TensorProduct.includeLeftRingHom

def TraceInt : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E, sigV I v α * α = 1 →
      ∃ t ∈ v.adicCompletionIntegers I.F, α + sigV I v α = incL I v t

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open Formalism.MainNotions.S

def ModQHom : Prop :=
  ∀ (G : Type) [Group G] (K : Subgroup G), Commensurated K →
    (∀ x y : G, modQ K (x * y) = modQ K x * modQ K y) ∧ (∀ k ∈ K, modQ K k = 1) ∧
      (∀ x : G, modQ K x = 1 → dIdx K x = dIdx K x⁻¹)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

def GLChi : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (n : ℕ) (χ : GL (Fin n) k →* ℚ), (∀ g, 0 < χ g) →
    (∀ d : kˣ, χ (Units.map (algebraMap k (Matrix (Fin n) (Fin n) k)).toMonoidHom d) = 1) →
    ∀ g, χ g = 1

theorem spl_sig_sig (I : AutInst) (a : I.E) : I.cm.sig (I.cm.sig a) = a := by
  change star (star a) = a
  exact star_star a

theorem spl_sig_fix (I : AutInst) (a : I.E) (h : I.cm.sig a = a) : a ∈ (algebraMap I.F I.E).range := (I.cm.fixed a).1 h

theorem spl_sigV_inclV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x : I.E) :
    sigV I v (inclV I v x) = inclV I v (starRingEnd I.E x) := by
  simp only [sigV, inclV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

theorem spl_herm_v (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.UG.cT (sigV I v) (I.J.map (inclV I v)) = I.J.map (inclV I v) := by
  have h := I.J_herm
  unfold Formalism.UG.IsHerm at h
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at hij ⊢
  rw [spl_sigV_inclV, hij]

theorem spl_det_v (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) : IsUnit (I.J.map (inclV I v)).det := by
  have h := RingHom.map_det (inclV I v) I.J
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact (isUnit_iff_ne_zero.2 I.J_det).map _

theorem locSplitChi_of (hG : GLChi) : LocSplitChi := by
  intro I v hnf χ hpos hcent _ g
  haveI : CharZero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    charZero_of_injective_algebraMap (algebraMap I.F _).injective
  obtain ⟨π, hπ⟩ := SplitIso.exists_split (K := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.cm.sig
    (spl_sig_sig I) (spl_sig_fix I) I.cm.deg2 two_ne_zero hnf
  have hπ' : ∀ r, π (sigV I v r) = (π r).swap := hπ
  let f : Uv I v →* GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) :=
    SplitGL.proj (sigV I v) π (I.J.map (inclV I v))
  have hbij : Function.Bijective f :=
    SplitGL.proj_bijective (sigV I v) π hπ' (I.J.map (inclV I v)) (spl_herm_v I v) (spl_det_v I v)
  let e : Uv I v ≃* GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) := MulEquiv.ofBijective f hbij
  have key := hG (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) I.n (χ.comp e.symm.toMonoidHom) (fun g => hpos _) ?_ (e g)
  · have h2 : e.symm (e g) = g := e.symm_apply_apply g
    rw [← h2]; exact key
  · intro d
    show χ (e.symm _) = 1
    apply hcent
    intro t
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    apply Units.ext
    simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    exact Algebra.commutes _ _

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S

theorem matV_coe (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    ((matV I v g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) : Matrix _ _ _) =
      (g : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)).map (PI.FinKW.psiV I v).toRingHom := rfl

private theorem eq_of_forall_evalV_eq {F : Type} [Field F] [NumberField F] (a b : Af F)
    (h : ∀ v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v a = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v b) : a = b :=
  Subtype.ext (funext fun v => h v)

private theorem tensorBasis_repr_psiV_eq_evalV_repr_comm (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (z : I.E ⊗[I.F] Af I.F) (i : Module.Free.ChooseBasisIndex I.F I.E) :
    (Algebra.TensorProduct.basis (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) (Module.Free.chooseBasis I.F I.E)).repr
        (PI.FinKW.psiV I v z) i =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v
        ((Algebra.TensorProduct.basis (Af I.F) (Module.Free.chooseBasis I.F I.E)).repr
          (Algebra.TensorProduct.comm I.F I.E (Af I.F) z) i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a =>
    simp [PI.FinKW.psiV, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply,
      Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem mat_ext_of_psiV (I : AutInst) (M N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (h : ∀ v, M.map (PI.FinKW.psiV I v).toRingHom = N.map (PI.FinKW.psiV I v).toRingHom) :
    M = N := by
  ext i j
  have hij : ∀ v, PI.FinKW.psiV I v (M i j) = PI.FinKW.psiV I v (N i j) := fun v => by
    have := congrFun (congrFun (h v) i) j
    simpa [Matrix.map_apply] using this
  apply (Algebra.TensorProduct.comm I.F I.E (Af I.F)).injective
  apply (Algebra.TensorProduct.basis (Af I.F) (Module.Free.chooseBasis I.F I.E)).repr.injective
  refine Finsupp.ext fun k => ?_
  apply eq_of_forall_evalV_eq
  intro v
  rw [← tensorBasis_repr_psiV_eq_evalV_repr_comm, ← tensorBasis_repr_psiV_eq_evalV_repr_comm, hij v]

theorem matrix_v_injective : MatVInj := by
  unfold MatVInj
  intro I y z h
  apply Subtype.ext
  apply Units.ext
  apply mat_ext_of_psiV I
  intro v
  have := congrArg Units.val (h v)
  simpa only [matV_coe] using this

theorem psiV_sigR (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (z : I.E ⊗[I.F] Af I.F) :
    PI.FinKW.psiV I v (Formalism.UG.sigR I.cm.sig (Af I.F) z) = sigV I v (PI.FinKW.psiV I v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e a => simp [PI.FinKW.psiV, Formalism.UG.sigR, sigV]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem psiV_inclE (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (e : I.E) :
    PI.FinKW.psiV I v (Formalism.UG.inclE (F := I.F) (Af I.F) e) = inclV I v e := by
  simp [PI.FinKW.psiV, Formalism.UG.inclE, inclV]

theorem map_cT {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (hf : ∀ a, f (σ a) = τ (f a)) {m p : Type} (M : Matrix m p A) :
    (Formalism.UG.cT σ M).map f = Formalism.UG.cT τ (M.map f) := by
  ext i j
  simp [Formalism.UG.cT, hf]

theorem mapJ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).map (PI.FinKW.psiV I v).toRingHom =
      I.J.map (inclV I v) := by
  ext i j
  simp only [Matrix.map_apply]
  exact psiV_inclE I v _

theorem map_unitary (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) M * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * M).map
              (PI.FinKW.psiV I v).toRingHom =
      Formalism.UG.cT (sigV I v) (M.map (PI.FinKW.psiV I v).toRingHom) * I.J.map (inclV I v) *
        M.map (PI.FinKW.psiV I v).toRingHom := by
  rw [Matrix.map_mul, Matrix.map_mul,
    map_cT (PI.FinKW.psiV I v).toRingHom (Formalism.UG.sigR I.cm.sig (Af I.F)) (sigV I v)
      (fun a => psiV_sigR I v a), mapJ]

theorem mem_Uv_iff (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (g : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
    g ∈ Uv I v ↔ Formalism.UG.cT (sigV I v) g.val * I.J.map (inclV I v) * g.val = I.J.map (inclV I v) := Iff.rfl

theorem mem_Gf_iff (I : AutInst) (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    g ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) ↔
      Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) g.val * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
        g.val = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := Iff.rfl

theorem matrix_v_unitary : MatVU := by
  unfold MatVU
  intro I v y
  rw [mem_Uv_iff, matV_coe]
  have hy := (mem_Gf_iff I y).1 y.2
  rw [← map_unitary, hy]
  exact mapJ I v

theorem vecV_mulVec' (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F))
    (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (x : Fin I.n → I.E ⊗[I.F] Af I.F) :
    PI.FinKW.vecV I v (M *ᵥ x) = M.map (PI.FinKW.psiV I v).toRingHom *ᵥ PI.FinKW.vecV I v x := by
  funext i

  simp [PI.FinKW.vecV, Matrix.mulVec, dotProduct, map_sum]

theorem stab_iff_loc (I : AutInst) (g : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
    g ∈ Formalism.UG.stabGL I.Lf ↔ ∀ v, matV I v g ∈ Kv I v := by
  have hL : ∀ x, x ∈ I.Lf ↔
      ∀ v, PI.FinKW.vecV I v x ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) :=
    fun x => ⟨PI.FinKW.LocTo.mem_local_lattice_iff I x, PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective I x⟩
  constructor
  · intro hst v y
    obtain ⟨x, hxv, hxw⟩ := PI.FinKW.local_vector_lift I v y
    have ex : x ∈ I.Lf ↔ y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL x]
      constructor
      · intro H
        have := H v
        rwa [hxv] at this
      · intro H w
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw]
          exact zero_mem _
    have egx : (g : Matrix _ _ _) *ᵥ x ∈ I.Lf ↔
        ((matV I v g : GL (Fin I.n) _) : Matrix _ _ _) *ᵥ y ∈
          Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)) := by
      rw [hL, matV_coe]
      constructor
      · intro H
        have := H v
        rwa [vecV_mulVec', hxv] at this
      · intro H w
        rw [vecV_mulVec']
        by_cases hw : w = v
        · subst hw
          rwa [hxv]
        · rw [hxw w hw, Matrix.mulVec_zero]
          exact zero_mem _
    exact ex.symm.trans ((hst x).trans egx)
  · intro hK x
    show x ∈ I.Lf ↔ (g : Matrix _ _ _) *ᵥ x ∈ I.Lf
    rw [hL x, hL ((g : Matrix _ _ _) *ᵥ x)]
    refine forall_congr' fun v => ?_
    rw [vecV_mulVec', ← matV_coe]
    exact hK v (PI.FinKW.vecV I v x)

theorem compact_local_global : KLocGlob := by
  unfold KLocGlob
  intro I y
  rw [PI.AdIndexEq.Ksub, Subgroup.mem_comap]
  exact stab_iff_loc I _

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end
