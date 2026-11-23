module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFormsTieOLatTie
public import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle196
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle193
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle305
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.SpOfMat

open MonoidAlgebra

variable {G : Type} [Group G] [Fintype G]

theorem eq_sum_single {R : Type} [Semiring R] (a : MonoidAlgebra R G) : a = ∑ g, single g (a.coeff g) := by
  classical
  apply MonoidAlgebra.ext
  ext g
  simp [MonoidAlgebra.coeff_sum, Finsupp.single_apply]

noncomputable def conjSum (R : Type) [Semiring R] (g : G) : MonoidAlgebra R G := ∑ h, single (h * g * h⁻¹) 1

theorem conjSum_mem_center (R : Type) [CommSemiring R] (g : G) : conjSum R g ∈ Subalgebra.center R (MonoidAlgebra R G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of k =>
    simp only [conjSum, MonoidAlgebra.of_apply, Finset.mul_sum, Finset.sum_mul, single_mul_single, one_mul, mul_one]
    refine Fintype.sum_equiv (Equiv.mulLeft k) _ _ fun h => ?_
    simp only [Equiv.coe_mulLeft]
    congr 1
    group
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem mapRange_conjSum {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) (g : G) :
    mapRingHom G f (conjSum R g) = conjSum S g := by

  simp [conjSum, map_sum, MonoidAlgebra.mapRingHom_single]

theorem card_smul_eq {R : Type} [CommSemiring R] (z : MonoidAlgebra R G) (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) :
    (Fintype.card G : R) • z = ∑ g, z.coeff g • conjSum R g := by
  rw [Subalgebra.mem_center_iff] at hz
  have h1 : ∀ h : G, single h (1 : R) * z * single h⁻¹ 1 = z := fun h => by
    rw [hz, mul_assoc, single_mul_single, mul_inv_cancel, one_mul, ← one_def, mul_one]
  have h2 : ∀ h : G, single h (1 : R) * z * single h⁻¹ 1 = ∑ g, single (h * g * h⁻¹) (z.coeff g) := fun h => by
    conv_lhs => rw [eq_sum_single z]
    simp only [Finset.mul_sum, Finset.sum_mul, single_mul_single, one_mul, mul_one]
  calc (Fintype.card G : R) • z = ∑ h : G, z := by rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    _ = ∑ h : G, ∑ g, single (h * g * h⁻¹) (z.coeff g) := Finset.sum_congr rfl fun h _ => (h1 h).symm.trans (h2 h)
    _ = ∑ g, z.coeff g • conjSum R g := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [conjSum, Finset.smul_sum, smul_single, smul_eq_mul, mul_one]

end GlobalTheory.Mem.R3.Rw.SpOfMat

namespace GlobalTheory.Mem.R3.Rw.SpOfMat

open MonoidAlgebra

variable {G : Type} [Group G] [Fintype G]

theorem coeff_mapRingHom {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) (a : MonoidAlgebra R G) (g : G) :
    (mapRingHom G f a).coeff g = f (a.coeff g) := by
  classical
  conv_lhs => rw [eq_sum_single a]

  simp [map_sum, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.coeff_sum, Finsupp.single_apply, apply_ite f]

section Act

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} {σ : K →+* ℂ}
  {j : (Fin n → K) →ₛₗ[σ] EuclideanSpace ℂ (Fin n)} {H : Matrix (Fin n) (Fin n) K}
  {ρ : Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n))}

theorem rho_smul (hρ : ∀ E, FormsTie σ j H E (ρ E)) (c : K) (E : Matrix (Fin n) (Fin n) K) :
    ρ (c • E) = σ c • ρ E := by
  refine LinearMap.ext_on_range (hρ E).span fun i => ?_
  rw [(hρ _).op_eq, LinearMap.smul_apply, (hρ E).op_eq, Matrix.smul_mulVec, map_smulₛₗ]

theorem rho_symm (hρ : ∀ E, FormsTie σ j H E (ρ E)) (E : Matrix (Fin n) (Fin n) K)
    (hsa : ∀ x y, Formalism.DivisionValues.hform H (E.mulVec x) y = Formalism.DivisionValues.hform H x (E.mulVec y)) : (ρ E).IsSymmetric := by
  let b := Module.Basis.mk (hρ E).li (hρ E).span.ge
  have hB : (innerₛₗ ℂ).comp (ρ E) = (innerₛₗ ℂ).compl₂ (ρ E) := by
    refine LinearMap.ext_basis b b fun i k => ?_
    simp only [b, Module.Basis.mk_apply, LinearMap.comp_apply, LinearMap.compl₂_apply, (hρ E).op_eq]
    change inner ℂ (j _) (j _) = inner ℂ (j _) (j _)
    rw [(hρ E).inner, (hρ E).inner, hsa]
  intro x y
  have := DFunLike.congr_fun (DFunLike.congr_fun hB x) y
  exact this

noncomputable def lin (ρ : Matrix (Fin n) (Fin n) K →+* Module.End ℂ (EuclideanSpace ℂ (Fin n)))
    (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K) :
    MonoidAlgebra ℂ G →ₗ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun a := ∑ g, a.coeff g • ρ (op (single g 1))
  map_add' a b := by simp [MonoidAlgebra.coeff_add, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [MonoidAlgebra.coeff_smul, Finset.smul_sum, smul_smul]

theorem lin_map (hρ : ∀ E, FormsTie σ j H E (ρ E)) (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, op (a + b) = op a + op b) (hsmul : ∀ (c : K) a, op (c • a) = c • op a) (a : MonoidAlgebra K G) :
    lin ρ op (mapRingHom G σ a) = ρ (op a) := by
  let opL : MonoidAlgebra K G →ₗ[K] Matrix (Fin n) (Fin n) K := ⟨⟨op, hadd⟩, hsmul⟩
  change _ = ρ (opL a)
  conv_rhs => rw [eq_sum_single a]

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : single g (a.coeff g) = a.coeff g • single g (1 : K) := by rw [smul_single, smul_eq_mul, mul_one]
  rw [h1, map_smul, rho_smul hρ, coeff_mapRingHom]
  rfl

theorem lin_mul (hρ : ∀ E, FormsTie σ j H E (ρ E)) (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, op (a + b) = op a + op b) (hsmul : ∀ (c : K) a, op (c • a) = c • op a)
    (hmul : ∀ a ∈ Subalgebra.center K (MonoidAlgebra K G), ∀ b ∈ Subalgebra.center K (MonoidAlgebra K G),
      op (a * b) = op a * op b)
    (z w : MonoidAlgebra ℂ G) (hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G))
    (hw : w ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : lin ρ op (z * w) = lin ρ op z * lin ρ op w := by
  have hone : ∀ α : G → ℂ, lin ρ op (∑ g, α g • conjSum ℂ g) = ∑ g, α g • ρ (op (conjSum K g)) := fun α => by

    rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, ← mapRange_conjSum σ, lin_map hρ op hadd hsmul]
  have key : ∀ α β : G → ℂ, lin ρ op ((∑ g, α g • conjSum ℂ g) * ∑ h, β h • conjSum ℂ h) =
      lin ρ op (∑ g, α g • conjSum ℂ g) * lin ρ op (∑ h, β h • conjSum ℂ h) := fun α β => by

    rw [hone, hone, Finset.sum_mul_sum, Finset.sum_mul_sum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [smul_mul_smul_comm, smul_mul_smul_comm, map_smul, ← mapRange_conjSum σ, ← mapRange_conjSum σ, ← map_mul,
      lin_map hρ op hadd hsmul, hmul _ (conjSum_mem_center K g) _ (conjSum_mem_center K h), map_mul]
  have h := key z.coeff w.coeff
  rw [← card_smul_eq z hz, ← card_smul_eq w hw, smul_mul_smul_comm, map_smul, map_smul, map_smul,
    smul_mul_smul_comm] at h
  have hc : ((Fintype.card G : ℂ) * (Fintype.card G : ℂ)) ≠ 0 := by
    have : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    exact mul_ne_zero this this
  exact smul_right_injective _ hc h

noncomputable def actC (hρ : ∀ E, FormsTie σ j H E (ρ E)) (op : MonoidAlgebra K G → Matrix (Fin n) (Fin n) K)
    (hadd : ∀ a b, op (a + b) = op a + op b) (hsmul : ∀ (c : K) a, op (c • a) = c • op a)
    (hmul : ∀ a ∈ Subalgebra.center K (MonoidAlgebra K G), ∀ b ∈ Subalgebra.center K (MonoidAlgebra K G),
      op (a * b) = op a * op b) (hone : op 1 = 1) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun z := lin ρ op z
  map_one' := by
    change lin ρ op 1 = 1
    rw [← map_one (mapRingHom G σ), lin_map hρ op hadd hsmul, hone, map_one]
  map_mul' z w := lin_mul hρ op hadd hsmul hmul z w z.2 w.2
  map_zero' := map_zero _
  map_add' z w := map_add _ _ _
  commutes' c := by
    change lin ρ op (algebraMap ℂ (MonoidAlgebra ℂ G) c) = _
    rw [Algebra.algebraMap_eq_smul_one, map_smul, ← map_one (mapRingHom G σ), lin_map hρ op hadd hsmul, hone, map_one,
      Algebra.algebraMap_eq_smul_one]

end Act

end GlobalTheory.Mem.R3.Rw.SpOfMat

namespace GlobalTheory.Mem.R3.Rw.SpOfMat

open MonoidAlgebra

theorem exists_complexification_of_definiteGroupForms : ∀ (K O : Type) [Field K] [NumberField K] [StarRing K] [CommRing O] (o : O →+* K) (σ : K →+* ℂ) (G : Type) [Group G] [Fintype G] (m : Mat1 K G) (e : MonoidAlgebra K G), (∀ x, σ (star x) = starRingEnd ℂ (σ x)) → (∀ y, IsIntegral ℤ (o y)) → m.Laws σ e → ∃ s : Sp1 O (σ.comp o) G, Nonempty (Tie1 σ m s) := by
  intro K O _ _ _ _ o σ G _ _ m e hσ ho hm
  obtain ⟨j, M, ρ, hρ, hM, hcar⟩ :=
    GlobalTheory.Mem.CoordForms.exists_formsTie_oLatTie K O o σ m.n m.H m.N hσ hm.pos hm.lat
  have hcar' := hcar ho
  have hEE : m.E * m.E = m.E := by
    rw [hm.E_eq, ← hm.mul e hm.cen e hm.cen, hm.idem.eq]
  let s : Sp1 O (σ.comp o) G :=
    { A := Hs.mk (EuclideanSpace ℂ (Fin m.n))
      lat := M
      e := ρ m.E
      idem := by rw [← Module.End.mul_eq_comp, ← map_mul, hEE]
      sa := rho_symm hρ m.E hm.sa
      act := actC hρ m.op hm.add hm.smul hm.mul hm.one }
  refine ⟨s, ⟨{ j := j, forms := hρ m.E, latT := hM, stable := ?_, cen := ?_ }⟩⟩
  · intro a y hy
    change y ∈ (M.carrier : Set (EuclideanSpace ℂ (Fin m.n))) at hy
    change σ (a : K) • y ∈ (M.carrier : Set (EuclideanSpace ℂ (Fin m.n)))
    rw [hcar'] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨(a : K) • x, ?_, by rw [map_smulₛₗ]⟩
    have := m.N.smul_mem a hx
    rwa [← algebraMap_smul K] at this
  · intro z a hza x
    have hz : (z : MonoidAlgebra ℂ G) = mapRingHom G σ a := by
      apply MonoidAlgebra.ext
      ext g
      rw [coeff_mapRingHom]
      exact (hza g).symm
    change lin ρ m.op z (j x) = _
    rw [hz, lin_map hρ m.op hm.add hm.smul, (hρ _).op_eq]

end GlobalTheory.Mem.R3.Rw.SpOfMat
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.ChainHilb

section Gen

variable {N : Type} [AddCommGroup N] [Module ℂ N] {C : Submodule ℂ N} {ip : N → N → ℂ}

theorem hp_add_right (h : PeterssonHilbertSpace.IsHermPos C ip) (x y y' : C) : ip x ((y : N) + y') = ip x y + ip x y' := by
  rw [← Submodule.coe_add, ← h.herm (y + y') x, Submodule.coe_add, h.add y y' x, map_add (f := _), h.herm y x, h.herm y' x]

theorem hp_smul_right (h : PeterssonHilbertSpace.IsHermPos C ip) (s : ℂ) (x y : C) : ip x (s • (y : N)) = s * ip x y := by
  rw [← Submodule.coe_smul, ← h.herm (s • y) x, Submodule.coe_smul, h.smul s y x, map_mul, h.herm y x,
    Complex.conj_conj]

theorem hp_restrict (h : PeterssonHilbertSpace.IsHermPos C ip) {C' : Submodule ℂ N} (hle : C' ≤ C) : PeterssonHilbertSpace.IsHermPos C' ip := by
  haveI := h.fd
  refine ⟨Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle), ?_, ?_, ?_, ?_⟩
  · intro x x' y; exact h.add ⟨x, hle x.2⟩ ⟨x', hle x'.2⟩ ⟨y, hle y.2⟩
  · intro s x y; exact h.smul s ⟨x, hle x.2⟩ ⟨y, hle y.2⟩
  · intro x y; exact h.herm ⟨x, hle x.2⟩ ⟨y, hle y.2⟩
  · intro x hx
    refine h.pos ⟨x, hle x.2⟩ ?_
    intro h0; apply hx; ext; simpa using congrArg Subtype.val h0

theorem hp_model (h : PeterssonHilbertSpace.IsHermPos C ip) : ∃ H : Hs, ∃ j : H.T →ₗ[ℂ] N,
    Function.Injective j ∧ LinearMap.range j = C ∧ ∀ x x', ⟪x, x'⟫_ℂ = ip (j x) (j x') := by
  have h1 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, ip x (y + c • z) = ip x y + c * ip x z ∧ ip y x = star (ip x y) := by
    intro x hx y hy z hz c
    refine ⟨?_, ?_⟩
    · have e1 := hp_add_right h ⟨x, hx⟩ ⟨y, hy⟩ ⟨c • z, C.smul_mem c hz⟩
      have e2 := hp_smul_right h c ⟨x, hx⟩ ⟨z, hz⟩
      exact e1.trans (congrArg (fun t => ip x y + t) e2)
    · exact (h.herm ⟨x, hx⟩ ⟨y, hy⟩).symm
  have h2 : ∀ x ∈ C, x ≠ 0 → 0 < (ip x x).re := fun x hx hne =>
    h.pos ⟨x, hx⟩ (fun h0 => hne (by simpa using congrArg Subtype.val h0))
  obtain ⟨M, hM⟩ := GlobalTheory.HilbertModel.exists_hmod N C ip h.fd h1 h2
  exact ⟨⟨M.H⟩, M.e, hM.1, hM.2.1, hM.2.2⟩

theorem hp_riesz {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (h : PeterssonHilbertSpace.IsHermPos C ip) (j : H →ₗ[ℂ] N) (hj : ∀ x, j x ∈ C) :
    ∃ r : C →ₗ[ℂ] H, ∀ x (w : C), ⟪x, r w⟫_ℂ = ip (j x) w := by
  have key : ∀ w : C, ∃ y : H, ∀ x, ⟪x, y⟫_ℂ = ip (j x) w := by
    intro w
    let φ : H →ₗ[ℂ] ℂ :=
      { toFun := fun x => ip w (j x)
        map_add' := fun a b => by
          have := hp_add_right h w ⟨j a, hj a⟩ ⟨j b, hj b⟩
          simpa [map_add (f := _)] using this
        map_smul' := fun s a => by
          have := hp_smul_right h s w ⟨j a, hj a⟩
          simpa [map_smul] using this }
    refine ⟨(InnerProductSpace.toDual ℂ H).symm (LinearMap.toContinuousLinearMap φ), fun x => ?_⟩
    rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
    exact h.herm w ⟨j x, hj x⟩
  choose y hy using key
  refine ⟨⟨⟨y, fun a b => ext_inner_left ℂ fun x => ?_⟩, fun s a => ext_inner_left ℂ fun x => ?_⟩, fun x w => hy w x⟩
  · rw [inner_add_right, hy, hy, hy, Submodule.coe_add]
    exact hp_add_right h ⟨j x, hj x⟩ a b
  · rw [RingHom.id_apply, inner_smul_right, hy, hy, Submodule.coe_smul]
    exact hp_smul_right h s ⟨j x, hj x⟩ a

end Gen

def heqv {A B : Hs} (h : A = B) : A.T ≃ₗᵢ[ℂ] B.T := by
  subst h; exact LinearIsometryEquiv.refl ℂ A.T

theorem heqv_heq {A B E : Hs} (e1 : A = E) (e2 : B = E) (v' : A.T) (v : B.T) (h : HEq v' v) :
    heqv e1 v' = heqv e2 v := by
  subst e1; subst e2; cases h; rfl

theorem heqv_self {A : Hs} (h : A = A) (x : A.T) : heqv h x = x := rfl

def chSel (m : ℕ) (A B : Hs) (L : ℕ → Hs) (j : ℕ) : Hs := if j = 0 then A else if j = m then B else L j

theorem chSel_zero {m : ℕ} {A B : Hs} {L : ℕ → Hs} : chSel m A B L 0 = A := if_pos rfl

theorem chSel_top {m : ℕ} {A B : Hs} {L : ℕ → Hs} (hm : m ≠ 0) : chSel m A B L m = B := by
  rw [chSel, if_neg hm, if_pos rfl]

theorem chSel_mid {m j : ℕ} {A B : Hs} {L : ℕ → Hs} (h1 : j ≠ 0) (h2 : j ≠ m) : chSel m A B L j = L j := by
  rw [chSel, if_neg h1, if_neg h2]

end GlobalTheory.ChainHilb

namespace GlobalTheory.ChainHilb

theorem exists_chainHilb : ∀ (D : D7) (C : ChainReal D) (b : Bool) (U : D.what₂.Tup → Prop) (Top : D.what₂.Tup → Hs) (jX : ∀ μ, (Top μ).T →ₗ[ℂ] C.AmbX), 2 ≤ D.R.m → PeterssonHilbertSpace.IsHermPos (C.EEc b) (C.ipE b) → (∀ μ, C.EEc b ≤ C.CC b μ 0 ∧ C.CCXP b μ ≤ C.CCX b μ ∧ PeterssonHilbertSpace.IsHermPos (C.CCX b μ) (C.ipXP b μ) ∧ ∀ j, j ≤ D.R.m - 1 → C.CCP b μ j ≤ C.CC b μ j ∧ PeterssonHilbertSpace.IsHermPos (C.CC b μ j) (C.ipP b μ j)) → (∀ μ, PeterssonHilbertSpace.IsHermPos (C.CC b μ 0) (C.ipE b)) → (∀ μ, U μ → Function.Injective (jX μ) ∧ LinearMap.range (jX μ) = C.CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = C.ipXP b μ (jX μ x) (jX μ x')) → ∃ (EE : Hs) (Mult : D.what₂.Tup → ℕ → Hs) (multZero : ∀ μ, (Mult μ 0).T ≃ₗᵢ[ℂ] EE.T) (multTop : ∀ μ, (Mult μ D.R.m).T ≃ₗᵢ[ℂ] (Top μ).T) (io : ∀ μ j, (Mult μ (j + 1)).T →ₗ[ℂ] (Mult μ j).T) (jE : EE.T →ₗ[ℂ] C.Amb 0) (jM : ∀ μ j, (Mult μ j).T →ₗ[ℂ] C.Amb j), Function.Injective jE ∧ LinearMap.range jE = C.EEc b ∧ (∀ x x', ⟪x, x'⟫_ℂ = C.ipE b (jE x) (jE x')) ∧ (∀ μ, U μ → ∀ j, 1 ≤ j → j ≤ D.R.m - 1 → Function.Injective (jM μ j) ∧ LinearMap.range (jM μ j) = C.CCP b μ j ∧ ∀ x x', ⟪x, x'⟫_ℂ = C.ipP b μ j (jM μ j x) (jM μ j x')) ∧ (∀ μ, U μ → ∀ x (v : (Mult μ 1).T) (h : jM μ 1 v ∈ C.CC b μ 1), ⟪x, multZero μ (io μ 0 v)⟫_ℂ = C.ipE b (jE x) (C.ioC b μ 0 ⟨jM μ 1 v, h⟩ : C.Amb 0)) ∧ (∀ μ, U μ → ∀ j, 1 ≤ j → j + 1 ≤ D.R.m - 1 → ∀ x (v : (Mult μ (j + 1)).T) (h : jM μ (j + 1) v ∈ C.CC b μ (j + 1)), ⟪x, io μ j v⟫_ℂ = C.ipP b μ j (jM μ j x) (C.ioC b μ j ⟨jM μ (j + 1) v, h⟩ : C.Amb j)) ∧ (∀ μ, U μ → ∀ x (v : (Mult μ D.R.m).T) (v' : (Mult μ (D.R.m - 1 + 1)).T), HEq v' v → ∀ h : jX μ (multTop μ v) ∈ C.CCX b μ, ⟪x, io μ (D.R.m - 1) v'⟫_ℂ = C.ipP b μ (D.R.m - 1) (jM μ (D.R.m - 1) x) (C.ioX b μ ⟨jX μ (multTop μ v), h⟩ : C.Amb (D.R.m - 1))) ∧ (∀ μ, ¬ U μ → ∀ j, io μ j = 0) := by
  classical
  intro D C b U Top jX hm hE hle hE0 hX
  obtain ⟨EE, jE, hEi, hEr, hEip⟩ := hp_model hE
  have jE_mem : ∀ μ x, jE x ∈ C.CC b μ 0 := fun μ x =>
    (hle μ).1 (by rw [← hEr]; exact LinearMap.mem_range_self jE x)
  have hLo : ∀ (μ : D.what₂.Tup) (j : ℕ), ∃ H : Hs, ∃ jj : H.T →ₗ[ℂ] C.Amb j, j ≤ D.R.m - 1 →
      Function.Injective jj ∧ LinearMap.range jj = C.CCP b μ j ∧
        ∀ x x', ⟪x, x'⟫_ℂ = C.ipP b μ j (jj x) (jj x') := by
    intro μ j
    by_cases hj : j ≤ D.R.m - 1
    · obtain ⟨h1, h2⟩ := (hle μ).2.2.2 j hj
      obtain ⟨H, jj, a1, a2, a3⟩ := hp_model (hp_restrict h2 h1)
      exact ⟨H, jj, fun _ => ⟨a1, a2, a3⟩⟩
    · exact ⟨EE, 0, fun h => absurd h hj⟩
  choose Lo jL hL using hLo
  let Mult : D.what₂.Tup → ℕ → Hs := fun μ => chSel D.R.m EE (Top μ) (Lo μ)
  let jM : ∀ μ j, (Mult μ j).T →ₗ[ℂ] C.Amb j := fun μ j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m - 1 then
      (jL μ j).comp (heqv (chSel_mid (m := D.R.m) (A := EE) (B := Top μ) (L := Lo μ)
        (by have := h.1; omega) (by have := h.2; omega))).toLinearEquiv.toLinearMap
    else 0
  have jM_mem : ∀ μ j x, jM μ j x ∈ C.CC b μ j := by
    intro μ j x
    dsimp only [jM]
    split_ifs with h
    · rw [LinearMap.comp_apply]
      refine ((hle μ).2.2.2 j h.2).1 ?_
      rw [← (hL μ j h.2).2.1]
      exact LinearMap.mem_range_self _ _
    · rw [LinearMap.zero_apply]; exact zero_mem _
  have hr0 : ∀ μ, ∃ r : C.CC b μ 0 →ₗ[ℂ] EE.T, ∀ x (w : C.CC b μ 0), ⟪x, r w⟫_ℂ = C.ipE b (jE x) w :=
    fun μ => hp_riesz (hE0 μ) jE (jE_mem μ)
  choose r0 hr0 using hr0
  have hR : ∀ μ j, ∃ r : C.CC b μ j →ₗ[ℂ] (Mult μ j).T, j ≤ D.R.m - 1 →
      ∀ x (w : C.CC b μ j), ⟪x, r w⟫_ℂ = C.ipP b μ j (jM μ j x) w := by
    intro μ j
    by_cases hj : j ≤ D.R.m - 1
    · obtain ⟨r, hr⟩ := hp_riesz ((hle μ).2.2.2 j hj).2 (jM μ j) (jM_mem μ j)
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose R hR using hR
  have memX : ∀ μ, U μ → ∀ y, jX μ y ∈ C.CCX b μ := fun μ hU y =>
    (hle μ).2.1 (by rw [← (hX μ hU).2.1]; exact LinearMap.mem_range_self (jX μ) y)
  let io : ∀ μ j, (Mult μ (j + 1)).T →ₗ[ℂ] (Mult μ j).T := fun μ j =>
    if hU : U μ then
      if h0 : j = 0 then
        (heqv (show Mult μ j = EE by rw [h0]; exact chSel_zero)).symm.toLinearEquiv.toLinearMap ∘ₗ r0 μ ∘ₗ
          C.ioC b μ 0 ∘ₗ (jM μ 1 ∘ₗ (heqv (show Mult μ (j + 1) = Mult μ 1 by rw [h0])).toLinearEquiv.toLinearMap).codRestrict
            (C.CC b μ 1) (fun y => jM_mem μ 1 _)
      else if hT : j + 1 = D.R.m then
        (heqv (show Mult μ (D.R.m - 1) = Mult μ j by rw [show D.R.m - 1 = j by omega])).toLinearEquiv.toLinearMap ∘ₗ
          R μ (D.R.m - 1) ∘ₗ C.ioX b μ ∘ₗ
          (jX μ ∘ₗ (heqv (show Mult μ (j + 1) = Top μ by rw [hT]; exact chSel_top (by omega))).toLinearEquiv.toLinearMap).codRestrict
            (C.CCX b μ) (fun y => memX μ hU _)
      else
        R μ j ∘ₗ C.ioC b μ j ∘ₗ (jM μ (j + 1)).codRestrict (C.CC b μ (j + 1)) (jM_mem μ (j + 1))
    else 0
  refine ⟨EE, Mult, fun μ => heqv (chSel_zero (m := D.R.m) (A := EE) (B := Top μ) (L := Lo μ)),
    fun μ => heqv (chSel_top (m := D.R.m) (A := EE) (B := Top μ) (L := Lo μ) (by omega)), io, jE, jM,
    hEi, hEr, hEip, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ _ j h1 h2
    have hh : 1 ≤ j ∧ j ≤ D.R.m - 1 := ⟨h1, h2⟩
    obtain ⟨hi, hr, hip⟩ := hL μ j h2
    dsimp only [jM]
    rw [dite_eq_left hh]
    refine ⟨?_, ?_, ?_⟩
    · rw [LinearMap.coe_comp]; exact hi.comp (LinearEquiv.injective _)
    · rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), hr]
    · intro x x'
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hip]
      exact (LinearIsometryEquiv.inner_map_map _ x x').symm
  · intro μ hU x v h
    dsimp only [io]
    rw [dite_eq_left hU, dite_eq_left rfl]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply]
    exact hr0 μ x _
  · intro μ hU j h1 h2 x v h
    dsimp only [io]
    rw [dite_eq_left hU, dite_eq_right (by omega), dite_eq_right (by omega)]
    rw [LinearMap.comp_apply, hR μ j (by omega)]
    rfl
  · intro μ hU x v v' hv h
    dsimp only [io]
    rw [dite_eq_left hU, dite_eq_right (by omega), dite_eq_left (by omega)]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [heqv_self, hR μ _ le_rfl]
    refine congrArg (fun y => C.ipP b μ (D.R.m - 1) (jM μ (D.R.m - 1) x)
      ((C.ioX b μ y : C.CC b μ (D.R.m - 1)) : C.Amb (D.R.m - 1))) (Subtype.ext ?_)
    exact congrArg (jX μ) (heqv_heq _ _ v' v hv)
  · intro μ hU j
    dsimp only [io]
    rw [dite_eq_right hU]

end GlobalTheory.ChainHilb
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.HFld


open Classical in
def chiC {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) :
    Fin B.R.m → IsDedekindDomain.HeightOneSpectrum (𝓞 B.host.E) → 𝓞 B.host.E → ℂ :=
  fun j w y =>
    if h : w ∈ (B.primes px).vGs then
      if hu : IsUnit (Ideal.Quotient.mk w.asIdeal y) then B.embLL ((I.Ch.chi j ⟨w, h⟩ hu.unit : B.LLˣ) : B.LL) else 0
    else 0


open Classical in
def qC {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) :
    Formalism.L2.Host.HChar B.host.E → Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 B.host.E)) :=
  fun ξ => if h : ∃ a, I.xi a = ξ then I.Q h.choose else ∅

def SameCfg (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px) (B' : Base) (px' : PreX B'.toPre) (I' : Col2.ColIn B' px') : Prop :=
  B.toPre = B'.toPre ∧ HEq I.C I'.C ∧ HEq (Set.range I.xi) (Set.range I'.xi) ∧ HEq px.piG px'.piG ∧ HEq (chiC I) (chiC I') ∧
    HEq (qC I) (qC I')

end GlobalTheory.Mem.HFld

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockPolynomialVector_change_orthonormalBases_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, (BS τ)ᴴ * gramAt D S τ * BS τ = 1) → ∀ (k : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ, u τ ∈ Matrix.unitaryGroup (Fin S.rank) ℂ) → ∀ f, IsThetaFunO ψ S T f → ∀ P : PolF D T.rank S.rank, pureTensorO ψ θ S T (fun _ => 1) (cart M) (fun τ => BS τ * u τ) (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (fsub M.ε k u P) := by
  first | exact @GlobalTheory.FockBasis.pureTensorO_basis | exact GlobalTheory.FockBasis.pureTensorO_basis | (intros; apply GlobalTheory.FockBasis.pureTensorO_basis <;> assumption)
end
