module

public import Development.WeilBound.ThetaLifts.SphericalLattices.Bundle001
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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

namespace PositivityTheory.Sph

open ValuativeRel Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem latt_eq {n d : ℕ} {t : k} (ht : t ≠ 0) (Y₀ : Matrix (Fin n) (Fin d) k) :
    ∃ h : GL (Fin d) k, ∀ v : Fin d → k, v ∈ latt t Y₀ ↔ ∀ j, (v ᵥ* h.1) j ∈ 𝒪[k] := by
  classical
  set L := latt t Y₀ with hL
  have : Module.Finite 𝒪[k] L := by
    rw [hL, latt]
    exact Module.Finite.span_of_finite _ ((Set.finite_range _).union (Set.finite_range _))
  obtain ⟨m, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := 𝒪[k]) (M := L)
  set w : Fin m → (Fin d → k) := fun i => (b i : Fin d → k) with hw
  have hwL : ∀ i, w i ∈ L := fun i => (b i).2
  have hli : LinearIndependent k w := by
    rw [← LinearIndependent.iff_fractionRing 𝒪[k] k]
    exact b.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hsum : ∀ x (hx : x ∈ L), x = ∑ i, ((b.repr ⟨x, hx⟩ i : 𝒪[k]) : k) • w i := by
    intro x hx
    have e := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    refine e.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact (algebraMap_smul k _ _).symm
  have hLw : ∀ x ∈ L, x ∈ Submodule.span k (Set.range w) := by
    intro x hx
    rw [hsum x hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span k (Set.range w) := by
    intro x _
    have hx : x = ∑ j, (t⁻¹ * x j) • (t • Pi.single j (1 : k) : Fin d → k) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
      rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ ht, one_mul]
    rw [hx]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hLw _ ?_)
    exact Submodule.subset_span (Or.inr ⟨j, rfl⟩)
  let bk := Module.Basis.mk hli hsp
  have hbk : ∀ i, bk i = w i := fun i => by simp [bk]
  have hm : m = d := by
    have := Module.finrank_eq_card_basis bk
    simpa using this.symm
  have hmem : ∀ v, v ∈ L ↔ ∀ i, bk.equivFun v i ∈ 𝒪[k] := by
    intro v
    constructor
    · intro hv i
      have : bk.equivFun v = fun i => ((b.repr ⟨v, hv⟩ i : 𝒪[k]) : k) := by
        apply bk.equivFun.symm.injective
        rw [LinearEquiv.symm_apply_apply, Module.Basis.equivFun_symm_apply]
        simpa only [hbk] using hsum v hv
      rw [this]
      exact (b.repr _ i).2
    · intro hc
      rw [← bk.sum_equivFun v]
      refine L.sum_mem fun i _ => ?_
      rw [hbk i, show bk.equivFun v i • w i = (⟨bk.equivFun v i, hc i⟩ : 𝒪[k]) • w i from rfl]
      exact L.smul_mem _ (hwL i)
  let bk' := bk.reindex (finCongr hm)
  let hmat : Matrix (Fin d) (Fin d) k := (LinearMap.toMatrix' bk'.equivFun.toLinearMap)ᵀ
  let Bmat : Matrix (Fin d) (Fin d) k := (LinearMap.toMatrix' bk'.equivFun.symm.toLinearMap)ᵀ
  have hB : hmat * Bmat = 1 := by
    simp only [hmat, Bmat, ← Matrix.transpose_mul, ← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨hmat, Bmat, hB, mul_eq_one_comm.mp hB⟩, fun v => ?_⟩
  have key : v ᵥ* hmat = bk'.equivFun v := by
    simp [hmat, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  have hre : ∀ j, bk'.equivFun v j = bk.equivFun v ((finCongr hm).symm j) := by
    intro j
    simp [bk', Module.Basis.equivFun_apply]
  show v ∈ L ↔ ∀ j, (v ᵥ* hmat) j ∈ 𝒪[k]
  rw [key, hmem]
  simp only [hre]
  exact ⟨fun H j => H _, fun H i => by simpa using H (finCongr hm i)⟩

end PositivityTheory.Sph

end
end

section

noncomputable section

namespace PositivityTheory.Sph

open ValuativeRel Matrix

theorem exists_isUnit_add_mul {K : Type} [Field K] {n : ℕ} (A D : Matrix (Fin n) (Fin n) K)
    (h : ∀ x, A *ᵥ x = 0 → D *ᵥ x = 0 → x = 0) : ∃ C : Matrix (Fin n) (Fin n) K, IsUnit (A + C * D).det := by
  classical
  obtain ⟨R, hR⟩ := Submodule.exists_isCompl (LinearMap.range (Matrix.toLin' A))
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl ((LinearMap.ker (Matrix.toLin' A)).map (Matrix.toLin' D))
  have h1 : Module.finrank K ((LinearMap.ker (Matrix.toLin' A)).map (Matrix.toLin' D))
      = Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
    have hker : LinearMap.ker ((Matrix.toLin' D).domRestrict (LinearMap.ker (Matrix.toLin' A))) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro w hw
      have hw1 : A *ᵥ (w : Fin n → K) = 0 := by
        have := w.2
        rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      have hw2 : D *ᵥ (w : Fin n → K) = 0 := by
        simpa [Matrix.toLin'_apply] using hw
      exact Subtype.ext (h _ hw1 hw2)
    rw [← LinearMap.range_domRestrict]
    exact LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hker)
  have h2 : Module.finrank K R = Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
    have e1 := Submodule.finrank_add_eq_of_isCompl hR
    have e2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
    omega
  let e := LinearEquiv.ofFinrankEq _ _ (h1.trans h2.symm)
  let proj := Submodule.linearProjOfIsCompl _ _ hU'
  let c : (Fin n → K) →ₗ[K] (Fin n → K) := R.subtype ∘ₗ e.toLinearMap ∘ₗ proj
  refine ⟨LinearMap.toMatrix' c, ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have key : ∀ x, (A + LinearMap.toMatrix' c * D) *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec] at hx
    have hcR : c (D *ᵥ x) ∈ R := (e (proj (D *ᵥ x))).2
    have haR : A *ᵥ x ∈ LinearMap.range (Matrix.toLin' A) := ⟨x, Matrix.toLin'_apply A x⟩
    have hax : A *ᵥ x = 0 := by
      have hneg : A *ᵥ x = -(c (D *ᵥ x)) := eq_neg_of_add_eq_zero_left hx
      have hmem : A *ᵥ x ∈ R := hneg ▸ R.neg_mem hcR
      exact (Submodule.disjoint_def.mp hR.disjoint) _ haR hmem
    have hcx : c (D *ᵥ x) = 0 := by
      rw [hax, zero_add] at hx
      exact hx
    have hDU : D *ᵥ x ∈ (LinearMap.ker (Matrix.toLin' A)).map (Matrix.toLin' D) :=
      ⟨x, by rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.toLin'_apply]; exact hax,
        Matrix.toLin'_apply D x⟩
    have hproj : proj (D *ᵥ x) = ⟨D *ᵥ x, hDU⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hU' ⟨_, hDU⟩
    have hex : e ⟨D *ᵥ x, hDU⟩ = 0 := by
      have h3 : ((e (proj (D *ᵥ x)) : R) : Fin n → K) = 0 := hcx
      rw [hproj] at h3
      exact Subtype.ext h3
    have hDx : D *ᵥ x = 0 := by
      have h4 := congrArg Subtype.val (e.injective (hex.trans (map_zero e).symm))
      exact h4
    exact h x hax hDx
  intro x y hxy
  have hsub : (A + LinearMap.toMatrix' c * D) *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  exact sub_eq_zero.mp (key _ hsub)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem orbit {n d : ℕ} {t : k} {Y Y' : Matrix (Fin n) (Fin d) k} (h1 : Below t Y Y') (h2 : Below t Y' Y) :
    ∃ U : Matrix (Fin n) (Fin n) 𝒪[k], IsUnit U.det ∧ ∃ Z, IntM Z ∧ Y = U.map (algebraMap 𝒪[k] k) * Y' + t • Z := by
  classical
  obtain ⟨A, Z, hZ, hY⟩ := h1
  obtain ⟨B, Z', hZ', hY'⟩ := h2
  have hsurj := IsLocalRing.residue_surjective (R := 𝒪[k])
  obtain ⟨Cb, hCb⟩ := exists_isUnit_add_mul (A.map (IsLocalRing.residue 𝒪[k]))
    (1 - B.map (IsLocalRing.residue 𝒪[k]) * A.map (IsLocalRing.residue 𝒪[k])) (by
      intro x hx1 hx2
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hx1, Matrix.mulVec_zero,
        sub_zero] at hx2
      exact hx2)
  let C : Matrix (Fin n) (Fin n) 𝒪[k] := Cb.map (Function.surjInv hsurj)
  have hC : C.map (IsLocalRing.residue 𝒪[k]) = Cb := by
    ext i j
    simp only [C, Matrix.map_apply]
    exact Function.surjInv_eq hsurj _
  let FinalForm : Matrix (Fin n) (Fin d) 𝒪[k] := Matrix.of fun i j => ⟨Z i j, hZ i j⟩
  let Zo' : Matrix (Fin n) (Fin d) 𝒪[k] := Matrix.of fun i j => ⟨Z' i j, hZ' i j⟩
  have hZo : FinalForm.map (algebraMap 𝒪[k] k) = Z := by
    ext i j
    rfl
  have hZo' : Zo'.map (algebraMap 𝒪[k] k) = Z' := by
    ext i j
    rfl
  refine ⟨A + C * (1 - B * A), ?_, (FinalForm - C * (B * FinalForm + Zo')).map (algebraMap 𝒪[k] k), ?_, ?_⟩
  · apply isUnit_of_map_unit (IsLocalRing.residue 𝒪[k])
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add (IsLocalRing.residue 𝒪[k]) (map_add _),
      Matrix.map_mul, Matrix.map_sub (IsLocalRing.residue 𝒪[k]) (map_sub _), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_mul, hC]
    exact hCb
  · intro i j
    exact ((FinalForm - C * (B * FinalForm + Zo')) i j).2
  · have hU : (A + C * (1 - B * A)).map (algebraMap 𝒪[k] k)
        = A.map (algebraMap 𝒪[k] k) + C.map (algebraMap 𝒪[k] k)
          * (1 - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k)) := by
      rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_sub _ (map_sub _),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_mul]
    have hW : (FinalForm - C * (B * FinalForm + Zo')).map (algebraMap 𝒪[k] k)
        = Z - C.map (algebraMap 𝒪[k] k) * (B.map (algebraMap 𝒪[k] k) * Z + Z') := by
      rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_add _ (map_add _), Matrix.map_mul, hZo, hZo']
    have h2' : Y' = B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k) * Y'
        + t • (B.map (algebraMap 𝒪[k] k) * Z + Z') := by
      calc Y' = B.map (algebraMap 𝒪[k] k) * Y + t • Z' := hY'
        _ = B.map (algebraMap 𝒪[k] k) * (A.map (algebraMap 𝒪[k] k) * Y' + t • Z) + t • Z' := by rw [hY]
        _ = _ := by
          rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_assoc, smul_add]
          abel
    have e1 : Y' - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k) * Y'
        = t • (B.map (algebraMap 𝒪[k] k) * Z + Z') := by
      rw [sub_eq_iff_eq_add']
      exact h2'
    have e2 : (A.map (algebraMap 𝒪[k] k) + C.map (algebraMap 𝒪[k] k)
          * (1 - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k))) * Y'
        = A.map (algebraMap 𝒪[k] k) * Y' + C.map (algebraMap 𝒪[k] k)
          * (Y' - B.map (algebraMap 𝒪[k] k) * A.map (algebraMap 𝒪[k] k) * Y') := by
      rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
    rw [hU, hW, e2, e1, Matrix.mul_smul, smul_sub]
    conv_lhs => rw [hY]
    abel

end PositivityTheory.Sph

end
end
