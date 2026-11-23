module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle025
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle027
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle028
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.SgAlg Matrix

namespace GlobalTheory

theorem witt_free_tuples_fin {E : Type} [CommRing E] (σ : E →+* E) (hσ : IsQA σ) {n k : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermU σ J) (Y Y' : Matrix (Fin n) (Fin k) E)
    (hY : Free Y) (hY' : Free Y') (hP : pairM σ J Y Y = pairM σ J Y' Y') :
    ∃ g, IsUn σ J g ∧ g * Y = Y' := by
  rcases GlobalTheory.T.isField_or_exists_swapped_idempotent_of_quadraticEtale σ hσ with hF | hS
  · letI := hF.toField
    exact GlobalTheory.T.witt_extension_hermitian_frames σ hσ J hJ Y Y' hY hY' hP
  · exact GlobalTheory.T.witt_free_tuples_split_quadratic_etale σ hσ hS J hJ Y Y' hY hY' hP

theorem free_reindex {E : Type} [CommRing E] {n : ℕ} {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (e : b ≃ a) {X : Matrix (Fin n) a E} (hX : Free X) :
    Free (X.submatrix id e) := by
  obtain ⟨L, hL⟩ := hX
  refine ⟨L.submatrix e id, ?_⟩
  have h : L.submatrix e id * X.submatrix id e = (L * X).submatrix e e := by
    ext i j
    simp [Matrix.mul_apply]
  rw [h, hL]
  simp

theorem pairM_reindex {E : Type} [CommRing E] (σ : E →+* E) {n : ℕ} {a b : Type} [Fintype a]
    (e : b ≃ a) (J : Matrix (Fin n) (Fin n) E) (X X' : Matrix (Fin n) a E) :
    pairM σ J (X'.submatrix id e) (X.submatrix id e) = (pairM σ J X' X).submatrix e e := by
  ext i j
  simp [pairM, cT, Matrix.mul_apply]

theorem witt_free_tuples {E : Type} [CommRing E] (σ : E →+* E) (hσ : IsQA σ) {n : ℕ} {a : Type}
    [Fintype a] [DecidableEq a] (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermU σ J)
    (X X' : Matrix (Fin n) a E) (hX : Free X) (hX' : Free X')
    (hP : pairM σ J X X = pairM σ J X' X') : ∃ g, IsUn σ J g ∧ g * X = X' := by
  let e : Fin (Fintype.card a) ≃ a := (Fintype.equivFin a).symm
  obtain ⟨g, hg, hgX⟩ := witt_free_tuples_fin σ hσ J hJ (X.submatrix id e) (X'.submatrix id e)
    (free_reindex e hX) (free_reindex e hX')
    (by rw [pairM_reindex, pairM_reindex, hP])
  refine ⟨g, hg, ?_⟩
  ext i j
  have h := congrFun (congrFun hgX i) (e.symm j)
  simpa [Matrix.mul_apply] using h

end GlobalTheory
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem encard_eq_tsum_fiber {X Z : Type*} (q : X → Z) (Q : X → Prop) :
    (({x | Q x} : Set X).encard : ℝ≥0∞)
      = ∑' z : Z, (({x | q x = z ∧ Q x} : Set X).encard : ℝ≥0∞) := by
  have e : ∀ S : Set X, (S.encard : ℝ≥0∞) = ∑' x, S.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro S
    rw [← ENNReal.tsum_set_one, tsum_subtype S (fun _ => (1 : ℝ≥0∞))]
  simp only [e]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  rw [tsum_eq_single (q x)]
  · simp [Set.indicator]
  · intro z hz
    have : ¬ q x = z := fun h => hz h.symm
    simp [Set.indicator, this]

theorem encard_orbit_fiber {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (H : Subgroup G) (P : X → Prop) (π : X → Y)
    (hP : ∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x) (x : X) (hx : P x)
    (hfin : (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) ≠ 0) :
    ({z | (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x ∧
        P z ∧ π z = π x} : Set X).encard
      = (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) := by
  have h1 : ({z | (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x ∧
        P z ∧ π z = π x} : Set X)
      = MulAction.orbit (↥(H ⊓ MulAction.stabilizer G (π x))) x := by
    ext z
    simp only [Set.mem_setOf_eq, Quotient.eq'', MulAction.orbitRel_apply]
    constructor
    · rintro ⟨⟨h, rfl⟩, -, hz⟩
      have h2 := (hP h h.2 x hx).2
      exact ⟨⟨h, h.2, h2.symm.trans hz⟩, rfl⟩
    · rintro ⟨⟨h, hh, hs⟩, rfl⟩
      have h2 := hP h hh x hx
      exact ⟨⟨⟨h, hh⟩, rfl⟩, h2.1, h2.2.trans hs⟩
  have h2 : (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x))
      = (MulAction.orbit (↥(H ⊓ MulAction.stabilizer G (π x))) x).ncard := by
    rw [← MulAction.index_stabilizer, Subgroup.relIndex]
    congr 1
    ext ⟨h, hh, hs⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    exact ⟨fun a => a.2, fun a => ⟨hh, a⟩⟩
  rw [h1, h2]
  rw [h2] at hfin
  exact (Set.finite_of_ncard_ne_zero hfin).cast_ncard_eq.symm

theorem mass_orbits_eq_tsum_fiber : ∀ {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y] (H K0 : Subgroup G) (P : X → Prop) (π : X → Y), K0 ≤ H → (∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x ∧ invVol K0 (H ⊓ MulAction.stabilizer G (h • x)) = invVol K0 (H ⊓ MulAction.stabilizer G x)) → (∀ x, P x → K0.relIndex (H ⊓ MulAction.stabilizer G x) ≠ 0 ∧ (H ⊓ MulAction.stabilizer G x).relIndex K0 ≠ 0 ∧ K0.relIndex (H ⊓ MulAction.stabilizer G (π x)) ≠ 0 ∧ (H ⊓ MulAction.stabilizer G (π x)).relIndex K0 ≠ 0) → (∑' o : MulAction.orbitRel.Quotient H X, if P o.out then ENNReal.ofReal (invVol K0 (H ⊓ MulAction.stabilizer G o.out)) else 0) = ∑' c : MulAction.orbitRel.Quotient H Y, ENNReal.ofReal (invVol K0 (H ⊓ MulAction.stabilizer G c.out)) * (({x | P x ∧ π x = c.out} : Set X).encard : ℝ≥0∞) := by
  intro G X Y _ _ _ H K0 P π _ hP hc
  have hP' : ∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x :=
    fun h hh x hx => ⟨(hP h hh x hx).1, (hP h hh x hx).2.1⟩
  simp only [fun c : MulAction.orbitRel.Quotient H Y =>
    encard_eq_tsum_fiber (fun z : X => (Quotient.mk'' z : MulAction.orbitRel.Quotient H X))
      (fun x => P x ∧ π x = c.out), ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun o => ?_
  have hmem : ∀ z : X, (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = o →
      ∃ h ∈ H, h • z = o.out := by
    intro z hz
    have : (Quotient.mk'' o.out : MulAction.orbitRel.Quotient H X) = Quotient.mk'' z := by
      rw [hz]; exact Quotient.out_eq' o
    rw [Quotient.eq'', MulAction.orbitRel_apply] at this
    obtain ⟨h, hh⟩ := this
    exact ⟨h, h.2, hh⟩
  split_ifs with ho
  · set c0 : MulAction.orbitRel.Quotient H Y := Quotient.mk'' (π o.out) with hc0
    rw [tsum_eq_single c0]
    · have : (Quotient.mk'' c0.out : MulAction.orbitRel.Quotient H Y) = Quotient.mk'' (π o.out) :=
        Quotient.out_eq' c0
      rw [Quotient.eq'', MulAction.orbitRel_apply] at this
      obtain ⟨⟨h, hh⟩, hy⟩ := this
      have hy' : h • π o.out = c0.out := hy
      obtain ⟨p1, p2, p3⟩ := hP h hh _ ho
      have ho' : o = Quotient.mk'' (h • o.out) := by
        conv_lhs => rw [← Quotient.out_eq' o]
        symm
        rw [Quotient.eq'', MulAction.orbitRel_apply]
        exact ⟨⟨h, hh⟩, rfl⟩
      rw [← p3, ← hy', ← p2]
      generalize h • o.out = x at p1 ho'
      obtain ⟨a1, a2, a3, a4⟩ := hc x p1
      have hle : H ⊓ MulAction.stabilizer G x ≤ H ⊓ MulAction.stabilizer G (π x) := by
        rintro g ⟨g1, g2⟩
        refine ⟨g1, ?_⟩
        have g3 : g • x = x := g2
        have := (hP' g g1 x p1).2
        rw [g3] at this
        exact this.symm
      obtain ⟨-, -, b, -⟩ := invVol_mul_pos_le_conj K0 _ _ a3 a4 a1 a2
      rw [ho', encard_orbit_fiber H P π hP' x p1 (Subgroup.relIndex_ne_zero_trans a2 a3), b hle,
        ENNReal.ofReal_mul' (Nat.cast_nonneg _)]
      simp
    · intro c hne
      have : ({x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ P x ∧ π x = c.out} :
          Set X) = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2, h3⟩
        obtain ⟨h, hh, e⟩ := hmem z h1
        apply hne
        rw [hc0, ← e, (hP' h hh z h2).2, h3]
        conv_lhs => rw [← Quotient.out_eq' c]
        symm
        rw [Quotient.eq'', MulAction.orbitRel_apply]
        exact ⟨⟨h, hh⟩, rfl⟩
      rw [this]; simp
  · symm
    refine ENNReal.tsum_eq_zero.2 fun c => ?_
    have : ({x | (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = o ∧ P x ∧ π x = c.out} :
        Set X) = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, -⟩
      obtain ⟨h, hh, e⟩ := hmem z h1
      exact ho (e ▸ (hP' h hh z h2).1)
    rw [this]; simp

end GlobalTheory.HL
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem invVol_conj_modular : ∀ {G : Type} [Group G] (H K : Subgroup G), K ≤ H → (∀ h ∈ H, K.relIndex (MulAut.conj h • K) ≠ 0 ∧ (MulAut.conj h • K).relIndex K ≠ 0) → (∀ a ∈ H, ∀ b ∈ H, invVol K (MulAut.conj (a * b) • K) = invVol K (MulAut.conj a • K) * invVol K (MulAut.conj b • K)) ∧ (∀ a ∈ H, 0 < invVol K (MulAut.conj a • K)) ∧ (∀ α : G ≃* G, K.map α.toMonoidHom = K → ∀ a ∈ H, invVol K (MulAut.conj (α a) • K) = invVol K (MulAut.conj a • K)) ∧ ∀ K' : Subgroup G, K.relIndex K' ≠ 0 → K'.relIndex K ≠ 0 → ∀ a ∈ H, invVol K (MulAut.conj a • K') = invVol K (MulAut.conj a • K) * invVol K K' ∧ (MulAut.conj a • K' = K' → invVol K (MulAut.conj a • K) = 1) := by
  intro G _ H K _ hc
  have e : ∀ (g : G) (A B : Subgroup G),
      (MulAut.conj g • A).relIndex (MulAut.conj g • B) = A.relIndex B := fun g A B =>
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A B
      (MulAut.conj g).injective
  have key : ∀ K' : Subgroup G, K.relIndex K' ≠ 0 → K'.relIndex K ≠ 0 → ∀ a ∈ H,
      invVol K (MulAut.conj a • K') = invVol K (MulAut.conj a • K) * invVol K K' := by
    intro K' h1 h2 a ha
    have p1 : K.relIndex (MulAut.conj a • K') ≠ 0 :=
      Subgroup.relIndex_ne_zero_trans (hc a ha).1 (by rw [e]; exact h1)
    have p2 : (MulAut.conj a • K').relIndex K ≠ 0 :=
      Subgroup.relIndex_ne_zero_trans (by rw [e]; exact h2) (hc a ha).2
    rw [(invVol_mul_pos_le_conj K (MulAut.conj a • K) _ (hc a ha).1 (hc a ha).2 p1 p2).1,
      (invVol_mul_pos_le_conj K K' K' h1 h2 h1 h2).2.2.2 a]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    rw [map_mul, mul_smul]
    exact key _ (hc b hb).1 (hc b hb).2 a ha
  · intro a ha
    exact (invVol_mul_pos_le_conj K _ _ (hc a ha).1 (hc a ha).2 (hc a ha).1 (hc a ha).2).2.1
  · intro α hα a _
    have h1 : (MulAut.conj a • K).map α.toMonoidHom
        = MulAut.conj (α a) • K.map α.toMonoidHom := by
      change (K.map (MulAut.conj a).toMonoidHom).map α.toMonoidHom
        = (K.map α.toMonoidHom).map (MulAut.conj (α a)).toMonoidHom
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp
    rw [hα] at h1
    have f : ∀ A B : Subgroup G,
        (A.map α.toMonoidHom).relIndex (B.map α.toMonoidHom) = A.relIndex B := fun A B =>
      Subgroup.relIndex_map_map_of_injective (f := α.toMonoidHom) A B α.injective
    have f1 := f K (MulAut.conj a • K)
    have f2 := f (MulAut.conj a • K) K
    rw [hα, h1] at f1 f2
    rw [invVol, invVol, f1, f2]
  · intro K' h1 h2 a ha
    refine ⟨key K' h1 h2 a ha, fun h => ?_⟩
    have k := key K' h1 h2 a ha
    rw [h] at k
    have pos := (invVol_mul_pos_le_conj K K' K' h1 h2 h1 h2).2.1
    exact mul_right_cancel₀ pos.ne' (by rw [← k, one_mul])

end GlobalTheory.HL
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate

namespace GlobalTheory.HL.GaussSummand

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem hf_add_left (x y z : Fin n → E) : hf L Hm (x + y) z = hf L Hm x z + hf L Hm y z := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y z : Fin n → E) : hf L Hm x (y + z) = hf L Hm x y + hf L Hm x z := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (c : E) (x z : Fin n → E) : hf L Hm (c • x) z = c * hf L Hm x z := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (c : E) (x z : Fin n → E) : hf L Hm x (c • z) = L.cj c * hf L Hm x z := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem hf_zero_left (z : Fin n → E) : hf L Hm 0 z = 0 := by
  simp [hf]

theorem hf_sum_left {ι : Type*} (s : Finset ι) (x : ι → Fin n → E) (z : Fin n → E) :
    hf L Hm (∑ a ∈ s, x a) z = ∑ a ∈ s, hf L Hm (x a) z := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, ih]

theorem cj_hf (h : IsHerm L Hm) (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by
  have h' : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun h i) j

  simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end

theorem norm_gauss_sum_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ψ : AddChar F ℂ), (∀ x : F, ‖ψ x‖ = 1) → (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ (UU : Submodule L.O (Fin n → E)), (∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O) → ∀ (ρ : ℕ) (e : Fin ρ → Fin n → E), (∀ a, e a ∈ UU) → (∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) → ∀ (i N : ℕ), 1 ≤ i → i ≤ N → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ∀ (χ : AddChar (Fin n → E) ℂ), (∀ u, ‖χ u‖ = 1) → (∀ u ∈ UU, χ (algebraMap F E ((ϖ : F) ^ N) • u) = 1) → ∀ (R : Finset (Fin n → E)) (nrm : (Fin n → E) → F), (∀ u, algebraMap F E (nrm u) = hf L Hm u u) → (∀ u ∈ R, u ∈ UU) → (∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y) → ‖∑ u ∈ R, ψ (t * nrm u) * χ u‖ ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(i * ρ : ℤ)) := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH ϖ hϖ ψ hψ1 hψ UU hUU d e heU hee i N _ hiN t u₀ ht χ hχ1 hχ
    R nrm hnrm hRO hR
  obtain ⟨-, -, hdual, -, hint, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hO : ∀ c : 𝒪[F], algebraMap F E c ∈ L.O := fun c => (hint c).2 c.2
  have hsm : ∀ c ∈ L.O, ∀ x ∈ UU, c • x ∈ UU := fun c hc x hx =>
    UU.smul_mem (⟨c, hc⟩ : L.O) hx
  let I : ℕ → Ideal L.O := fun j => Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)}
  have hI : ∀ j (x : L.O), x ∈ I j ↔ ∃ c ∈ L.O, (x : E) = algebraMap F E ((ϖ : F) ^ j) * c := by
    intro j x
    have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)}
        = {⟨algebraMap F E ((ϖ : F) ^ j), hO (ϖ ^ j)⟩} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff]
    simp only [I]
    rw [hset, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, c.2, congrArg Subtype.val hc⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨⟨c, hc⟩, Subtype.ext h⟩
  let P₀ : AddSubgroup (Fin d → L.O) := AddSubgroup.pi Set.univ fun _ => (I i).toAddSubgroup
  have hP₀ : ∀ x, x ∈ P₀ ↔ ∀ a, ∃ c ∈ L.O, (x a : E) = algebraMap F E ((ϖ : F) ^ i) * c := by
    intro x
    simp only [P₀, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup, hI]
  have hidx₀ : P₀.index = (resQ ϖ ^ (i * d)) ^ 2 := by
    have : (I i).toAddSubgroup.index = resQ ϖ ^ (2 * i) := hcard i
    simp only [P₀]
    rw [AddSubgroup.index_pi, Finset.prod_const, this, Finset.card_univ, Fintype.card_fin]
    ring
  let φ : UU →+ (Fin d → L.O) :=
    { toFun := fun m a => ⟨hf L Hm m (e a), hUU _ m.2 _ (heU a)⟩
      map_zero' := funext fun a => Subtype.ext (hf_zero_left L Hm _)
      map_add' := fun x y => funext fun a => Subtype.ext (hf_add_left L Hm _ _ _) }
  have hφ : Function.Surjective φ := fun c => by
    refine ⟨⟨∑ b, (c b : E) • e b, UU.sum_mem fun b _ => hsm _ (c b).2 _ (heU b)⟩,
      funext fun a => Subtype.ext ?_⟩
    show hf L Hm (∑ b, (c b : E) • e b) (e a) = c a
    simp [hf_sum_left, hf_smul_left, hee]
  let Q : AddSubgroup UU := P₀.comap φ
  have hQ : ∀ x : UU, x ∈ Q ↔
      ∀ a, ∃ c ∈ L.O, hf L Hm x (e a) = algebraMap F E ((ϖ : F) ^ i) * c := fun x => hP₀ (φ x)
  have hidx : Q.index = (resQ ϖ ^ (i * d)) ^ 2 := by
    rw [← hidx₀]; exact AddSubgroup.index_comap_of_surjective P₀ hφ
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hiN
  let P : AddSubgroup UU :=
    { carrier := {x | ∃ y ∈ UU, (x : Fin n → E) = algebraMap F E ((ϖ : F) ^ (i + k)) • y}
      zero_mem' := ⟨0, UU.zero_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨x', hx', hx⟩ ⟨y', hy', hy⟩
        exact ⟨x' + y', UU.add_mem hx' hy', by rw [Submodule.coe_add, hx, hy, smul_add]⟩
      neg_mem' := by
        rintro x ⟨x', hx', hx⟩
        exact ⟨-x', UU.neg_mem hx', by rw [Submodule.coe_neg, hx, smul_neg]⟩ }
  have hP : ∀ x : UU, x ∈ P ↔
      ∃ y ∈ UU, (x : Fin n → E) = algebraMap F E ((ϖ : F) ^ (i + k)) • y := fun _ => Iff.rfl
  have hPQ : P ≤ Q := fun x hx => (hQ x).2 fun a => by
    obtain ⟨y, hy, h⟩ := (hP x).1 hx
    refine ⟨algebraMap F E ((ϖ : F) ^ k) * hf L Hm y (e a),
      L.O.mul_mem (hO (ϖ ^ k)) (hUU _ hy _ (heU a)), ?_⟩
    rw [h, hf_smul_left, pow_add, map_mul, mul_assoc]
  have hιinj : Function.Injective (Subtype.val : UU → Fin n → E) := Subtype.val_injective
  have hrange : ∀ u ∈ R, u ∈ Set.range (Subtype.val : UU → Fin n → E) :=
    fun u hu => ⟨⟨u, hRO u hu⟩, rfl⟩
  let R' := R.preimage (Subtype.val : UU → Fin n → E) hιinj.injOn
  have hτ : algebraMap F E t * algebraMap F E ((ϖ : F) ^ i)
      = algebraMap F E ((u₀ : 𝒪[F]) : F) := by rw [← map_mul, ht]
  have key := GaussSum.sq_norm_sum_reps_mul_index_le P Q hPQ R' ?_
    (fun m => ψ (t * nrm m) * χ m) (fun m => by rw [norm_mul, hψ1, hχ1, mul_one]) ?_ ?_
  · rw [Finset.sum_preimage Subtype.val R hιinj.injOn (fun u => ψ (t * nrm u) * χ u)
      (fun u hu h => (h (hrange u hu)).elim), Finset.card_preimage, hidx,
      Finset.filter_true_of_mem hrange, Nat.cast_pow, ← mul_pow] at key
    have hq0 : (0 : ℝ) < resQ ϖ := by exact_mod_cast (by omega : 0 < resQ ϖ)
    have h := (sq_le_sq₀ (by positivity) (by positivity)).1 key
    rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact_mod_cast h
  · intro u
    obtain ⟨w, ⟨hw, hw'⟩, huniq⟩ := hR u u.2
    obtain ⟨w, rfl⟩ := hrange w hw
    refine ⟨w, ⟨Finset.mem_preimage.2 hw, (hP _).2 hw'⟩, fun y hy => hιinj ?_⟩
    exact huniq _ ⟨Finset.mem_preimage.1 hy.1, (hP _).1 hy.2⟩
  · intro u p hp
    obtain ⟨c, hc, hpc⟩ := (hP p).1 hp
    have h1 : χ p = 1 := by rw [hpc, hχ c hc]
    have h3 : t * (nrm (u + p) - nrm u) ∈ 𝒪[F] := by
      rw [← hint, map_mul, map_sub, hnrm, hnrm]
      have : algebraMap F E t * (hf L Hm (u + p) (u + p) - hf L Hm u u)
          = algebraMap F E ((u₀ : 𝒪[F]) : F) * algebraMap F E ((ϖ : F) ^ k)
            * (hf L Hm c (u + p) + hf L Hm u c) := by
        have e1 : hf L Hm p (u + p) = algebraMap F E ((ϖ : F) ^ (i + k)) * hf L Hm c (u + p) := by
          rw [← hf_smul_left, ← hpc]
        have e2 : hf L Hm u p = algebraMap F E ((ϖ : F) ^ (i + k)) * hf L Hm u c := by
          rw [hpc, hf_smul_right, AlgEquiv.commutes]
        rw [hf_add_left, e1, hf_add_right L Hm u u p, e2, ← hτ, pow_add, map_mul]
        ring
      rw [this]
      exact L.O.mul_mem (L.O.mul_mem (hO _) (hO (ϖ ^ k)))
        (L.O.add_mem (hUU _ hc _ (UU.add_mem u.2 p.2)) (hUU _ u.2 _ hc))
    have h4 := (hψ _).2 h3 1
    have h5 : t * nrm (u + p) = t * nrm u
        + t * (nrm (u + p) - nrm u) * ((1 : 𝒪[F]) : F) := by
      push_cast; ring
    show ψ (t * nrm (u + p)) * χ (u + p) = _
    rw [h5, AddChar.map_add_eq_mul, h4, mul_one, AddChar.map_add_eq_mul, h1, mul_one]
  · intro h hh
    obtain ⟨a, ha⟩ := not_forall.1 fun h' => hh ((hQ h).2 h')
    obtain ⟨z, hz⟩ : ∃ z, z = hf L Hm h (e a) := ⟨_, rfl⟩
    rw [← hz] at ha
    have h1 : algebraMap F E t * z ∉ L.O := fun h' => ha
      ⟨algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (algebraMap F E t * z),
        L.O.mul_mem (hO _) h', by
          have h2 : algebraMap F E ((u₀ : 𝒪[F]) : F)
              * algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) = 1 := by
            rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
          linear_combination (-z) * h2
            - algebraMap F E ((u₀⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * z * hτ⟩
    obtain ⟨b, hb⟩ := not_forall.1 fun h' => h1 (hdual _ h')
    obtain ⟨hb, hb'⟩ := Classical.not_imp.1 hb
    obtain ⟨s, hs⟩ := (L.cj_fix (algebraMap F E t * z * L.cj b
      + L.cj (algebraMap F E t * z * L.cj b))).1 (by rw [map_add (f := _), L.cj_cj, add_comm])
    have hs' : s ∉ 𝒪[F] := fun h' => hb' ⟨⟨s, h'⟩, hs.symm⟩
    obtain ⟨y, hy⟩ := not_forall.1 fun h' => hs' ((hψ s).1 h')
    let v : UU := ⟨(algebraMap F E y * b) • e a, hsm _ (L.O.mul_mem (hO y) hb) _ (heU a)⟩
    refine ⟨v, ψ (s * y), hy, fun u => ?_⟩
    have h2 : t * nrm (u + v + h) - t * nrm (u + v)
        = s * y + (t * nrm (u + h) - t * nrm u) := by
      apply hinj
      have h3 : hf L Hm v h = algebraMap F E y * b * L.cj z := by
        rw [hz, cj_hf L Hm hH.1]
        exact hf_smul_left L Hm _ _ _
      have h3' : hf L Hm h v = algebraMap F E y * L.cj b * z := by
        rw [← cj_hf L Hm hH.1, h3]
        simp only [map_mul, AlgEquiv.commutes, L.cj_cj]
      simp only [map_mul, AlgEquiv.commutes, L.cj_cj] at hs
      simp only [map_sub, map_add (algebraMap F E), map_mul, hnrm, hs, hf_add_left, hf_add_right,
        h3, h3']
      ring
    have h4 : (u : Fin n → E) + v + h - (u + v) = u + h - u := by abel
    simp only [map_mul, Submodule.coe_add]
    rw [mul_mul_mul_comm, GaussSum.mul_conj_eq ψ hψ1, GaussSum.mul_conj_eq χ hχ1,
      mul_mul_mul_comm, GaussSum.mul_conj_eq ψ hψ1, GaussSum.mul_conj_eq χ hχ1, h2, h4,
      AddChar.map_add_eq_mul, mul_assoc]

end GlobalTheory.HL.GaussSummand
end

section

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.primitiveTuplesWithGramMatrix_hensel_count : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → IsNilpotent p → ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) A), (∀ a b, c (G b a) = G a b) → Set.ncard (sols c n G) * Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} = Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} := by
  first | exact @GlobalTheory.GramCount.hensel_count | exact GlobalTheory.GramCount.hensel_count | (intros; apply GlobalTheory.GramCount.hensel_count <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.meanL_tsum_ofReal_eq_ofReal_re_meanC : ∀ (G : Type) [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G) (ι : Type) [Countable ι] (f : ι → G → ℝ), (∀ i, Measurable (f i)) → (∀ i h, 0 ≤ f i h) → μ 𝓕 < ⊤ → ∫⁻ h in 𝓕, ∑' i, ‖((f i h : ℝ) : ℂ)‖ₑ ∂μ < ⊤ → meanL μ 𝓕 (fun h => ∑' i, ENNReal.ofReal (f i h)) = ENNReal.ofReal (meanC μ 𝓕 (fun h => ∑' i, ((f i h : ℝ) : ℂ))).re := by
  first | exact @GlobalTheory.meanL_eq_ofReal_meanC_re | exact GlobalTheory.meanL_eq_ofReal_meanC_re | (intros; apply GlobalTheory.meanL_eq_ofReal_meanC_re <;> assumption)
end
