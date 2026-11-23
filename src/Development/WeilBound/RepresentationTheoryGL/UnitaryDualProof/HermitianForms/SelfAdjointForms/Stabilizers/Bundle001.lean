module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.SelfAdjointForms.Stabilizers.AnnAnti
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixIntegralOfAddCharTraceDual
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle086
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle058
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle039
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix ValuativeRel

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_unif' : ∃ ϖ : k, ϖ ≠ 0 ∧ valuation k ϖ < 1 := by
  obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  refine ⟨r, ?_, hr1⟩
  first
    | exact hr0
    | exact (Valuation.ne_zero_iff _).1 hr0
    | simpa using hr0

theorem pi_lt_mem_nhds {n : ℕ} {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    Set.univ.pi (fun _ : Fin n => {y : k | valuation k y < γ}) ∈ nhds (0 : Fin n → k) :=
  set_pi_mem_nhds Set.finite_univ fun _ _ => (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem hγ

theorem ball_isLat {n : ℕ} (s : kˣ) :
    IsCompact (ball n s : Set (Fin n → k)) ∧ IsOpen (ball n s : Set (Fin n → k)) := by
  have hs : valuation k (s : k) ≠ 0 := (Valuation.ne_zero_iff _).2 s.ne_zero
  refine ⟨?_, ?_⟩
  · have e : (ball n s : Set (Fin n → k)) =
        Set.univ.pi (fun _ => {y : k | valuation k y ≤ valuation k (s : k)}) := by
      ext x
      exact Iff.intro (fun h i _ => h i) (fun h i => h i (Set.mem_univ i))
    rw [e]
    exact isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k _
  · refine (ball n s).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (pi_lt_mem_nhds hs) ?_)
    intro x hx i
    exact (hx i (Set.mem_univ i)).le

theorem exists_ball_n {n : ℕ} {A : AddSubgroup (Fin n → k)} (hA : IsCompact (A : Set (Fin n → k))) :
    ∃ s : kˣ, A ≤ ball n s := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_unif' (k := k)
  have hU : (ball n (1 : kˣ) : Set (Fin n → k)) ∈ nhds (0 : Fin n → k) := by
    refine Filter.mem_of_superset (pi_lt_mem_nhds (n := n) (γ := 1) one_ne_zero) ?_
    intro x hx i
    have h := hx i (Set.mem_univ i)
    simp only [Set.mem_ofPred_eq] at h
    simpa using h.le
  obtain ⟨l, hl⟩ := GlobalTheory.T.compact_scaled_into_nhds k n _ hA _ hU ϖ hϖ1
  have hpl : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
  have hne : valuation k (ϖ ^ l) ≠ 0 := (Valuation.ne_zero_iff _).2 hpl
  refine ⟨Units.mk0 ((ϖ ^ l)⁻¹) (inv_ne_zero hpl), fun x hx i => ?_⟩
  have h1 := hl x hx i
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Units.val_one, map_one] at h1
  simp only [Units.val_mk0]
  calc valuation k (x i) = (valuation k (ϖ ^ l))⁻¹ * (valuation k (ϖ ^ l) * valuation k (x i)) :=
        (inv_mul_cancel_left₀ hne _).symm
    _ ≤ (valuation k (ϖ ^ l))⁻¹ * 1 := by gcongr
    _ = valuation k ((ϖ ^ l)⁻¹) := by rw [mul_one, map_inv₀]

theorem ann_isLat_pf {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {n : ℕ} {A : AddSubgroup (Fin n → k)}
    (hA : IsCompact (A : Set (Fin n → k)) ∧ IsOpen (A : Set (Fin n → k))) :
    IsCompact (ann ψ A : Set (Fin n → k)) ∧ IsOpen (ann ψ A : Set (Fin n → k)) := by
  obtain ⟨s, hs⟩ := exists_ball_n hA.1
  obtain ⟨γ, hγ, hball⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hvs : valuation k (s : k) ≠ 0 := (Valuation.ne_zero_iff _).2 s.ne_zero
  have hδ : γ / valuation k (s : k) ≠ 0 := div_ne_zero hγ hvs
  refine ⟨?_, ?_⟩
  · obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_unif' (k := k)
    have hAn : (A : Set (Fin n → k)) ∈ nhds 0 := hA.2.mem_nhds A.zero_mem
    obtain ⟨l, hl⟩ := GlobalTheory.T.compact_scaled_into_nhds k n _ (ball_isLat (n := n) 1).1 _ hAn ϖ hϖ1
    have hb : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
    have hsub : (ann ψ A : Set (Fin n → k)) ⊆
        {x : Fin n → k | ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (ϖ ^ l * (t ⬝ᵥ x)) = 1} := by
      intro η hη
      show ∀ t : Fin n → k, (∀ j, t j ∈ 𝒪[k]) → ψ (ϖ ^ l * (t ⬝ᵥ η)) = 1
      intro t ht
      have htb : t ∈ ball n 1 := fun j => by
        simpa using (Valuation.mem_integer_iff _ _).mp (ht j)
      have h1 : ψ (η ⬝ᵥ (ϖ ^ l • t)) = 1 := hη _ (hl t htb)
      rw [dotProduct_smul, smul_eq_mul, dotProduct_comm] at h1
      exact h1
    have hcl : IsClosed (ann ψ A : Set (Fin n → k)) := by
      have e : (ann ψ A : Set (Fin n → k)) = ⋂ a ∈ A, {η : Fin n → k | ψ (η ⬝ᵥ a) = 1} := by
        ext η
        simp only [Set.mem_iInter]
        rfl
      rw [e]
      exact isClosed_biInter fun a _ => isClosed_eq (hψ.comp (by unfold dotProduct; fun_prop)) continuous_const
    exact (GlobalTheory.CompanionTheory.CharLattice.isCompact_isOpen_annihilator k ψ hψ hψ1 n _ hb).1.of_isClosed_subset hcl hsub
  · refine (ann ψ A).isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset (pi_lt_mem_nhds hδ) ?_)
    intro η hη a ha
    apply hball
    have hpos : 0 < valuation k (s : k) := zero_lt_iff.mpr hvs
    show valuation k (∑ j, η j * a j) < γ
    refine Valuation.map_sum_lt _ hγ fun j _ => ?_
    have h1 : valuation k (η j) * valuation k (s : k) < γ := (lt_div_iff₀ hpos).1 (hη j (Set.mem_univ j))
    rw [map_mul]
    have h2 := hs ha j
    exact lt_of_le_of_lt (by gcongr) h1

theorem exists_ball_pf {m : ℕ} {A : AddSubgroup (Fin (m + 1) → k)} (hA : IsLat A) :
    ∃ s : kˣ, A ≤ ball (m + 1) s ∧ IsLat (ball (m + 1) s) := by
  obtain ⟨s, hs⟩ := exists_ball_n hA.1
  exact ⟨s, hs, ball_isLat s⟩

theorem exists_big_pf {ψ : AddChar k Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {m : ℕ} (D : Set (Fin (m + 1) → k))
    (hD : D ∈ nhds (0 : Fin (m + 1) → k)) {A₀ : AddSubgroup (Fin (m + 1) → k)} (hA₀ : IsLat A₀) :
    ∃ A₁, IsLat A₁ ∧ A₀ ≤ A₁ ∧ (ann ψ A₁ : Set (Fin (m + 1) → k)) ⊆ D := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := exists_unif' (k := k)
  have hC := ann_isLat_pf hψ hψ1 (ball_isLat (n := m + 1) (1 : kˣ))
  obtain ⟨l, hl⟩ := GlobalTheory.T.compact_scaled_into_nhds k (m + 1) _ hC.1 D hD ϖ hϖ1
  have hb : ϖ ^ l ≠ 0 := pow_ne_zero _ hϖ0
  set u : kˣ := Units.mk0 ((ϖ ^ l)⁻¹) (inv_ne_zero hb) with hu
  obtain ⟨s₀, hs₀⟩ := exists_ball_n (n := m + 1) hA₀.1
  obtain ⟨s, h1, h2⟩ : ∃ s : kˣ, valuation k (s₀ : k) ≤ valuation k (s : k) ∧
      valuation k (u : k) ≤ valuation k (s : k) := by
    rcases le_total (valuation k (s₀ : k)) (valuation k (u : k)) with h | h
    · exact ⟨u, h, le_rfl⟩
    · exact ⟨s₀, le_rfl, h⟩
  refine ⟨ball (m + 1) s, ball_isLat s, fun x hx i => (hs₀ hx i).trans h1, ?_⟩
  intro η hη
  have hη' : (ϖ ^ l)⁻¹ • η ∈ ann ψ (ball (m + 1) 1) := by
    intro a ha
    have hmem : (ϖ ^ l)⁻¹ • a ∈ ball (m + 1) s := fun i => by
      rw [Pi.smul_apply, smul_eq_mul, map_mul]
      have ha' : valuation k (a i) ≤ 1 := by simpa using ha i
      calc valuation k (ϖ ^ l)⁻¹ * valuation k (a i) ≤ valuation k (ϖ ^ l)⁻¹ * 1 := by gcongr
        _ = valuation k (u : k) := by simp [hu]
        _ ≤ _ := h2
    have e := hη _ hmem
    rwa [dotProduct_smul, ← smul_dotProduct] at e
  have := hl _ hη'
  rwa [smul_smul, mul_inv_cancel₀ hb, one_smul] at this

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir ValuativeRel

namespace PositivityTheory.RgUd.Form.LeviSmoothness.stab

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.ColumnElementGluing PositivityTheory.RgUd.Form.LeviSmoothness

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem vmv_sq {m : ℕ} (η : Fin (m + 1) → k) :
    vecMulVec (xi0 k m) η * vecMulVec (xi0 k m) η = η (Fin.last m) • vecMulVec (xi0 k m) η := by
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply, xi0, Pi.single_apply, mul_comm, mul_left_comm]

theorem inv_pair {m : ℕ} (E : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (a c : k) (hE : E * E = a • E)
    (hc : c * (1 + a) = 1) : (1 + E) * (1 - c • E) = 1 ∧ (1 - c • E) * (1 + E) = 1 := by
  have h : E = c • E + (c * a) • E := by
    rw [← add_smul, ← mul_one_add, hc, one_smul]
  constructor
  · rw [add_mul, one_mul, mul_sub, mul_one, mul_smul_comm, hE, smul_smul]
    have h2 : E - (c * a) • E = c • E := by
      rw [sub_eq_iff_eq_add]
      exact h
    rw [sub_add_eq_add_sub, add_sub_assoc, h2, sub_self, add_zero]
  · rw [sub_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hE, smul_smul, ← h, add_sub_cancel_right]

def gU {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) : GL (Fin (m + 1)) k :=
  ⟨1 + vecMulVec (xi0 k m) η, 1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η,
    (inv_pair _ _ _ (vmv_sq η) (inv_mul_cancel₀ hη)).1, (inv_pair _ _ _ (vmv_sq η) (inv_mul_cancel₀ hη)).2⟩

theorem gU_val {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    ((gU η hη : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = 1 + vecMulVec (xi0 k m) η := rfl

theorem gU_inv_val {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    (((gU η hη)⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η := rfl

theorem gU_transpose {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    ((gU η hη : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ *ᵥ xi0 k m = xi0 k m + η := by
  funext i
  simp [gU_val, Matrix.transpose_add, Matrix.add_mulVec, Matrix.transpose_vecMulVec, Matrix.mulVec,
    dotProduct, vecMulVec_apply, xi0, Pi.single_apply]
  by_cases h : i = Fin.last m
  · subst h
    simp
  · simp [h, Matrix.one_apply_ne (Ne.symm h)]

theorem gU_det {m : ℕ} (η : Fin (m + 1) → k) (hη : 1 + η (Fin.last m) ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (gU η hη) : kˣ) : k) = 1 + η (Fin.last m) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, gU_val, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow]
  simp [xi0, dotProduct_single]

theorem val_dot_le {n : ℕ} (a x : Fin n → k) (γ : ValueGroupWithZero k) (ha : ∀ i, valuation k (a i) ≤ 1)
    (hx : ∀ i, valuation k (x i) ≤ γ) : valuation k (a ⬝ᵥ x) ≤ γ := by
  simp only [dotProduct]
  refine Valuation.map_sum_le _ (fun i _ => ?_)
  rw [Valuation.map_mul]
  calc _ ≤ 1 * γ := mul_le_mul' (ha i) (hx i)
    _ = γ := one_mul γ

theorem vmv_mulVec_apply {m : ℕ} (u v w : Fin (m + 1) → k) (i : Fin (m + 1)) :
    (vecMulVec u v *ᵥ w) i = u i * (v ⬝ᵥ w) := by
  simp [mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem mem_ball_of {m : ℕ} (c : k) (η x : Fin (m + 1) → k) (hc : valuation k c ≤ 1) (hη : ∀ i, valuation k (η i) ≤ 1)
    (s : kˣ) (hx : x ∈ ball (m + 1) s) : (1 + c • vecMulVec (xi0 k m) η) *ᵥ x ∈ ball (m + 1) s := by
  have hx' : ∀ i, valuation k (x i) ≤ valuation k (s : k) := hx
  show ∀ i, valuation k (((1 + c • vecMulVec (xi0 k m) η) *ᵥ x) i) ≤ valuation k (s : k)
  intro i
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Matrix.smul_mulVec, Pi.smul_apply,
    vmv_mulVec_apply, smul_eq_mul]
  refine Valuation.map_add_le _ (hx' i) ?_
  rw [Valuation.map_mul, Valuation.map_mul]
  have hu : valuation k (xi0 k m i) ≤ 1 := by
    unfold xi0
    rw [Pi.single_apply]
    split_ifs <;> simp
  have hd := val_dot_le η x _ hη hx'
  calc _ ≤ 1 * (1 * valuation k (s : k)) := mul_le_mul' hc (mul_le_mul' hu hd)
    _ = _ := by rw [one_mul, one_mul]

theorem good_nbhd_pf {m : ℕ} (K : Subgroup (GL (Fin (m + 1)) k)) (hK : IsOpen (K : Set (GL (Fin (m + 1)) k))) :
    ∃ D ∈ nhds (0 : Fin (m + 1) → k), ∀ η ∈ D, ∃ g ∈ K, nabs k (Matrix.GeneralLinearGroup.det g) = 1 ∧
      (∀ s : kˣ, pre g⁻¹ (ball (m + 1) s) = ball (m + 1) s) ∧
      ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵀ *ᵥ xi0 k m = xi0 k m + η := by
  have hv : {x : k | valuation k x < 1} ∈ nhds (0 : k) :=
    (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun x hx => by simpa using hx⟩
  have hS : {η : Fin (m + 1) → k | ∀ i, valuation k (η i) < 1} ∈ nhds (0 : Fin (m + 1) → k) := by
    simp only [Set.setOf_forall]
    refine Filter.iInter_mem.2 fun i => ?_
    have h1 : (fun η : Fin (m + 1) → k => η i) ⁻¹' {x : k | valuation k x < 1} ∈
        nhds (0 : Fin (m + 1) → k) :=
      ((continuous_apply i).tendsto (0 : Fin (m + 1) → k)) hv
    exact h1
  obtain ⟨U, hU, hUK⟩ := isOpen_induced_iff.1 hK
  let F : (Fin (m + 1) → k) →
      Matrix (Fin (m + 1)) (Fin (m + 1)) k × (Matrix (Fin (m + 1)) (Fin (m + 1)) k)ᵐᵒᵖ :=
    fun η => (1 + vecMulVec (xi0 k m) η,
      MulOpposite.op (1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η))
  have hF : ContinuousAt F 0 := by
    have hE : Continuous fun η : Fin (m + 1) → k => vecMulVec (xi0 k m) η :=
      Continuous.matrix_vecMulVec continuous_const continuous_id
    have h2 : ContinuousAt (fun η : Fin (m + 1) → k => (1 + η (Fin.last m))⁻¹) 0 :=
      ContinuousAt.inv₀ (continuous_const.add (continuous_apply _)).continuousAt (by simp)
    have h3 : ContinuousAt
        (fun η : Fin (m + 1) → k => 1 - (1 + η (Fin.last m))⁻¹ • vecMulVec (xi0 k m) η) 0 :=
      continuousAt_const.sub (h2.smul hE.continuousAt)
    exact ContinuousAt.prodMk (continuous_const.add hE).continuousAt
      (MulOpposite.continuous_op.continuousAt.comp h3)
  have h0 : F 0 ∈ U := by
    have h1 : (1 : GL (Fin (m + 1)) k) ∈ (K : Set (GL (Fin (m + 1)) k)) := K.one_mem
    rw [← hUK] at h1
    have e : F 0 = Units.embedProduct _ (1 : GL (Fin (m + 1)) k) :=
      Prod.ext (by simp [F]) (MulOpposite.unop_injective (by simp [F]))
    rw [e]
    exact h1
  refine ⟨F ⁻¹' U ∩ {η | ∀ i, valuation k (η i) < 1},
    Filter.inter_mem (hF.preimage_mem_nhds (hU.mem_nhds h0)) hS, ?_⟩
  rintro η ⟨hηU, hηv⟩
  have hl : valuation k (1 + η (Fin.last m)) = 1 := Valuation.map_one_add_of_lt _ (hηv _)
  have hne : 1 + η (Fin.last m) ≠ 0 := by
    intro h
    rw [h, map_zero] at hl
    exact zero_ne_one hl
  have hη1 : ∀ i, valuation k (η i) ≤ 1 := fun i => (hηv i).le
  refine ⟨(gU η hne)⁻¹, ?_, ?_, ?_, ?_⟩
  · apply K.inv_mem
    have e : Units.embedProduct _ (gU η hne) = F η :=
      Prod.ext (gU_val η hne) (MulOpposite.unop_injective (gU_inv_val η hne))
    have h1 : gU η hne ∈ Units.embedProduct _ ⁻¹' U := by
      show Units.embedProduct _ (gU η hne) ∈ U
      rw [e]
      exact hηU
    rw [hUK] at h1
    exact h1
  · rw [GlobalTheory.SplitWeil.nabs_eq_one_iff, map_inv, Units.val_inv_eq_inv_val, gU_det, map_inv₀, hl, inv_one]
  · intro s
    rw [inv_inv]
    ext x
    simp only [pre, AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, gU_val]
    constructor
    · intro hx
      have hc' : valuation k (-(1 + η (Fin.last m))⁻¹) ≤ 1 := by
        rw [Valuation.map_neg, map_inv₀, hl, inv_one]
      have hmul : (1 + (-(1 + η (Fin.last m))⁻¹) • vecMulVec (xi0 k m) η) *
          (1 + vecMulVec (xi0 k m) η) = 1 := by
        rw [neg_smul, ← sub_eq_add_neg]
        exact (inv_pair _ _ _ (vmv_sq η) (inv_mul_cancel₀ hne)).2
      have h1 := mem_ball_of _ η _ hc' hη1 s hx
      rwa [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec] at h1
    · intro hx
      have h1 := mem_ball_of 1 η x (map_one (valuation k)).le hη1 s hx
      rwa [one_smul] at h1
  · rw [inv_inv]
    exact gU_transpose η hne

end PositivityTheory.RgUd.Form.LeviSmoothness.stab
end
end
