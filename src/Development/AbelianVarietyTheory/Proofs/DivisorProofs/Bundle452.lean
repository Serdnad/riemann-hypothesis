module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem hasLoc_OAff : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R'),
    Desc.HasLoc (OAff s') := by
  intro R' _ X' s' T b
  let U := T.unop
  let b' : Γ(X', U.1) := b
  let V : X'.affineOpens := ⟨X'.basicOpen b', U.2.basicOpen b'⟩
  have hVU : V ≤ U := X'.basicOpen_le b'
  let l : T ⟶ Opposite.op V := (homOfLE hVU).op
  haveI := U.2.isLocalization_basicOpen b'
  refine ⟨Opposite.op V, l, ?_, ?_, ?_, ?_⟩
  · exact IsLocalization.Away.algebraMap_isUnit (S := Γ(X', X'.basicOpen b')) b'
  · intro y
    let y' : Γ(X', X'.basicOpen b') := y
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers b') y'
    refine ⟨n, x, ?_⟩
    show y' * (algebraMap Γ(X', U.1) Γ(X', X'.basicOpen b') b') ^ n =
      algebraMap Γ(X', U.1) Γ(X', X'.basicOpen b') x
    rw [← map_pow]
    exact e
  · intro x hx
    let x' : Γ(X', U.1) := x
    have hx : algebraMap Γ(X', U.1) Γ(X', X'.basicOpen b') x' = 0 := hx
    obtain ⟨⟨_, n, rfl⟩, e⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers b') _ x').1 hx
    exact ⟨n, e⟩
  · intro S u hu
    have hSU : S.unop.1 ≤ U.1 := leOfHom u.unop
    have hu' : IsUnit ((X'.presheaf.map (homOfLE hSU).op).hom b') := hu
    have h1 := X'.basicOpen_res b' (homOfLE hSU).op
    rw [Scheme.basicOpen_of_isUnit _ hu'] at h1
    have hSV : S.unop ≤ V := by
      change S.unop.1 ≤ X'.basicOpen b'
      rw [h1]; exact inf_le_right
    refine ⟨(homOfLE hSV).op, Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩

end GlobalTheory.CechDR
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj

namespace GlobalTheory.FunObj.DiagLattice

theorem exists_KO_of_det {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι k)
    (h1 : ∀ i j, M i j ∈ 𝒪[k]) (h2 : valuation k M.det = 1) : ∃ g ∈ KO k ι, g.val = M := by
  let A : Matrix ι ι 𝒪[k] := fun i j => ⟨M i j, h1 i j⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = M := rfl
  have hd : algebraMap 𝒪[k] k A.det = M.det := by rw [RingHom.map_det, hA]
  have hu : IsUnit A.det :=
    (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (valuation k))).2 (by rw [hd, h2])
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det A).2 hu
  refine ⟨Matrix.GeneralLinearGroup.map (n := ι) (algebraMap 𝒪[k] k) u, ⟨u, rfl⟩, ?_⟩
  change u.val.map (algebraMap 𝒪[k] k) = _
  rw [hu]; rfl

theorem exists_unip {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (p : ℕ)
    (v : Fin c → n ⊕ Fin c → k) (h1 : ∀ i, v i (Sum.inr i) = 1) (h2 : ∀ i l, i < l → v i (Sum.inr l) = 0)
    (h3 : ∀ i : Fin c, i.val < p → ∀ r, v i (Sum.inl r) = 0) :
    ∃ u ∈ N k n c p, (∀ r i, u.val r (Sum.inr i) = v i r) ∧
      ∀ r s, u.val r (Sum.inl s) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inl s) := by
  refine ⟨(Model.mkNel p fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2).1,
    Subtype.property _, ?_, ?_⟩
  · intro r i
    show Model.mkN p (fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2) r (Sum.inr i) = _
    simp only [Model.mkN, of_apply, Sum.elim_inr]
    split_ifs with h
    · rfl
    · rcases r with r | r
      · rw [h3 i (by simp [lev] at h; omega)]; simp
      · simp only [lev, Sum.elim_inr] at h
        rcases eq_or_lt_of_le (show i ≤ r by rw [Fin.le_def]; omega) with e | e
        · subst e; simp [h1]
        · rw [h2 i r e, Matrix.one_apply_ne]
          simpa using e.ne'
  · intro r s
    show Model.mkN p (fun rs => Sum.elim (fun _ => (0 : k)) (fun i => v i rs.1.1) rs.1.2) r (Sum.inl s) = _
    simp only [Model.mkN, of_apply, Sum.elim_inl]
    split_ifs with h
    · rw [Matrix.one_apply_ne]
      rintro rfl; exact lt_irrefl _ h
    · rfl

theorem exists_symR_diag : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (d : Fin c → kˣ) (H : GL (n ⊕ Fin c) k),
  (∀ i : Fin c, ∃ v : n ⊕ Fin c → k, v (Sum.inr i) = 1 ∧ (∀ l : Fin c, i < l → v (Sum.inr l) = 0) ∧ (i.val < (c + 1) / 2 → ∀ r, v (Sum.inl r) = 0) ∧ ∀ t, ((H⁻¹).val *ᵥ ((d i : k) • v)) t ∈ 𝒪[k]) →
  (∀ (i : Fin c) (y : n ⊕ Fin c → k), (∀ t, y t ∈ 𝒪[k]) → (∀ l : Fin c, i < l → (H.val *ᵥ y) (Sum.inr l) = 0) → (i.val < c / 2 → ∀ r, (H.val *ᵥ y) (Sum.inl r) = 0) → valuation k ((H.val *ᵥ y) (Sum.inr i)) ≤ valuation k (d i : k)) →
  ∃ r ∈ symR k n c, ∃ w ∈ KO k (n ⊕ Fin c), H = r * diagGL (Sum.elim (fun _ => 1) d) * w := by
  intro k _ _ _ _ n _ _ c d H hA hB
  choose v v1 v2 v3 v4 using hA
  obtain ⟨u, hu, uc, uX⟩ := exists_unip ((c + 1) / 2) v v1 v2 v3
  let lv : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * (c / 2)) (fun i => 2 * i.val + 1)
  obtain ⟨b, hb, w, hw, hbw⟩ := iwasawa_blockTriangular k (n ⊕ Fin c) lv (u⁻¹ * H)
  have hbi : (b⁻¹).val.BlockTriangular lv := by
    rw [Matrix.coe_units_inv]
    haveI := b.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hH : H = u * b * w := by rw [mul_assoc, ← hbw]; simp
  obtain ⟨w1, w2⟩ := (mem_KO_iff w).1 hw
  have hdiag : ∀ i, (b⁻¹).val (Sum.inr i) (Sum.inr i) * b.val (Sum.inr i) (Sum.inr i) = 1 := by
    intro i
    have h := congrFun (congrFun b.inv_mul (Sum.inr i)) (Sum.inr i)
    rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr i)] at h
    · simpa using h
    · intro t _ ht
      rcases lt_trichotomy (lv t) (lv (Sum.inr i)) with e | e | e
      · rw [hbi e, zero_mul]
      · exfalso
        rcases t with t | t
        · simp only [lv, Sum.elim_inl, Sum.elim_inr] at e; omega
        · simp only [lv, Sum.elim_inr] at e; exact ht (congrArg _ (Fin.ext (by omega)))
      · rw [hb e, mul_zero]
    · simp
  have hbl : ∀ i l : Fin c, i < l → b.val (Sum.inr l) (Sum.inr i) = 0 := fun i l h =>
    hb (by simp only [lv, Sum.elim_inr]; rw [Fin.lt_def] at h; omega)
  have h3 : ∀ i, valuation k (b.val (Sum.inr i) (Sum.inr i)) ≤ valuation k (d i : k) := by
    intro i
    have key : ∀ t, (H.val *ᵥ fun s => (w⁻¹).val s (Sum.inr i)) t =
        ∑ s, u.val t (Sum.inl s) * b.val (Sum.inl s) (Sum.inr i) + ∑ l, v l t * b.val (Sum.inr l) (Sum.inr i) := by
      intro t
      have : (H * w⁻¹).val t (Sum.inr i) = (u * b).val t (Sum.inr i) := by rw [hH]; simp
      rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type
        (fun j => u.val t j * b.val j (Sum.inr i))] at this
      simp only [uc] at this
      exact this
    have h := hB i (fun s => (w⁻¹).val s (Sum.inr i)) (fun t => w2 _ _) ?_ ?_
    · rw [key, Finset.sum_eq_single i] at h
      · simpa [uX, v1] using h
      · intro l _ hl
        rcases lt_or_gt_of_ne hl with e | e
        · rw [v2 l i e, zero_mul]
        · rw [hbl i l e, mul_zero]
      · simp
    · intro l hl
      rw [key, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
      · intro m _
        rcases lt_or_ge m l with e | e
        · rw [v2 m l e, zero_mul]
        · rw [hbl i m (hl.trans_le e), mul_zero]
      · intro s _; simp [uX]
    · intro hi r
      rw [key, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
      · intro m _
        rcases lt_or_ge i m with e | e
        · rw [hbl i m e, mul_zero]
        · rw [v3 m (by rw [Fin.le_def] at e; omega), zero_mul]
      · intro s _
        rw [hb (show lv (Sum.inr i) < lv (Sum.inl s) by simp only [lv, Sum.elim_inr, Sum.elim_inl]; omega), mul_zero]
  have h4 : ∀ t i, (b⁻¹).val t (Sum.inr i) * (d i : k) ∈ 𝒪[k] := by
    intro t i
    have e : b⁻¹ = w * H⁻¹ * u := by rw [hH]; group
    have : (b⁻¹).val t (Sum.inr i) * (d i : k) = (w.val *ᵥ ((H⁻¹).val *ᵥ ((d i : k) • v i))) t := by
      rw [Matrix.mulVec_mulVec, e, Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_mul]
      simp only [Matrix.mulVec, dotProduct, uc, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    exact sum_mem fun j _ => mul_mem (w1 _ _) (v4 i j)
  let A : Matrix (Fin c) (Fin c) k := Matrix.of fun l i => (b⁻¹).val (Sum.inr l) (Sum.inr i) * d i
  let β : Matrix n (Fin c) k := Matrix.of fun r i => (b⁻¹).val (Sum.inl r) (Sum.inr i) * d i
  have hAtri : A.BlockTriangular id := fun l i h => by
    simp only [A, of_apply]
    rw [hbi (by simp only [lv, Sum.elim_inr]; rw [id, id, Fin.lt_def] at h; omega), zero_mul]
  obtain ⟨κ, hκ, hκv⟩ := exists_KO_of_det (fromBlocks 1 β 0 A) (by
    rintro (r | r) (s | s)
    · simp only [fromBlocks_apply₁₁, Matrix.one_apply]; split_ifs <;> simp
    · exact h4 _ _
    · exact zero_mem _
    · exact h4 _ _) (by
    rw [det_fromBlocks_zero₂₁, det_one, one_mul, det_of_upperTriangular hAtri, map_prod]
    refine Finset.prod_eq_one fun i _ => le_antisymm (h4 (Sum.inr i) i) ?_
    simp only [A, of_apply, map_mul]
    calc (1 : ValueGroupWithZero k) = valuation k ((b⁻¹).val (Sum.inr i) (Sum.inr i)) *
          valuation k (b.val (Sum.inr i) (Sum.inr i)) := by rw [← map_mul, hdiag, map_one]
      _ ≤ _ := mul_le_mul_right (h3 i) _)
  have hB : (b * κ).val = fromBlocks b.val.toBlocks₁₁ 0 b.val.toBlocks₂₁ (diagonal fun i => (d i : k)) := by
    have col : ∀ t i, (b * κ).val t (Sum.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) t (Sum.inr i) * d i := by
      intro t i
      rw [← b.mul_inv, Units.val_mul, hκv, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      rintro (j | j) _ <;> simp [A, β, mul_assoc]
    ext (r | r) (s | s)
    · simp [hκv, Matrix.mul_apply, Matrix.one_apply, toBlocks₁₁]
    · rw [col]; simp
    · simp [hκv, Matrix.mul_apply, Matrix.one_apply, toBlocks₂₁]
    · rw [col]
      by_cases h : r = s
      · subst h; simp
      · simp [h]
  have hg : b.val.toBlocks₁₁.det ≠ 0 := by
    have := Matrix.GeneralLinearGroup.det_ne_zero (b * κ)
    rw [hB, det_fromBlocks_zero₁₂] at this
    exact left_ne_zero_of_mul this
  let g : GL n k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hg
  have hlow : lowU b.val.toBlocks₂₁ ∈ N k n c (c / 2 + 1) := by
    rw [Model.mem_N_iff]
    rintro (r | r) (s | s) h
    · simp [lowU, Matrix.one_apply]
    · simp [lowU]
    · simp only [lev, Sum.elim_inl, Sum.elim_inr] at h
      simp only [lowU, fromBlocks_apply₂₁, toBlocks₂₁, of_apply]
      rw [hb (show lv (Sum.inl s) < lv (Sum.inr r) by simp only [lv, Sum.elim_inr, Sum.elim_inl]; omega)]
      simp
    · simp [lowU, Matrix.one_apply]
  have hfac : b * κ = embX c g * lowU b.val.toBlocks₂₁ * diagGL (Sum.elim (fun _ => 1) d) := by
    refine Units.ext ?_
    have hD : (diagGL (Sum.elim (fun _ : n => (1 : kˣ)) d)).val = fromBlocks 1 0 0 (diagonal fun i => (d i : k)) := by
      rw [diagGL_val, ← diagonal_one, fromBlocks_diagonal]
      congr 1
      funext x; rcases x with x | x <;> simp
    rw [hB, Units.val_mul, Units.val_mul, hD]
    show _ = fromBlocks b.val.toBlocks₁₁ 0 0 1 * fromBlocks 1 0 b.val.toBlocks₂₁ 1 * _
    simp [fromBlocks_multiply]
  refine ⟨u * (embX c g * lowU b.val.toBlocks₂₁), ?_, κ⁻¹ * w, mul_mem (inv_mem hκ) hw, ?_⟩
  · exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_left hu))
      (mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right (Subgroup.mem_sup_right hlow)))
  · rw [mul_assoc u, ← hfac, hH]; group

end GlobalTheory.FunObj.DiagLattice
end

section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.FunObj
open Matrix

section Ratio
variable {G : Type*} [Group G]

def idxRatio (A B : Subgroup G) : ℚ := (B.relIndex A : ℚ) / A.relIndex B

theorem idxRatio_eq_of_le {A B D : Subgroup G} (hD : D ≤ A ⊓ B) (h0 : D.relIndex (A ⊓ B) ≠ 0) :
    idxRatio A B = (D.relIndex A : ℚ) / D.relIndex B := by
  have h1 := Subgroup.relIndex_mul_relIndex D (A ⊓ B) A hD inf_le_left
  have h2 := Subgroup.relIndex_mul_relIndex D (A ⊓ B) B hD inf_le_right
  have e1 : (A ⊓ B).relIndex A = B.relIndex A := by rw [inf_comm]; exact Subgroup.inf_relIndex_right B A
  have e2 : (A ⊓ B).relIndex B = A.relIndex B := Subgroup.inf_relIndex_right A B
  rw [idxRatio, ← h1, ← h2, e1, e2]
  push_cast
  rw [mul_div_mul_left _ _ (by exact_mod_cast h0)]

theorem idxRatio_map {f : G →* G} (hf : Function.Injective f) (A B : Subgroup G) :
    idxRatio (A.map f) (B.map f) = idxRatio A B := by
  rw [idxRatio, idxRatio, Subgroup.relIndex_map_map_of_injective _ _ hf,
    Subgroup.relIndex_map_map_of_injective _ _ hf]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem relIndex_inf_ne_zero {N O C H : Subgroup G} (hO : IsOpen (O : Set G)) (hC : IsCompact (C : Set G))
    (hHN : H ≤ N) (hHC : H ≤ C) : (N ⊓ O).relIndex H ≠ 0 := by
  intro h
  have h1 : O ⊓ H ≤ N ⊓ O := fun x hx => Subgroup.mem_inf.2 ⟨hHN (Subgroup.mem_inf.1 hx).2, (Subgroup.mem_inf.1 hx).1⟩
  have h2 := Subgroup.relIndex_eq_zero_of_le_left h1 h
  rw [Subgroup.inf_relIndex_right] at h2
  exact relIndex_ne_zero_of_isOpen hO hC hHC h2

theorem idxRatio_cocycle (N : Subgroup G) {U V W : Subgroup G} (hUo : IsOpen (U : Set G))
    (hUc : IsCompact (U : Set G)) (hVo : IsOpen (V : Set G)) (hVc : IsCompact (V : Set G))
    (hWo : IsOpen (W : Set G)) (hWc : IsCompact (W : Set G)) :
    idxRatio (N ⊓ U) (N ⊓ V) * idxRatio (N ⊓ V) (N ⊓ W) = idxRatio (N ⊓ U) (N ⊓ W) := by
  have hO : IsOpen ((U ⊓ V ⊓ W : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf, Subgroup.coe_inf]; exact (hUo.inter hVo).inter hWo
  have l1 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ U) ⊓ (N ⊓ V) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have l2 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ V) ⊓ (N ⊓ W) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have l3 : N ⊓ (U ⊓ V ⊓ W) ≤ (N ⊓ U) ⊓ (N ⊓ W) := by
    intro x hx; simp only [Subgroup.mem_inf] at hx ⊢; tauto
  have nV : (N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ V) ≠ 0 := relIndex_inf_ne_zero hO hVc inf_le_left inf_le_right
  have nW : (N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ W) ≠ 0 := relIndex_inf_ne_zero hO hWc inf_le_left inf_le_right
  rw [idxRatio_eq_of_le l1 (relIndex_inf_ne_zero hO hUc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)),
    idxRatio_eq_of_le l2 (relIndex_inf_ne_zero hO hVc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right)),
    idxRatio_eq_of_le l3 (relIndex_inf_ne_zero hO hUc (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right))]
  have nV' : ((N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ V) : ℚ) ≠ 0 := by exact_mod_cast nV
  have nW' : ((N ⊓ (U ⊓ V ⊓ W)).relIndex (N ⊓ W) : ℚ) ≠ 0 := by exact_mod_cast nW
  field_simp

end Ratio

section Diag
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem diagGL_mul' (d e : n → kˣ) : diagGL (d * e) = diagGL d * diagGL e :=
  Units.ext (by simp [diagonal_mul_diagonal])

theorem diagGL_inv' (d : n → kˣ) : diagGL d⁻¹ = (diagGL d)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← diagGL_mul']; exact Units.ext (by simp))

theorem conj_diagGL_InN {p : ℕ} (d : n ⊕ Fin c → kˣ) {x : GL (n ⊕ Fin c) k} (hx : InN p x) :
    InN p (MulAut.conj (diagGL d) x) := by
  intro r s hrs
  have h := hx r s hrs
  have hinv : ((diagGL d)⁻¹ : GL (n ⊕ Fin c) k).val = diagonal fun i => (((d i)⁻¹ : kˣ) : k) := rfl
  rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, hinv, diagGL_val, mul_diagonal, diagonal_mul, h]
  by_cases hrs' : r = s
  · subst hrs'; simp
  · simp [hrs']

theorem map_conj_diagGL_N_le (p : ℕ) (d : n ⊕ Fin c → kˣ) :
    (N k n c p).map (MulAut.conj (diagGL d)).toMonoidHom ≤ N k n c p := by
  rw [N, MonoidHom.map_closure]
  exact (Subgroup.closure_le _).2 (by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.subset_closure (conj_diagGL_InN d hx))

theorem map_conj_diagGL_symN (d : n ⊕ Fin c → kˣ) :
    (symN k n c).map (MulAut.conj (diagGL d)).toMonoidHom = symN k n c := by
  have hle : ∀ d : n ⊕ Fin c → kˣ, (symN k n c).map (MulAut.conj (diagGL d)).toMonoidHom ≤ symN k n c := by
    intro d
    rw [symN, Subgroup.map_sup]
    exact sup_le_sup (map_conj_diagGL_N_le _ d) (map_conj_diagGL_N_le _ d)
  refine le_antisymm (hle d) ?_
  have h := Subgroup.map_mono (f := (MulAut.conj (diagGL d)).toMonoidHom) (hle d⁻¹)
  have e : (MulAut.conj (diagGL d)).toMonoidHom.comp (MulAut.conj (diagGL d⁻¹)).toMonoidHom = MonoidHom.id _ := by
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply, diagGL_inv']
    group
  rwa [Subgroup.map_map, e, Subgroup.map_id] at h

end Diag

end GlobalTheory.FunObj

namespace GlobalTheory.FunObj
open Matrix

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem relIndex_congr_inf {G : Type*} [Group G] {A B L : Subgroup G} (h : A ⊓ L = B ⊓ L) :
    A.relIndex L = B.relIndex L := by
  rw [← Subgroup.inf_relIndex_right A L, h, Subgroup.inf_relIndex_right]


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem invVol_eq_idxRatio (C : Subgroup (GL (n ⊕ Fin c) k)) :
    invVol C = idxRatio (symN k n c ⊓ KO k _) (symN k n c ⊓ C) := by
  rw [invVol, idxRatio, relIndex_congr_inf (A := C) (B := symN k n c ⊓ C),
    relIndex_congr_inf (A := KO k _) (B := symN k n c ⊓ KO k _)]
  · ext x; simp only [Subgroup.mem_inf]; tauto
  · ext x; simp only [Subgroup.mem_inf]; tauto

theorem isOpen_map_conj_KO (x : GL (n ⊕ Fin c) k) :
    IsOpen (((KO k (n ⊕ Fin c)).map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (GL (n ⊕ Fin c) k)) := by
  rw [Subgroup.map_equiv_eq_comap_symm']
  exact isOpen_KO.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem isCompact_map_conj_KO (x : GL (n ⊕ Fin c) k) :
    IsCompact (((KO k (n ⊕ Fin c)).map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (GL (n ⊕ Fin c) k)) :=
  isCompact_KO.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem invVol_conj_diagGL_mul (d e : n ⊕ Fin c → kˣ) :
    invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom) =
      invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL d)).toMonoidHom) *
        invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom) := by
  have hmapN : ∀ (d : n ⊕ Fin c → kˣ) (K' : Subgroup (GL (n ⊕ Fin c) k)),
      (symN k n c ⊓ K').map (MulAut.conj (diagGL d)).toMonoidHom =
        symN k n c ⊓ K'.map (MulAut.conj (diagGL d)).toMonoidHom := by
    intro d K'
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (diagGL d)).injective, map_conj_diagGL_symN]
  have hcomp : (KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (d * e))).toMonoidHom =
      ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom).map
        (MulAut.conj (diagGL d)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext1 x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, diagGL_mul']
    group
  rw [invVol_eq_idxRatio, invVol_eq_idxRatio, invVol_eq_idxRatio, hcomp,
    ← idxRatio_cocycle (symN k n c) isOpen_KO isCompact_KO (isOpen_map_conj_KO (diagGL d))
      (isCompact_map_conj_KO (diagGL d)) (hcomp ▸ isOpen_map_conj_KO (diagGL (d * e)))
      (hcomp ▸ isCompact_map_conj_KO (diagGL (d * e)))]
  congr 1
  rw [← hmapN d (KO k _), ← hmapN d ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL e)).toMonoidHom),
    idxRatio_map (MulAut.conj (diagGL d)).injective]

end Main

end GlobalTheory.FunObj
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem coboundaryOne_additiveFormalGroupLaw_X_pow (R : Type) [CommRing R] (d N : ℕ) (m : Fin d) (hN : 1 ≤ N) :
    cob1 (addLaw R d) (X m ^ N) = ∑ i ∈ Finset.Ioo 0 N,
      monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i))
        (N.choose i : R) := by
  have h1 : HasSubst (addLaw R d) := hasSubst_of_constantCoeff_zero fun i => by simp [addLaw]
  have h2 : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have h3 : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  unfold cob1 inL inR
  rw [subst_pow h1, subst_pow h2, subst_pow h3, subst_X h1, subst_X h2, subst_X h3]
  simp only [addLaw]
  have hr : Finset.range (N + 1) = insert 0 (insert N (Finset.Ioo 0 N)) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [add_pow, hr, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]
  simp only [pow_zero, Nat.sub_zero, Nat.sub_self, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, mul_one, one_mul]
  have key : ∀ i ∈ Finset.Ioo 0 N,
      (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R) ^ i * X (Sum.inr m) ^ (N - i) *
        (N.choose i : MvPowerSeries (Fin d ⊕ Fin d) R) =
      monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i))
        (N.choose i : R) := by
    intro i _
    rw [X_pow_eq, X_pow_eq, monomial_mul_monomial, one_mul, ← nsmul_eq_mul', ← map_nsmul,
      nsmul_one]
  rw [Finset.sum_congr rfl key]
  abel

end GlobalTheory
end
