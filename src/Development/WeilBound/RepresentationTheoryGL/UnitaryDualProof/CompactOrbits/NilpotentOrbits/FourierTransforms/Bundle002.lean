module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.EInjective
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.Bundle001
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem supp_congr {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ}
    (h : Supp ξ (Bz Z ×ˢ Set.univ)) {f g : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n)))
    (hg : g ∈ supportedIn (Set.univ : Set (Sp k n))) (e : ∀ p ∈ Bz Z ×ˢ Set.univ, f p = g p) : ξ f = ξ g := by
  have := h (f - g) ((supportedIn Set.univ).sub_mem hf hg) fun p hp => by simp [e p hp]
  rwa [map_sub, sub_eq_zero] at this

theorem fourP_of (hΦ : PhiP (k := k)) (hC : CompP (k := k)) : FourP (k := k) := by
  intro n Z hZ
  obtain ⟨Φ, Φ', h1, h2, h3, h4, h5, h6, h7, h8⟩ := hΦ n Z hZ
  obtain ⟨hCs, hCa, -, -⟩ := hC n Z hZ
  have hUU : ∀ f ∈ supportedIn (UU : Set (Sp k n)), f ∈ supportedIn (Set.univ : Set (Sp k n)) :=
    fun f hf => ⟨hf.1, Set.subset_univ _⟩
  let F : ((Sp k n → ℂ) →ₗ[ℂ] ℂ) →ₗ[ℂ] (Sp k n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ξ => ξ ∘ₗ Φ
      map_add' := fun a b => by ext; simp
      map_smul' := fun a b => by ext; simp }
  have hF : ∀ ξ f, F ξ f = ξ (Φ f) := fun _ _ => rfl
  refine ⟨F, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ hξ f hf hz
    rw [hF]
    refine hξ _ (h1 f hf) fun p hp => ?_
    have hpF : p ∈ Fib Z (qZ Z p.1) := ⟨⟨hp.1, rfl⟩, Set.mem_univ _⟩
    exact h3 f hf (qZ Z p.1) (fun q hq => hz q ⟨hq.1.1, Set.mem_univ _⟩) p hpF
  · intro ξ y hξ f hf hz
    rw [hF]
    exact hξ _ (h1 f hf) (h3 f hf y hz)
  · intro ξ hξ hinv g hg f hf
    rw [hF, hF]
    have hfg : (fun q => f (act g q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := hCa g f hf
    rw [supp_congr hξ (h1 _ hfg) (hCa g _ (h1 f hf)) (fun p hp => h4 g hg f hf p hp)]
    exact hinv g hg _ (h1 f hf)
  · intro ξ hξ
    constructor
    · intro hk f hf
      rw [hF]
      exact hk _ (h5 f hf)
    · intro hk f hf
      have hfu := hUU f hf
      rw [← supp_congr hξ (h1 _ (h2 f hfu)) hfu (fun p hp => h7 f hfu p hp)]
      exact hk _ (h6 f hf)
  · intro ξ hξ f hf
    rw [hF]
    exact hξ _ (h1 f hf)
  · intro t ξ hξ f hf
    rw [hF]
    show ξ (fun q => Φ f (sig Z t q)) = _ * ξ (Φ (fun q => f (sig Z t⁻¹ q)))
    have hsf : (fun q => f (sig Z t⁻¹ q)) ∈ supportedIn (Set.univ : Set (Sp k n)) := hCs t⁻¹ f hf
    rw [← smul_eq_mul, ← map_smul]
    exact supp_congr hξ (hCs t _ (h1 f hf)) (Submodule.smul_mem _ _ (h1 _ hsf))
      (fun p hp => by rw [Pi.smul_apply, smul_eq_mul]; exact h8 t f hf p hp)

end PositivityTheory.RgUd.T.Nil.Four
end
end

section

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  (Z : Subalgebra k (Matrix (Fin n) (Fin n) k))

def Dl : Matrix (Fin n) (Fin n) k →ₗ[k] (Fin (d Z) → k) where
  toFun := D Z
  map_add' := D_add Z
  map_smul' := D_smul Z

abbrev TT : Type := ↥(LinearMap.ker (Dl Z)) × (Fin n → k)

theorem continuous_E : Continuous (E Z) := by
  have e : E Z = fun u => ∑ j, u j • ee Z j := funext (E_apply Z)
  rw [e]
  fun_prop

theorem continuous_D : Continuous (D Z) :=
  continuous_pi fun j => (continuous_const.matrix_mul continuous_id).matrix_trace

theorem continuous_Pr : Continuous (Pr Z) :=
  (continuous_E Z).comp (continuous_const.matrix_mulVec (continuous_D Z))

variable {Z}
variable (hZ : CR Z) (h : Hyp Z)

def Hb : Sp k n ≃ₜ TT Z × (Fin (d Z) → k) where
  toFun p := ((⟨p.1 - Pr Z p.1, by show D Z _ = 0; exact D_sub_Pr hZ h _⟩, p.2), D Z p.1)
  invFun q := (q.1.1.1 + E Z ((G Z)⁻¹ *ᵥ q.2), q.1.2)
  left_inv p := by
    ext1
    · show p.1 - Pr Z p.1 + E Z ((G Z)⁻¹ *ᵥ D Z p.1) = p.1
      rw [← Pr, sub_add_cancel]
    · rfl
  right_inv q := by
    obtain ⟨⟨⟨y, hy⟩, v⟩, w⟩ := q
    have hy' : D Z y = 0 := hy
    have hPy : Pr Z (y + E Z ((G Z)⁻¹ *ᵥ w)) = E Z ((G Z)⁻¹ *ᵥ w) := by
      rw [Pr_add, Pr_of_D hZ h hy', Pr_E hZ h, zero_add]
    have hDx : D Z (y + E Z ((G Z)⁻¹ *ᵥ w)) = w := by
      rw [D_add, hy', zero_add, D_E, mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det hZ h)), one_mulVec]
    refine Prod.ext (Prod.ext (Subtype.ext ?_) rfl) hDx
    show y + E Z ((G Z)⁻¹ *ᵥ w) - Pr Z (y + E Z ((G Z)⁻¹ *ᵥ w)) = y
    rw [hPy, add_sub_cancel_right]
  continuous_toFun := by
    refine Continuous.prodMk (Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_snd)
      ((continuous_D Z).comp continuous_fst)
    exact continuous_fst.sub ((continuous_Pr Z).comp continuous_fst)
  continuous_invFun := by
    refine Continuous.prodMk ?_ (continuous_snd.comp continuous_fst)
    exact (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).add
      ((continuous_E Z).comp (continuous_const.matrix_mulVec continuous_snd))

def Gm : (Fin (d Z) → k) ≃ₜ (Fin (d Z) → k) where
  toFun u := G Z *ᵥ u
  invFun u := (G Z)⁻¹ *ᵥ u
  left_inv u := by
    show (G Z)⁻¹ *ᵥ (G Z *ᵥ u) = u
    rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det hZ h)), one_mulVec]
  right_inv u := by
    show G Z *ᵥ ((G Z)⁻¹ *ᵥ u) = u
    rw [mulVec_mulVec, mul_nonsing_inv _ (Ne.isUnit (G_det hZ h)), one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def F1 : TT Z × (Fin (d Z) → k) ≃ₜ Sp k n := ((Homeomorph.refl (TT Z)).prodCongr (Gm hZ h)).trans (Hb hZ h).symm

theorem real_test_function_apply (q : TT Z × (Fin (d Z) → k)) : F1 hZ h q = (q.1.1.1 + E Z q.2, q.1.2) := by
  show (q.1.1.1 + E Z ((G Z)⁻¹ *ᵥ (G Z *ᵥ q.2)), q.1.2) = _
  rw [mulVec_mulVec, nonsing_inv_mul _ (Ne.isUnit (G_det hZ h)), one_mulVec]

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end
end

section

noncomputable section

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Phi2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem inv_mem_Gz {g : GL (Fin n) k} (hg : g ∈ Gz Z) : g⁻¹ ∈ Gz Z := by
  intro a ha
  have hga := hg a ha
  have h1 : (g⁻¹ : GL (Fin n) k).val * g.val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : g.val * (g⁻¹ : GL (Fin n) k).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc a * (g⁻¹ : GL (Fin n) k).val
      = (g⁻¹ : GL (Fin n) k).val * (g.val * a) * (g⁻¹ : GL (Fin n) k).val := by
        rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    _ = (g⁻¹ : GL (Fin n) k).val * (a * g.val) * (g⁻¹ : GL (Fin n) k).val := by rw [hga]
    _ = (g⁻¹ : GL (Fin n) k).val * a := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem conj_mem_Bz {g : GL (Fin n) k} (hg : g ∈ Gz Z) {w : Matrix (Fin n) (Fin n) k} (hw : w ∈ Bz Z) :
    g.val * w * g⁻¹.val ∈ Bz Z := by
  intro a ha
  have h1 := hg a ha
  have h2 := inv_mem_Gz hg a ha
  have h3 := hw a ha
  calc a * (g.val * w * g⁻¹.val) = a * g.val * w * g⁻¹.val := by simp only [Matrix.mul_assoc]
    _ = g.val * (a * w) * g⁻¹.val := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = g.val * w * (a * g⁻¹.val) := by rw [h3]; simp only [Matrix.mul_assoc]
    _ = g.val * w * g⁻¹.val * a := by rw [h2]; simp only [Matrix.mul_assoc]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem conj_mem_nilpotent_cone {g : GL (Fin n) k} (hg : g ∈ Gz Z) {w : Matrix (Fin n) (Fin n) k} (hw : w ∈ B0 Z) :
    g.val * w * g⁻¹.val ∈ B0 Z := by
  unfold B0 at hw ⊢
  rw [Submodule.mem_inf] at hw ⊢
  obtain ⟨hw1, hw2⟩ := hw
  refine ⟨conj_mem_Bz hg hw1, ?_⟩
  rw [LinearMap.mem_ker] at hw2 ⊢
  have hq : qZ Z w = 0 := hw2
  show qZ Z (g.val * w * g⁻¹.val) = 0
  rw [qZ_conj Z hg w]
  exact hq

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem tr_conj (A P g g' : Matrix (Fin n) (Fin n) k) : trace (A * (g * P * g')) = trace (g' * A * g * P) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

variable (hZ : CR Z) (h : Hyp Z)
include hZ h

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Pr_unique {w y : Matrix (Fin n) (Fin n) k} (hw : w ∈ B0 Z) (hD : D Z w = D Z y) : w = Pr Z y := by
  obtain ⟨u, rfl⟩ := exists_E Z hw
  have hP : Pr Z y = E Z ((G Z)⁻¹ *ᵥ D Z y) := rfl
  rw [hP]
  congr 1
  have h1 : D Z (Pr Z y) = D Z y := D_Pr hZ h y
  rw [hP, D_E] at h1
  rw [D_E] at hD
  have hz : G Z *ᵥ (u - (G Z)⁻¹ *ᵥ D Z y) = 0 := by
    rw [Matrix.mulVec_sub, hD, h1, sub_self]
  exact sub_eq_zero.mp (G_inj hZ h hz)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem trace_nilpotent_cone_projection {w : Matrix (Fin n) (Fin n) k} (hw : w ∈ B0 Z) (x : Matrix (Fin n) (Fin n) k) :
    trace (w * x) = trace (w * Pr Z x) := by
  obtain ⟨u, rfl⟩ := exists_E Z hw
  have h0 := D_sub_Pr hZ h x
  have hz : trace (E Z u * (x - Pr Z x)) = 0 := by
    rw [E_apply, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul]
    have hj : D Z (x - Pr Z x) j = 0 := by rw [h0]; rfl
    have hj' : trace (ee Z j * (x - Pr Z x)) = 0 := hj
    rw [hj', smul_zero]
  rw [Matrix.mul_sub, Matrix.trace_sub, sub_eq_zero] at hz
  exact hz

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem Pr_conj {g : GL (Fin n) k} (hg : g ∈ Gz Z) (x : Matrix (Fin n) (Fin n) k) :
    Pr Z (g.val * x * g⁻¹.val) = g.val * Pr Z x * g⁻¹.val := by
  have hPx : Pr Z x ∈ B0 Z := E_mem Z _
  refine (Pr_unique hZ h (conj_mem_nilpotent_cone hg hPx) ?_).symm
  funext j
  show trace (ee Z j * (g.val * Pr Z x * g⁻¹.val)) = trace (ee Z j * (g.val * x * g⁻¹.val))
  rw [tr_conj, tr_conj]
  have hee : ee Z j ∈ B0 Z := ((bas Z) j).2
  have hm := conj_mem_nilpotent_cone (inv_mem_Gz hg) hee
  rw [inv_inv] at hm
  exact (trace_nilpotent_cone_projection hZ h hm x).symm

end PositivityTheory.RgUd.T.Nil.Four.Phi2
end
end
