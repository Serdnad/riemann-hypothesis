module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle685
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle731
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle726
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle716
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle736
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle735
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle722
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle734
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle729
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle668

@[expose] public section

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.StarLab

theorem exists_isTwInv_simpLab_star : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab w ψ' : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H lab → SimpLab H.bar q φ lab → IsTwInv H w → IsCentreSet H.bar q φ w →
    IsPolyFan H.bar q ψ' → Subordinate H.bar q ψ' φ → IsStarOf H.bar q φ w ψ' →
    ∃ lab' : InvFun (𝓞 E), IsTwInv H lab' ∧ SimpLab H.bar q ψ' lab' := by
  intro E _ _ _ H q φ lab w ψ' hDom hφ hlab hSL hw hC _ _ hS
  refine ⟨starLab lab w, isTwInv_starLab H hlab hw,
    fun X _ _ _ _ hX β hβ hp k hk => starLab_evalZ_smul lab w β hk (hSL.1 X hX β hβ hp k hk),
    fun X _ _ _ _ hX n γ' hγ' => ?_⟩
  rcases hS.2.2 X hX n γ' hγ' with ⟨m, γ, hγ, hfree, hin⟩ | ⟨m, γ, β₀, m', s, h, hγ, hb₀, hp₀, hw₀, hin₀, hf, hpos, hin⟩
  · obtain ⟨m₁, δ, hδ, hli, hinj, hγδ⟩ := hSL.2 X hX m γ hγ
    obtain ⟨g, hg1, hg2, hg3⟩ := exists_cut_of_cell_le (𝓞 E) H.bar φ X m₁ m δ γ hδ hγ hγδ
    obtain ⟨m₂, s, hfs⟩ := exists_isFaceCut δ g hg1
    have hδs : IsCell H.bar φ (fun j => δ (s j)) := GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell E H q φ hφ X hX (hDom X) m₁ δ hδ m₂ s g hfs
    have hfree' : ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone (fun j => δ (s j)) β → w.evalZ β = 0 :=
      fun β hb hp hc => hfree β hb hp (hg3 β hb hp (inRCone_of_sub s hc) (IsFaceCut.apply_eq_zero hfs hc))
    have hcell' := hS.1 X hX m₂ _ hδs hfree'
    have hnc : ∀ j, ¬ IsCentreRay w X (fun a b => (δ (s j) a b : ℝ)) := fun j hc => by
      obtain ⟨t, ht, β', hb', hp', hw', e⟩ := exists_of_isCentreRay w (hδs.mem j) (hδs.nonneg j) hc
      have := hfree' β' hb' hp' (InRCone.of_toReal_eq_smul (inRCone_self (fun j => δ (s j)) j) ht.le e)
      rw [hw'] at this
      norm_num at this
    refine ⟨m₂, _, hcell', hli.comp _ s.injective, fun i j hij => ?_, fun j => ?_⟩
    · simp only [starLab_evalZ_of_not lab w (hnc i), starLab_evalZ_of_not lab w (hnc j)] at hij
      exact s.injective (hinj (Real.exp_injective (by linarith)))
    · exact inRCone_trans (fun k => inRCone_face hfs (hγδ k) (hg2 k)) (hin j)
  · obtain ⟨m₁, δ, hδ, hli, hinj, hγδ⟩ := hSL.2 X hX m γ hγ
    have hγs : IsCell H.bar φ (fun j => γ (s j)) := GlobalTheory.T.polyFan_face_cut_by_intLinearForm_isCell E H q φ hφ X hX (hDom X) m γ hγ m' s h hf
    obtain ⟨g, hg1, hg2, hg3⟩ :=
      exists_cut_of_cell_le (𝓞 E) H.bar φ X m₁ m' δ (fun j => γ (s j)) hδ hγs (fun k => hγδ (s k))
    obtain ⟨m₂, s', hfs⟩ := exists_isFaceCut δ g hg1
    have hβ₀δ : InRCone δ β₀ := inRCone_trans hγδ hin₀
    have hgpos : 0 < g β₀ := by
      rcases (hβ₀δ.apply_nonneg g hg1).lt_or_eq with h' | h'
      · exact h'
      · exact (hpos.ne' (IsFaceCut.apply_eq_zero hf (hg3 β₀ hb₀ hp₀ hβ₀δ h'.symm))).elim
    have hcell' := hS.2.1 X hX m₁ δ hδ β₀ hb₀ hp₀ hw₀ hβ₀δ m₂ s' g hfs hgpos
    have hnc : ∀ j, ¬ IsCentreRay w X (fun a b => (δ (s' j) a b : ℝ)) := fun j hc => by
      obtain ⟨t, ht, β', hb', hp', hw', e⟩ := exists_of_isCentreRay w (hδ.mem (s' j)) (hδ.nonneg (s' j)) hc
      have hβ'δ : InRCone δ β' := InRCone.of_toReal_eq_smul (inRCone_self δ (s' j)) ht.le e
      have heq : β' = β₀ := (hC X hX).2.2 m₁ δ hδ β' hb' hp' β₀ hb₀ hp₀ hw' hw₀ hβ'δ hβ₀δ
      have h0 : g β' = 0 := IsFaceCut.apply_eq_zero hfs (InRCone.of_toReal_eq_smul (inRCone_self (fun j => δ (s' j)) j) ht.le e)
      rw [heq] at h0
      exact hgpos.ne' h0
    have hv0 : (starLab lab w).evalZ β₀ = -1 := starLab_evalZ_of_eq_one lab w hw₀
    have hvs : ∀ j, (starLab lab w).evalZ (δ (s' j)) = Real.exp (lab.evalZ (δ (s' j))) - 1 :=
      fun j => starLab_evalZ_of_not lab w (hnc j)
    have hsp : Submodule.span ℤ (Set.range fun j => δ (s' j)) ≤ LinearMap.ker g :=
      Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact LinearMap.mem_ker.2 ((hfs.2 (s' j)).2 ⟨j, rfl⟩))
    have hself : ∀ j, InRCone (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) (δ (s' j)) :=
      fun j => by simpa using inRCone_self (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) j.succ
    refine ⟨m₂ + 1, Fin.cons β₀ fun j => δ (s' j), hcell', ?_, ?_, fun j => ?_⟩
    · refine LinearIndependent.finCons' β₀ _ (hli.comp _ s'.injective) fun c y hy hz => ?_
      have h1 : g y = 0 := LinearMap.mem_ker.1 (hsp hy)
      have h2 := congrArg g hz
      rw [map_add (f := _), map_smul, h1, add_zero, map_zero, smul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_right hgpos.ne'
    · intro i j hij
      simp only at hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ, hv0, hvs] at hij
          linarith [Real.exp_pos (lab.evalZ (δ (s' j)))]
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ, hv0, hvs] at hij
          linarith [Real.exp_pos (lab.evalZ (δ (s' i)))]
        | succ j =>
          simp only [Fin.cons_succ, hvs] at hij
          exact congrArg Fin.succ (s'.injective (hinj (Real.exp_injective (by linarith))))
    · refine inRCone_trans (fun k => ?_) (hin j)
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using inRCone_self (Fin.cons β₀ fun j => δ (s' j) : Fin (m₂ + 1) → LinearMap.BilinForm ℤ X) 0
      · simp only [Fin.cons_succ]
        exact inRCone_trans hself (inRCone_face hfs (hγδ (s k)) (hg2 k))

end GlobalTheory.PolFan.StarLab
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.CarDim

namespace GlobalTheory.PolFan.CarDim

theorem exists_cell {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {ψ : InvFun (𝓞 E)} {X : Type}
    [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (hfan : IsPolyFanOn H.bar ψ X)
    {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms H.bar X) (hp : ∀ y, 0 ≤ β y y) :
    ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β := by
  have hmem : toReal β ∈ psdCone (bar := H.bar) (X := X) := by
    have := ConeSub.sum_smul_toReal_mem_psdCone (𝓞 E) H.bar X 1 ![β] ![1] (fun i => by fin_cases i; exact hβ)
      (fun i y => by fin_cases i; exact hp y) (fun i => by fin_cases i; norm_num)
    simpa using this
  obtain ⟨S, -, hS⟩ := hfan.finite
  obtain ⟨e, m, γ, c, hγ, -, hc, he⟩ := hS _ hmem
  refine ⟨m, fun i => pull e.symm.toLinearMap (γ i), isCell_pull_equiv hγ e.symm, c, hc, LinearMap.ext₂ fun a b => ?_⟩
  have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
  simpa [LinearMap.sum_apply] using this

end GlobalTheory.PolFan.CarDim

theorem GlobalTheory.PolFan.CarDim.exists_isCarrierDim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → ∃ lab : InvFun (𝓞 E), IsTwInv H lab ∧ IsCarrierDim H.bar q ψ lab := by
  intro E _ _ _ H q ψ hD hψ htw
  refine ⟨carFun H.bar ψ, GlobalTheory.T.carrierDimInvFun_hostFixingAut_invariant E H ψ htw, ?_⟩
  intro X _ _ _ _ hX β hβ hp
  have hfan := hψ X hX
  have hface := GlobalTheory.T.polyhedralPolarisation_face_cut_isCell E H ψ X hfan (hD X)
  rw [evalZ_carFun hβ hp]
  congr 1
  obtain ⟨m₀, γ₀, hγ₀, hin₀⟩ := exists_cell hfan hβ hp
  have hne : {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧
      genRank γ = k}.Nonempty := ⟨_, m₀, γ₀, hγ₀, hin₀, rfl⟩
  apply le_antisymm
  · obtain ⟨m, γ, h1, h2, h3⟩ := Nat.sInf_mem hne
    obtain ⟨m', δ, k1, k2, k3⟩ := GlobalTheory.T.exists_cell_quotient_by_radical_of_mem_cone E H ψ X hface β hβ hp m γ h1 h2
    exact (Nat.sInf_le (show genRank δ ∈ cdimSet H.bar ψ X (orad β) β from ⟨m', δ, k1, k2, rfl⟩)).trans (k3.trans h3.le)
  · have hne' : (cdimSet H.bar ψ X (orad β) β).Nonempty := by
      obtain ⟨m', δ, k1, k2, -⟩ := GlobalTheory.T.exists_cell_quotient_by_radical_of_mem_cone E H ψ X hface β hβ hp m₀ γ₀ hγ₀ hin₀
      exact ⟨_, m', δ, k1, k2, rfl⟩
    obtain ⟨m', δ, h1, h2, h3⟩ := Nat.sInf_mem hne'
    obtain ⟨m, γ, k1, k2, k3⟩ := GlobalTheory.T.cell_of_quotient_cell_radical_pullback E H ψ X hfan hface β hβ hp m' δ h1 h2
    unfold cdimQ
    rw [← h3]
    exact (Nat.sInf_le (show genRank γ ∈ {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧
      InRCone γ β ∧ genRank γ = k} from ⟨m, γ, k1, k2, rfl⟩)).trans k3
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.exists_uniform_strictness_and_face_cut_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → ∃ N₀ C₀ : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ N₀ ∧ StrictWith H.bar ψ N ℓ γ ∧ ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → ∃ h' : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, IsFaceCut γ s h' ∧ (∀ β, InRCone γ β → 0 < h β → 0 < h' β) ∧ ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → -(h' β) ≤ C₀ * ℓ β := by
  first | exact @GlobalTheory.PolFan.StrictData.exists_strict_data | exact GlobalTheory.PolFan.StrictData.exists_strict_data | (intros; apply GlobalTheory.PolFan.StrictData.exists_strict_data <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan.FaceSub

variable {X : Type} [AddCommGroup X]

theorem eq_of_toReal_sum_eq {p : ℕ} {u : Fin p → LinearMap.BilinForm ℤ X} (hu : LinearIndependent ℤ u)
    {r r' : Fin p → ℝ} (h : ∑ j, r j • toReal (u j) = ∑ j, r' j • toReal (u j)) : r = r' := by
  have hind : ∀ (d : Fin 0 → ℤ) (c : Fin p → ℤ), ∑ j, c j • u j = ∑ k, d k • (Fin.elim0 k : LinearMap.BilinForm ℤ X) →
      c = 0 := fun d c hc => by
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hc
    exact funext (Fintype.linearIndependent_iff.1 hu c hc)
  have h0 : ∑ j, (r - r') j • toReal (u j) = ∑ k, (Fin.elim0 k : ℝ) • toReal (Fin.elim0 k : LinearMap.BilinForm ℤ X) := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self, Finset.univ_eq_empty, Finset.sum_empty]
  exact sub_eq_zero.1 (eq_zero_of_toReal_rel hind h0)

theorem eq_zero_of_toReal_eq_zero {β : LinearMap.BilinForm ℤ X} (h : toReal β = 0) : β = 0 :=
  LinearMap.ext₂ fun a b => by
    have := LinearMap.congr_fun₂ h a b
    simp only [toReal_apply, LinearMap.zero_apply] at this
    simpa using this

theorem exists_ray {p q : ℕ} {u : Fin p → LinearMap.BilinForm ℤ X} {v : Fin q → LinearMap.BilinForm ℤ X}
    (hu : LinearIndependent ℤ u) (hv : ∀ l, v l ≠ 0) (A : Fin q → ℝ) (B : Fin q → Fin p → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hB : ∀ l k', 0 ≤ B l k') (k : Fin p) (hk : toReal (u k) = ∑ l, A l • toReal (v l))
    (hBe : ∀ l, 0 < A l → toReal (v l) = ∑ k', B l k' • toReal (u k')) :
    ∃ l, 0 < A l ∧ ∃ c : ℝ, 0 < c ∧ toReal (v l) = c • toReal (u k) := by
  classical
  set B' : Fin q → Fin p → ℝ := fun l k' => if 0 < A l then B l k' else 0 with hB'
  have hB'0 : ∀ l k', 0 ≤ B' l k' := fun l k' => by
    simp only [hB']; split_ifs <;> [exact hB l k'; exact le_rfl]
  have hterm : ∀ l, A l • toReal (v l) = A l • ∑ k', B' l k' • toReal (u k') := fun l => by
    rcases (hA l).lt_or_eq with hl | hl
    · simp only [hB', if_pos hl]; rw [hBe l hl]
    · simp [← hl]
  have hsum : ∑ k', (if k' = k then (1 : ℝ) else 0) • toReal (u k') =
      ∑ k', (∑ l, A l * B' l k') • toReal (u k') := by
    rw [Finset.sum_eq_single k (fun b _ hb => by simp [hb]) (by simp)]
    rw [if_pos rfl, one_smul, hk]
    simp only [hterm, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have hc := eq_of_toReal_sum_eq hu hsum
  have hk1 : ∑ l, A l * B' l k = 1 := by simpa using (congrFun hc k).symm
  obtain ⟨l, -, hl⟩ : ∃ l ∈ Finset.univ, A l * B' l k ≠ 0 := by
    by_contra hne
    push_neg at hne
    rw [Finset.sum_eq_zero hne] at hk1
    exact zero_ne_one hk1
  have hAl : 0 < A l := (hA l).lt_of_ne fun h0 => hl (by rw [← h0, zero_mul])
  have hoff : ∀ k', k' ≠ k → B l k' = 0 := fun k' hk' => by
    have h0 : ∑ l, A l * B' l k' = 0 := by simpa [hk'] using (congrFun hc k').symm
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_nonneg (hA l) (hB'0 l k'))).1 h0 l (Finset.mem_univ _)
    simpa [hB', if_pos hAl, hAl.ne'] using this
  have hvl : toReal (v l) = B l k • toReal (u k) := by
    rw [hBe l hAl, Finset.sum_eq_single k (fun b _ hb => by rw [hoff b hb, zero_smul]) (by simp)]
  refine ⟨l, hAl, B l k, (hB l k).lt_of_ne fun h0 => hv l (eq_zero_of_toReal_eq_zero ?_), hvl⟩
  rw [hvl, ← h0, zero_smul]

end GlobalTheory.PolFan.FaceSub


open GlobalTheory.PolFan.FaceSub in
theorem GlobalTheory.PolFan.eq_subfamily_of_face : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X] {m n : ℕ}
    (δ : Fin m → LinearMap.BilinForm ℤ X) (γ : Fin n → LinearMap.BilinForm ℤ X) (hδ : ∀ i, δ i ∈ balForms bar X)
    (hγ : ∀ j, γ j ∈ balForms bar X) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    LinearIndependent ℤ δ → LinearIndependent ℤ γ → (∀ i, IsPrim bar (⟨δ i, hδ i⟩ : balForms bar X)) →
    (∀ j, IsPrim bar (⟨γ j, hγ j⟩ : balForms bar X)) → (∀ j, InRCone δ (γ j)) → (∀ i, 0 ≤ h (δ i)) →
    (∀ j, h (γ j) = 0) → (∀ i, h (δ i) = 0 → InRCone γ (δ i)) →
    ∃ s : Fin n ↪ Fin m, (∀ j, γ j = δ (s j)) ∧ ∀ i, h (δ i) = 0 ↔ i ∈ Set.range s := by
  intro O _ bar X _ _ m n δ γ hδ hγ h hδi hγi hδp hγp hγc hδn hγz hZ
  classical
  choose b hb hbe using hγc
  choose a ha hae using hZ
  have hsupp : ∀ j i, 0 < b j i → h (δ i) = 0 := fun j i hji => by
    have e := apply_eq_of_toReal_eq (hbe j) h
    rw [hγz j, Int.cast_zero] at e
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hb j i) (by exact_mod_cast hδn i))).1 e.symm i
      (Finset.mem_univ _)
    have h2 : ((h (δ i) : ℤ) : ℝ) = 0 := (mul_eq_zero.1 this).resolve_left hji.ne'
    exact_mod_cast h2
  have hex1 : ∀ i, h (δ i) = 0 → ∃ j, γ j = δ i := fun i hi => by
    obtain ⟨j, -, c, hc, e⟩ := exists_ray hδi hγi.ne_zero (a i hi) b (ha i hi) hb i (hae i hi) (fun l _ => hbe l)
    exact ⟨j, GlobalTheory.T.eq_of_primitiveBalancedForm_same_real_ray bar (γ j) (δ i) (hγ j) (hδ i) (hγp j) (hδp i) c hc e⟩
  have hex2 : ∀ j, ∃ i, h (δ i) = 0 ∧ γ j = δ i := fun j => by
    obtain ⟨i, hbi, c, hc, e⟩ := exists_ray hγi hδi.ne_zero (b j)
      (fun i => if hi : h (δ i) = 0 then a i hi else 0) (hb j)
      (fun i j' => by split_ifs with hi <;> [exact ha i hi j'; exact le_rfl]) j (hbe j)
      (fun l hl => by rw [dite_eq_left (hsupp j l hl)]; exact hae l _)
    exact ⟨i, hsupp j i hbi, (GlobalTheory.T.eq_of_primitiveBalancedForm_same_real_ray bar (δ i) (γ j) (hδ i) (hγ j) (hδp i) (hγp j) c hc e).symm⟩
  choose s hsZ hsγ using hex2
  have hsinj : Function.Injective s := fun j j' hjj => hγi.injective (by rw [hsγ j, hsγ j', hjj])
  refine ⟨⟨s, hsinj⟩, hsγ, fun i => ⟨fun hi => ?_, ?_⟩⟩
  · obtain ⟨j, hj⟩ := hex1 i hi
    exact ⟨j, hδi.injective (show δ (s j) = δ i by rw [← hsγ j, hj])⟩
  · rintro ⟨j, rfl⟩
    exact hsZ j
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_linForm_cut_face_of_cell_in_cone : ∀ {O : Type} [CommRing O] (bar : O → O) (ψ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    {m n : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar ψ γ → IsCell bar ψ γ' → (∀ j, InRCone γ (γ' j)) →
    ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ i, 0 ≤ h (γ i)) ∧ (∀ j, h (γ' j) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → h β = 0 → InRCone γ' β := by
  first | exact @GlobalTheory.PolFan.CellFace.exists_face_form | exact GlobalTheory.PolFan.CellFace.exists_face_form | (intros; apply GlobalTheory.PolFan.CellFace.exists_face_form <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.isStarOf_of_cells_starCone_or_centreless : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell H.bar ψ' γ) → (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsCell H.bar ψ' (Fin.cons β₀ fun j => γ (s j))) → IsStarOf H.bar q ψ w ψ' := by
  first | exact @GlobalTheory.PolFan.StarCells.isStarOf_of_clauses | exact GlobalTheory.PolFan.StarCells.isStarOf_of_clauses | (intros; apply GlobalTheory.PolFan.StarCells.isStarOf_of_clauses <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.starSubdivision_cells_finite_cover_up_to_aut : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w ψ' : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → IsStarOf H.bar q ψ w ψ' → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∃ S : Set (LinearMap.BilinForm ℤ X), S.Finite ∧ ∀ B ∈ psdCone (bar := H.bar) (X := X), ∃ (e : X ≃ₗ[𝓞 E] X) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ), IsCell H.bar ψ' γ ∧ (∀ i, γ i ∈ S) ∧ (∀ i, 0 ≤ c i) ∧ pullR e.toLinearMap B = ∑ i, c i • toReal (γ i) := by
  first | exact @GlobalTheory.PolFan.isStarOf_finite_cover | exact GlobalTheory.PolFan.isStarOf_finite_cover | (intros; apply GlobalTheory.PolFan.isStarOf_finite_cover <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark


theorem _root_.GlobalTheory.T.inRealCone_cell_of_inFace_of_cellForm_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (v : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ v → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone v β → ∀ x ∈ balForms H.bar X, (∀ y, 0 ≤ x y y) → ψ.evalZ (β + x) = ψ.evalZ β + ψ.evalZ x → lab.evalZ (β + x) = lab.evalZ β → InRCone v x := by
  first | exact @GlobalTheory.PolFan.Mark.FaceIn.inRCone_of_add | exact GlobalTheory.PolFan.Mark.FaceIn.inRCone_of_add | (intros; apply GlobalTheory.PolFan.Mark.FaceIn.inRCone_of_add <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark

namespace GlobalTheory.PolFan

theorem cone_match_rays_of_nonneg {X : Type} [AddCommGroup X] {m₀ : ℕ}
    (p : Fin m₀ → LinearMap.BilinForm ℤ X) (t : Fin m₀ → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hp : LinearIndependent ℤ (fun i : {i // 0 < t i} => p i))
    (β : LinearMap.BilinForm ℤ X) (hβ : toReal β = ∑ i, t i • toReal (p i))
    (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (hδ : LinearIndependent ℤ δ)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) (hβ' : toReal β = ∑ j, c j • toReal (δ j))
    (h1 : ∀ i, 0 < t i → InRCone δ (p i))
    (h2 : ∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧
      toReal (δ j) = ∑ i, a i • toReal (p i)) :
    (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
    (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧
      c j = t i * d) := by
  classical
  set e := (Fintype.equivFin {i // 0 < t i}).symm with he
  have key : ∀ a : Fin m₀ → ℝ, (∀ i, t i = 0 → a i = 0) →
      ∑ i', a (e i') • toReal (p (e i')) = ∑ i, a i • toReal (p i) := by
    intro a ha
    refine Fintype.sum_of_injective (fun i' => ((e i' : {i // 0 < t i}) : Fin m₀))
      (Subtype.val_injective.comp e.injective) _ _ ?_ (fun _ => rfl)
    intro i hi
    have : t i = 0 := by
      by_contra h0
      exact hi ⟨e.symm ⟨i, lt_of_le_of_ne (ht i) (Ne.symm h0)⟩, by simp⟩
    rw [ha i this, zero_smul]
  obtain ⟨r1, r2⟩ := GlobalTheory.T.coneMatch_rays_of_linearIndependent_intForms (fun i' => p (e i')) δ (hp.comp e e.injective) hδ
    (fun i' => t (e i')) c (fun i' => (e i').2) hc
    (by rw [key t (fun _ h => h), ← hβ, hβ'])
    (fun i' => h1 _ (e i').2)
    (fun j hj => by
      obtain ⟨a, ha0, ha1, ha2⟩ := h2 j hj
      exact ⟨fun i' => a (e i'), fun i' => ha0 _, by rw [ha2, ← key a ha1]⟩)
  refine ⟨fun i hi => ?_, fun j hj => ?_⟩
  · simpa using r1 (e.symm ⟨i, hi⟩)
  · obtain ⟨i', h⟩ := r2 j hj
    exact ⟨e i', (e i').2, h⟩

end GlobalTheory.PolFan
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.Mark


theorem _root_.GlobalTheory.T.cell_leastDim_vanishes_where_form_vanishes_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ lab : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCarrierDim H.bar q ψ lab → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → Dominates H.bar X → ∀ (m : ℕ) (τ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ τ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone τ β → (genRank τ : ℝ) ≤ lab.evalZ β → ∀ j y, β y y = 0 → τ j y y = 0 := by
  first | exact @GlobalTheory.PolFan.Mark.vanish_of_inRCone_of_genRank_le | exact GlobalTheory.PolFan.Mark.vanish_of_inRCone_of_genRank_le | (intros; apply GlobalTheory.PolFan.Mark.vanish_of_inRCone_of_genRank_le <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.starDepth_le_strictnessGap_off_centres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → 0 < N → StrictWith H.bar ψ N ℓ γ → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → (starDepth H.bar ψ w).evalZ β ≤ ℓ β - N * ψ.evalZ β := by
  first | exact @GlobalTheory.PolFan.StarGap.starDepth_le_gap | exact GlobalTheory.PolFan.StarGap.starDepth_le_gap | (intros; apply GlobalTheory.PolFan.StarGap.starDepth_le_gap <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem depth_le_starDepth : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (v : LinearMap.BilinForm ℤ X) (t : ℝ), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X → (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v ≠ 0 → (∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v) → 0 ≤ t → B - t • toReal v ∈ rcone γ → t ≤ evalR (starDepth bar ψ w) B := by
  intro O _ bar ψ w X _ _ _ m γ B v t hγ hB hv hvp hvw hvc hv0 huniq ht hBt
  rcases ht.eq_or_lt with rfl | ht
  · exact starDepth_eval_nonneg _
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' O X
  show t ≤ (starDepth bar ψ w).eval X (fun a b => B a b)
  rw [InvFun.eval_eq _ hπ]
  exact le_csSup (GlobalTheory.T.starDepthSet_bddAbove_of_unique_centre O bar ψ w X m γ B v hγ hB hv hvp hv0 huniq n π hπ)
    (GlobalTheory.T.mem_starDepthSet_through_radicalFree_presentation O bar ψ w X m γ B v t hγ hB hv hvp hvw hvc ht hBt n π hπ)

end GlobalTheory.PolFan
end
end
