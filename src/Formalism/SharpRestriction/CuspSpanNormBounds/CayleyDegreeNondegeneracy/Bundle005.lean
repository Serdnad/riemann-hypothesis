module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDef
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.AbsPointwiseMonoConstant
import Formalism.FlagUnipotentLattices.AlgebraicIdentityHigherDegree
import Formalism.FormalDegreeBessel.Bundle002
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfGluingFacts
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExistsSmallMemFractionalIdeal
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ProdNormEmbeddingsEqAbsNorm
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.TraceInnerPosOfOrthonormalPair
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle006

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma MeasureTheory

theorem deg_epsI_empty {N : ℕ} : epsI (∅ : Finset (Fin N)) = 0 := by
  funext x; simp [epsI]

theorem deg_epsI_insert {N : ℕ} (I : Finset (Fin N)) (a : Fin N) (ha : a ∉ I) :
    epsI (insert a I) = epsI I + Pi.single a 1 := by
  funext x
  by_cases hx : x = a
  · subst hx; simp [epsI, ha]
  · simp [epsI, hx]

theorem deg_hc_int {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) (I : Finset (Fin N)) (x : Fin N) :
    ∃ m : ℤ, (μ + epsI I) x - ((N : ℝ) - 1) / 2 = (m : ℝ) := by
  obtain ⟨m, hm⟩ := h.2 x
  by_cases hx : x ∈ I
  · refine ⟨m + 1, ?_⟩
    simp only [Pi.add_apply, epsI, if_pos hx]
    push_cast
    linarith
  · refine ⟨m, ?_⟩
    simp only [Pi.add_apply, epsI, if_neg hx]
    linarith

theorem deg_hc_diff {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) (a b : Fin N) : ∃ m : ℤ, μ a - μ b = (m : ℝ) := by
  obtain ⟨m, hm⟩ := h.2 a
  obtain ⟨m', hm'⟩ := h.2 b
  refine ⟨m - m', ?_⟩
  push_cast
  linarith

theorem deg_hc_drop {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) (I : Finset (Fin N)) (a : Fin N)
    (hmax : ∀ x ∈ I, x < a) (h' : IsHCParam (μ + epsI (insert a I))) : IsHCParam (μ + epsI I) := by
  refine ⟨fun i j hij => ?_, deg_hc_int h I⟩
  have h1 := h.1 hij
  have h2 := h'.1 hij
  have ha : a ∉ I := fun hh => lt_irrefl _ (hmax a hh)
  simp only [Pi.add_apply, epsI, Finset.mem_insert] at h2 ⊢
  by_cases hja : j = a
  · subst hja
    rw [if_neg ha]
    split_ifs <;> linarith
  · by_cases hia : i = a
    · subst hia
      have hj : j ∉ I := fun hh => lt_asymm hij (hmax j hh)
      rw [if_neg ha, if_neg hj]
      linarith
    · simpa [hja, hia] using h2

theorem deg_ind_up {N : ℕ} {μ : Fin N → ℝ} (hμ : IsHCParam μ) (Pr : Finset (Fin N) → Prop) (h0 : Pr ∅)
    (hs : ∀ I a, a ∉ I → IsHCParam (μ + epsI I) → IsHCParam (μ + epsI I + Pi.single a 1) → Pr I → Pr (insert a I)) :
    ∀ I, IsHCParam (μ + epsI I) → Pr I := by
  intro I
  induction I using Finset.induction_on_max with
  | empty => intro _; exact h0
  | insert a I hmax ih =>
    intro h'
    have ha : a ∉ I := fun hh => lt_irrefl _ (hmax a hh)
    have h1 := deg_hc_drop hμ I a hmax h'
    refine hs I a ha h1 ?_ (ih h1)
    rw [add_assoc, ← deg_epsI_insert I a ha]
    exact h'

theorem deg_fdeg_pos {N : ℕ} {μ : Fin N → ℝ} (h : IsHCParam μ) : 0 < fdegHC μ := by
  unfold fdegHC
  apply div_pos
  · exact Finset.prod_pos fun a _ => Finset.prod_pos fun b hb =>
      abs_pos.2 (sub_ne_zero.2 (h.1 (Finset.mem_filter.1 hb).2).ne')
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    have h1 : a.1 < b.1 := (Finset.mem_filter.1 hb).2
    have h2 : (a.1 : ℝ) < b.1 := by exact_mod_cast h1
    linarith

theorem deg_set_bound {N : ℕ} {μ : Fin N → ℝ} (hμ : IsHCParam μ) : ∀ I : Finset (Fin N), IsHCParam (μ + epsI I) →
    ((N : ℝ) ^ I.card)⁻¹ ≤ fdegHC (μ + epsI I) / fdegHC μ ∧ fdegHC (μ + epsI I) / fdegHC μ ≤ (N : ℝ) ^ I.card := by
  have h0 := deg_fdeg_pos hμ
  refine deg_ind_up hμ _ ?_ ?_
  · rw [deg_epsI_empty, add_zero, div_self h0.ne']
    simp
  · intro I a ha h1 h2 ih
    obtain ⟨ihl, ihu⟩ := ih
    have hr := Formalism.QuantumDeterminants.fdegRatio N (μ + epsI I) a h1.1.injective (deg_hc_diff h1) h2.1.injective
    have hb := (Formalism.HermitianLatticeCounting.Final.ExpansionTerms.degStepBound N (μ + epsI I) a h1.1.injective (deg_hc_diff h1)).1 h2.1.injective
    rw [← hr] at hb
    have hN : (0 : ℝ) < N := by
      have : 0 < N := lt_of_le_of_lt (Nat.zero_le _) a.2
      exact_mod_cast this
    have hp1 := deg_fdeg_pos h1
    have e : fdegHC (μ + epsI I + Pi.single a 1) / fdegHC μ =
        (fdegHC (μ + epsI I) / fdegHC μ) * (fdegHC (μ + epsI I + Pi.single a 1) / fdegHC (μ + epsI I)) := by
      field_simp
    rw [deg_epsI_insert I a ha, ← add_assoc, Finset.card_insert_of_notMem ha, pow_succ, e, mul_inv]
    have hq : 0 ≤ fdegHC (μ + epsI I) / fdegHC μ := (div_pos hp1 h0).le
    constructor
    · refine mul_le_mul ihl ?_ (by positivity) hq
      rw [← one_div]; exact hb.1
    · exact mul_le_mul ihu hb.2 (le_trans (by positivity) hb.1) (by positivity)

theorem deg_set_bound' {N : ℕ} {μ : Fin N → ℝ} (hμ : IsHCParam μ) (I : Finset (Fin N)) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (h' : IsHCParam (μ + s • epsI I)) :
    ((N : ℝ) ^ I.card)⁻¹ ≤ fdegHC (μ + s • epsI I) / fdegHC μ ∧ fdegHC (μ + s • epsI I) / fdegHC μ ≤ (N : ℝ) ^ I.card := by
  rcases hs with rfl | rfl
  · rw [one_smul] at h' ⊢
    exact deg_set_bound hμ I h'
  · have e : μ + (-1 : ℝ) • epsI I + epsI I = μ := by
      rw [neg_one_smul, neg_add_cancel_right]
    have h := deg_set_bound h' I (by rw [e]; exact hμ)
    rw [e] at h
    have h0 := deg_fdeg_pos hμ
    have h1 := deg_fdeg_pos h'
    have hx : 0 < fdegHC μ / fdegHC (μ + (-1 : ℝ) • epsI I) := div_pos h0 h1
    rw [← inv_div (fdegHC μ) (fdegHC (μ + (-1 : ℝ) • epsI I))]
    refine ⟨inv_anti₀ hx h.2, ?_⟩
    have h5 := inv_anti₀ (lt_of_lt_of_le (by
      have := hx
      exact inv_pos.2 (lt_of_lt_of_le hx h.2)) le_rfl) h.1
    rwa [inv_inv] at h5

def deg_VandLine (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W →
    ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A →
      ∀ (I : Finset (Fin (2 * D.R.rS + D.R.k + 1))) (s : ℝ), (s = 1 ∨ s = -1) →
        ∀ A' : LocS W, GoodS D (lam' + s • epsI I) A' →
          A'.deg / A.deg = fdegHC (lam' + s • epsI I) / fdegHC lam'

theorem deg_cast_r (D : D7) : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [dimS_eq]

theorem degree_ratio_one_of_vandermonde (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ)
    (h : deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1) : DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 1 := by
  intro hH τ w w' hTT θ hθ W hW lam' hl A hA I s hs A' hA'
  rw [h hH τ w w' hTT θ hθ W hW lam' hl A hA I s hs A' hA', one_mul, Real.rpow_natCast, ← deg_cast_r]
  exact (deg_set_bound' hA.1 I s hs hA'.1).2

section Fam

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_scanl_head (xs : List ℕ) (a : ℕ) : xs.scanl (· + ·) a = a :: (xs.scanl (· + ·) a).tail := by
  cases xs <;> simp [List.scanl_cons]

theorem rows_scanl_pw : ∀ (xs : List ℕ) (a : ℕ), (∀ x ∈ xs, 1 ≤ x) →
    ((xs.scanl (· + ·) a).tail).Pairwise (· < ·) ∧ ∀ y ∈ (xs.scanl (· + ·) a).tail, a < y := by
  intro xs
  induction xs with
  | nil => intro a _; simp
  | cons x xs ih =>
    intro a h
    have hx : 1 ≤ x := h x (List.mem_cons_self ..)
    obtain ⟨ih1, ih2⟩ := ih (a + x) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.scanl_cons, List.tail_cons]
    rw [rows_scanl_head xs (a + x)]
    refine ⟨List.pairwise_cons.2 ⟨fun y hy => ih2 y hy, ih1⟩, ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · omega
    · have := ih2 y hy
      omega

theorem rows_pw_ext : ∀ (l₁ l₂ : List ℕ), l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂ := by
  intro l₁ l₂ h1 h2 hm
  have hp : l₁.Perm l₂ := (List.perm_ext_iff_of_nodup (h1.imp ne_of_lt) (h2.imp ne_of_lt)).2 hm
  exact hp.eq_of_sortedLE (List.sortedLE_iff_pairwise.2 (h1.imp le_of_lt))
    (List.sortedLE_iff_pairwise.2 (h2.imp le_of_lt))

theorem rows_blockEnds_pw {i : ℕ} (p : Point ℂ i) :
    (ptBlockEnds p).Pairwise (· < ·) ∧ ∀ y ∈ ptBlockEnds p, 0 < y := by
  have h := rows_scanl_pw (p.1.map Prod.snd) 0 (by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    exact (p.2.1 b hb).2)
  exact h

section Comparison₂

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def wordPairNormRelation (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t →
    1 ≤ ∏ τ, Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ ∧
    ∀ l, l ≤ D.R.rS + 1 → leadMinorE (termGramMatrix X t) l ≠ 0 → 1 ≤ ∏ τ, absDl D (termGramMatrix X t) l τ ^ 2

theorem rows_Dmin_ne_iff (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (τ : D.what₂.Tau) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    DminN (Y.W τ).z (Y.W τ).z' (Y.γ t τ) l ≠ 0 ↔ leadMinorE (termGramMatrix X t) l ≠ 0 := by
  rw [← norm_ne_zero_iff, d_norm_Dmin Y hrd t τ l hl]
  unfold absDl absReal
  have h0 : D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ))) ≠ 0 := (Real.rpow_pos_of_pos hrd _).ne'
  rw [mul_ne_zero_iff, norm_ne_zero_iff, map_ne_zero]
  exact ⟨fun h => h.1, fun h => ⟨h, h0⟩⟩

theorem rows_TermPtsTie_of (hrd : 0 < D.host.rdE) (hN : wordPairNormRelation X u u') : TermPtsTie X Y := by
  intro t hG hrel
  have hR : ∀ τ, RelPt D (Y.W τ).z (Y.W τ).z' (Y.γ t τ) (Y.pt t τ) := fun τ => (Y.rel t hG hrel τ).1
  have mem_iff : ∀ τ l, l ∈ ptBlockEnds (Y.pt t τ) ↔ (1 ≤ l ∧ l ≤ D.R.rS + 1 ∧ leadMinorE (termGramMatrix X t) l ≠ 0) := by
    intro τ l
    constructor
    · intro h
      have hl := blockEnd_le (Y.pt t τ) l h
      exact ⟨(rows_blockEnds_pw (Y.pt t τ)).2 l h, hl, (rows_Dmin_ne_iff Y hrd t τ l hl).1 (cell_ne_of_mem D (hR τ) l h)⟩
    · rintro ⟨h1, hl, hne⟩
      exact cell_mem_blockEnds D (hR τ) l h1 hl ((rows_Dmin_ne_iff Y hrd t τ l hl).2 hne)
  refine ⟨fun τ => ?_, fun τ τ' => ?_, ?_, fun τ₀ l hl => ?_⟩
  · obtain ⟨_, _, hz, hz', hT, hT', _⟩ := Y.goodW τ
    exact ⟨hz, hz', hT, hT', hR τ⟩
  · exact rows_pw_ext _ _ (rows_blockEnds_pw _).1 (rows_blockEnds_pw _).1 fun x => by rw [mem_iff τ x, mem_iff τ' x]
  · rw [Finset.prod_congr rfl fun τ _ => d_Gf_eq Y hrd t τ]
    exact (hN t hG hrel).1
  · obtain ⟨_, h2, h3⟩ := (mem_iff τ₀ l).1 hl
    rw [Finset.prod_congr rfl fun τ _ => by rw [d_norm_Dmin Y hrd t τ l h2]]
    exact (hN t hG hrel).2 l h2 h3

end Comparison₂

end Formalism.MainNotions.BridgeLemma₂

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.HermitianLatticesTheory

theorem second_orthogonal_vector_holds (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) : SecondOrthogonalVector K :=
  by
    classical
    intro V _ _ _ _ h L hs hL M hlat hint huni x hx hx0
    obtain ⟨e, he, hspan, hLe, ho⟩ := hL
    let b : Basis (Fin 2) K V := Basis.mk he (by rw [hspan])
    have hfull : Submodule.IsFullLattice K M := by
      refine { toIsLattice := hlat, span_eq_top := ?_ }
      apply Submodule.dualAnnihilator_eq_bot_iff.mp
      apply le_antisymm ?_ bot_le
      intro f hf
      let v : V := ∑ i : Fin 2, star (f (e i)) • e i
      have hpair : h v = f := by
        apply b.ext
        intro i
        fin_cases i <;> simp [v, LinearMap.map_smulₛₗ, starRingEnd_apply, ho, b, Basis.coe_mk]
      have hline (r : K) : r • v ∈ M := by
        rw [← huni]
        simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
        intro y hy
        have hy0 : h v y = 0 := by
          rw [hpair]
          exact (Submodule.mem_dualAnnihilator f).mp hf y (Submodule.subset_span hy)
        have hz : h y v = 0 := by simpa [hy0] using (hs.eq v y).symm
        simp [hz]
      have hv : v = 0 := by
        by_contra hv
        obtain ⟨i, hi⟩ : ∃ i, b.repr v i ≠ 0 := by
          by_contra hn
          push_neg at hn
          apply hv
          apply b.repr.injective
          ext i
          simp [hn i]
        let c := ((Finsupp.lapply i).comp b.repr.toLinearMap).restrictScalars (𝓞 K)
        have htop : M.map c = ⊤ := by
          rw [eq_top_iff]
          intro a _
          refine ⟨(a / b.repr v i) • v, hline _, ?_⟩
          simp [c, div_mul_cancel₀ _ hi]
        have : Module.Finite (𝓞 K) K := Module.finite_def.mpr (htop ▸ hlat.fg.map c)
        exact RingOfIntegers.not_isField K
          (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 K) K) (Field.toIsField K))
      rw [Submodule.mem_bot]
      simpa [hv] using hpair.symm
    exact exists_orthogonal_second_vector K hK V h L ⟨e, he, hspan, hLe, ho⟩ M hfull hint huni x hx hx0

theorem plane_class_count_holds (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) : PlaneClassCount K :=
  fun V _ _ _ _ h L hs hL s hreps B₁ B₂ hint hshort => class_count_plane_bound K hK V h L hs hL s hreps B₁ B₂ hint hshort

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem plane_mass_le_height_pow (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : UnitaryVolumeMass.Mass2At D large₂ C := by
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hfin := Formalism.MainNotions.StandardLattice.finrank_host D
  have hrd : rootDiscriminant D.host.E = D.host.rdE := rfl
  have h19 : 1 ≤ D.host.v := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := hH
    exact h19
  have hrd0 : 0 ≤ D.host.rdE := by
    have e : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [← e]; linarith
  refine plane_mass_bound_of_facts D large₂ C' Cl Cg cb Cu cT CT C _ (short_vector_every_place D.host.E hK)
    (second_orthogonal_vector_holds D.host.E hK) (plane_class_count_holds D.host.E hK) ?_ ?_ hC hH
  · rw [hrd]; positivity
  · rw [hrd, hfin]; push_cast; apply le_of_eq; ring

theorem plane_mass_bound_parameters (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) : UnitaryVolumeMass.stMass2 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C :=
  fun hH => plane_mass_le_height_pow D large₂ C' Cl Cg cb Cu cT CT C hC hH.1.1

section Family

variable {eps : ℝ} (Fm : FamP eps)

end Family

end Formalism.MainNotions.BridgeLemma₂

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LiftsConjugateUnderStabilizer (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlag D u fun F0 => ∀ Λ₁ Λ₂ : LatV D, IsRowLat D F0 Λ₁ → IsRowLat D F0 Λ₂ →
    Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) →
    ∃ n ∈ stabF D F0, (∀ x ∈ orth (hS D) F0.X, n x - x ∈ F0.X) ∧ gmap n Λ₁ = Λ₂

section Cl

variable {D : D7}

theorem partial_isotropic_top {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : F0.Xa D.R.rS = F0.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp

theorem partial_isotropic_le {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (j : ℕ) : F0.Xa j ≤ F0.X :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem isotropic_le_orth_isotropic {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) : F0.X ≤ orth (hS D) F0.X := by
  intro y hy
  rw [Formalism.MainNotions.mem_orth_iff]
  intro x hx
  exact Formalism.MainNotions.hT_swap_zero (Formalism.MainNotions.hT_zero_of_mem_X F0
    (fun a => Formalism.MainNotions.hT_swap_zero (Formalism.MainNotions.hT_zero_of_mem_X F0 (fun b => F0.e_iso b a) x hx)) y hy)

theorem isotropic_le_Lsub {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LatV D) :
    toO (hS D) F0.X ≤ Lsub Λ (lf D F0) :=
  le_inf le_sup_right (fun _ hx => isotropic_le_orth_isotropic F0 hx)

theorem Lsub_gmap_of_isometry {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hσ : σ ∈ isom (VS D).hT) (hX : F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X) (Λ : LatV D) :
    Lsub (gmap σ Λ) (lf D F0) = gmap σ (Lsub Λ (lf D F0)) := by
  have hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y := hσ
  have hmem : ∀ x, σ.symm x ∈ F0.X ↔ x ∈ F0.X := by
    intro x
    conv_rhs => rw [← hX]
    rw [Submodule.mem_map_equiv]
  have hgX : gmap σ (toO (hS D) F0.X) = toO (hS D) F0.X := by
    ext x
    rw [isomAct_mem_gmap]
    exact hmem x
  have hgO : gmap σ (toO (hS D) (orth (hS D) F0.X)) = toO (hS D) (orth (hS D) F0.X) := by
    ext y
    rw [isomAct_mem_gmap]
    change σ.symm y ∈ orth (hS D) F0.X ↔ y ∈ orth (hS D) F0.X
    rw [Formalism.MainNotions.mem_orth_iff, Formalism.MainNotions.mem_orth_iff]
    constructor
    · intro h x hx
      have := h (σ.symm x) ((hmem x).2 hx)
      rwa [← hσ' (σ.symm x) (σ.symm y), LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
    · intro h x hx
      have hx' : σ x ∈ F0.X := by
        rw [← hmem, LinearEquiv.symm_apply_apply]
        exact hx
      have := h (σ x) hx'
      rwa [← hσ' x (σ.symm y), LinearEquiv.apply_symm_apply]
  unfold Lsub Lrep
  rw [gmap_inf_cayley_degree_nondegeneracy, gmap_sup_cayley_degree_nondegeneracy, gmap_inf_cayley_degree_nondegeneracy]
  change (gmap σ Λ ⊓ toO (hS D) (orth (hS D) F0.X) ⊔ toO (hS D) F0.X) ⊓ toO (hS D) (orth (hS D) F0.X) =
    (gmap σ Λ ⊓ gmap σ (toO (hS D) (orth (hS D) F0.X)) ⊔ gmap σ (toO (hS D) F0.X)) ⊓
      gmap σ (toO (hS D) (orth (hS D) F0.X))
  rw [hgX, hgO]

theorem mul_mem_flag_stabilizer {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (ha : a ∈ stabF D F0) (hb : b ∈ stabF D F0) : a * b ∈ stabF D F0 := by
  refine ⟨(isom (VS D).hT).mul_mem ha.1 hb.1, fun j => ?_, ?_⟩
  · have e : ((a * b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
        (a : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (b : (VS D).V →ₗ[D.host.E] (VS D).V) := rfl
    rw [e, Submodule.map_comp, hb.2.1 j, ha.2.1 j]
  · change a (b F0.z) = F0.z
    rw [hb.2.2, ha.2.2]

end Cl

end Formalism.MainNotions.BridgeLemma₂

end
end
