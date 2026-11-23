module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGSDvr
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle009
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

section Coord2

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

theorem gram_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F)
    (hes : ∀ x, e (M.L.cj x) = (e x).swap)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F)) (Ph : Matrix (Fin n) (Fin n) 𝒪[F])
    (hπ : IsSplitCoord e H Λ π Ph) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E)
    (h1 : ∀ a b, G₀ a b ∈ M.L.O) (h2 : ∀ a b, G₀ b a = M.L.cj (G₀ a b)) (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    (∀ a b, H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}) ↔
      ∀ a b, resF F (∑ k, ∑ l, (π (v b)).1 k * (Ph k l : F) * (π (v a)).2 l) = resF F ((e (G₀ a b)).1) := by
  have hform := hπ.2.2.2
  have hL := fun a => (hπ.2.1 (v a)).1 (hv a)
  have hc : ∀ a b, InP ϖ (e (H.h (v b) (v a) - G₀ a b)).1 ↔
      resF F (∑ k, ∑ l, (π (v b)).1 k * (Ph k l : F) * (π (v a)).2 l) = resF F ((e (G₀ a b)).1) := by
    intro a b
    rw [map_sub, Prod.fst_sub, hform]
    exact inP_sub_iff hϖ (bil_mem _ _ (hL b).1 (hL a).2 Ph) ((hO _).1 (h1 a b)).1
  have hc2 : ∀ a b, (e (H.h (v b) (v a) - G₀ a b)).2 = (e (H.h (v a) (v b) - G₀ b a)).1 := by
    intro a b
    have hg : e (G₀ a b) = (e (G₀ b a)).swap := by rw [h2 b a, hes]
    rw [map_sub, map_sub, Prod.snd_sub, Prod.fst_sub, hform, hform, hg]
    rfl
  constructor
  · intro h a b
    exact (hc a b).1 ((mem_span_irr_iff e hO ϖ _).1 (h a b)).1
  · intro h a b
    rw [mem_span_irr_iff e hO ϖ]
    exact ⟨(hc a b).2 (h a b), by rw [hc2]; exact (hc b a).2 (h b a)⟩

theorem pi_sum (e : E ≃ₐ[F] F × F) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) :
    π (∑ i, c i • v i) = (∑ i, (e (c i)).1 • (π (v i)).1, ∑ i, (e (c i)).2 • (π (v i)).2) := by

  rw [map_sum]
  simp only [hπa]
  exact Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])

theorem prim_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    H.Prim Λ v ↔ LinearIndependent 𝓀[F] (redM F fun a => (π (v a)).1) ∧
      LinearIndependent 𝓀[F] (redM F fun a => (π (v a)).2) := by
  set X : ι → Fin n → F := fun a => (π (v a)).1 with hXd
  set Y : ι → Fin n → F := fun a => (π (v a)).2 with hYd
  have hX : ∀ a k, X a k ∈ 𝒪[F] := fun a k => ((hπL (v a)).1 (hv a)).1 k
  have hY : ∀ a k, Y a k ∈ 𝒪[F] := fun a k => ((hπL (v a)).1 (hv a)).2 k
  have hsum := pi_sum e π hπa v
  have hpiS : ∀ u w : Fin n → F, π (π.symm (u, w)) = (u, w) := fun u w => AddEquiv.apply_symm_apply _ _

  have hLI : LinearIndependent E v ↔ LinearIndependent F X ∧ LinearIndependent F Y := by
    constructor
    · intro hind
      constructor
      · rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h0 := Fintype.linearIndependent_iff.1 hind (fun i => e.symm (c i, 0)) (by
          apply π.injective
          rw [hsum, map_zero]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          ext k
          · simpa [hXd] using congrFun hc k
          · simp) i
        have := congrArg (fun z => (e z).1) h0
        simpa using this
      · rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h0 := Fintype.linearIndependent_iff.1 hind (fun i => e.symm (0, c i)) (by
          apply π.injective
          rw [hsum, map_zero]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          ext k
          · simp
          · simpa [hYd] using congrFun hc k) i
        have := congrArg (fun z => (e z).2) h0
        simpa using this
    · rintro ⟨hXi, hYi⟩
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h0 := congrArg π hc
      rw [hsum, map_zero] at h0
      have a1 := Fintype.linearIndependent_iff.1 hXi (fun i => (e (c i)).1) (congrArg Prod.fst h0) i
      have a2 := Fintype.linearIndependent_iff.1 hYi (fun i => (e (c i)).2) (congrArg Prod.snd h0) i
      apply e.injective
      rw [map_zero]
      exact Prod.ext a1 a2

  have hSat : (∀ x ∈ Λ, x ∈ Submodule.span E (Set.range v) → x ∈ Submodule.span M.L.O (Set.range v)) ↔
      SatF F X ∧ SatF F Y := by
    have hOsum : ∀ d : ι → M.L.O, ∑ i, d i • v i = ∑ i, (d i : E) • v i := fun d => rfl
    constructor
    · intro hs
      constructor
      · rintro u hu ⟨c, hc⟩
        have hxL : π.symm (u, 0) ∈ Λ := (hπL _).2 (by rw [hpiS]; exact ⟨hu, fun k => Subring.zero_mem _⟩)
        have hxs : π.symm (u, 0) ∈ Submodule.span E (Set.range v) := by
          rw [Submodule.mem_span_range_iff_exists_fun]
          refine ⟨fun i => e.symm (c i, 0), ?_⟩
          apply π.injective
          rw [hsum, hpiS]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          rw [← hc]
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hs _ hxL hxs)
        refine ⟨fun i => (e (d i)).1, fun i => ((hO _).1 (d i).2).1, ?_⟩
        have h0 := congrArg (fun z => (π z).1) hd
        simp only [hOsum, hsum, hpiS] at h0
        exact h0
      · rintro u hu ⟨c, hc⟩
        have hxL : π.symm (0, u) ∈ Λ := (hπL _).2 (by rw [hpiS]; exact ⟨fun k => Subring.zero_mem _, hu⟩)
        have hxs : π.symm (0, u) ∈ Submodule.span E (Set.range v) := by
          rw [Submodule.mem_span_range_iff_exists_fun]
          refine ⟨fun i => e.symm (0, c i), ?_⟩
          apply π.injective
          rw [hsum, hpiS]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          rw [← hc]
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hs _ hxL hxs)
        refine ⟨fun i => (e (d i)).2, fun i => ((hO _).1 (d i).2).2, ?_⟩
        have h0 := congrArg (fun z => (π z).2) hd
        simp only [hOsum, hsum, hpiS] at h0
        exact h0
    · rintro ⟨sX, sY⟩ x hx hxs
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
      have hπx := hsum c
      rw [hc] at hπx
      have hxc := (hπL x).1 hx
      obtain ⟨c1, hc1, hs1⟩ := sX (π x).1 hxc.1 ⟨_, (congrArg Prod.fst hπx).symm⟩
      obtain ⟨c2, hc2, hs2⟩ := sY (π x).2 hxc.2 ⟨_, (congrArg Prod.snd hπx).symm⟩
      have hmem : ∀ i, e.symm (c1 i, c2 i) ∈ M.L.O := fun i => by
        rw [hO, AlgEquiv.apply_symm_apply]; exact ⟨hc1 i, hc2 i⟩
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => ⟨_, hmem i⟩, ?_⟩
      rw [hOsum]
      apply π.injective
      rw [hsum]
      simp only [AlgEquiv.apply_symm_apply]
      exact Prod.ext hs1 hs2
  have hP : H.Prim Λ v ↔ (LinearIndependent F X ∧ LinearIndependent F Y) ∧ (SatF F X ∧ SatF F Y) := by
    unfold Loc.HermSp.Prim
    rw [← hLI, ← hSat]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hv, h.1, h.2⟩⟩
  rw [hP, ← dvr_prim_iff hϖ X hX, ← dvr_prim_iff hϖ Y hY]
  tauto

end Coord2

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fixedOK_of_rows (D : Formalism.BasicNotions.D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Λ ∈ what₂) : FixedOK D F0 Λ := by
  obtain ⟨hE, hz, hrr, -⟩ := hR
  obtain ⟨-, ⟨hlat, hunim, -, -⟩, hx⟩ := hrr.1 Λ hΛ
  refine ⟨hlat, hunim, hE, ?_, (D.cOf u)⁻¹, inv_ne_zero (D.cOf_ne u), ?_⟩
  · unfold XLam at hx
    intro a
    have hmem : F0.e a ∈ XS D F0 := by
      unfold XS
      clear hrr hz hunim hlat hΛ what₂ hE hx
      apply Submodule.subset_span
      refine ⟨a, 1, ?_, (one_smul _ _).symm⟩
      unfold ddS
      have hne : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) ≠ ⊥ :=
        Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
      have hk : ((D.R.rS : ℤ) - ((a : ℕ) : ℤ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
        have := a.isLt
        omega
      rw [hk, zpow_neg, zpow_natCast, ← FractionalIdeal.coeIdeal_pow,
        FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 (pow_ne_zero _ hne))]
      intro y hy
      rw [one_mul]
      exact FractionalIdeal.coeIdeal_le_one hy
    rw [← hx] at hmem
    exact hmem.1
  · rw [hz]
    rfl

theorem orbitReps_of (hN : UnipotentIntegralIsGroup) (hRk : RankG) (hG : GoodEZ) (h1 : Stage1) (h2 : Stage2) (hK : FinK) :
    OrbitReps := by
  intro D δ M hA L u u' hT F0 what₂ hR Z Λ hΛ
  have hF := fixedOK_of_rows D u F0 what₂ hR hΛ
  by_cases hne : (EZ (Tn u') F0 Λ Z).Nonempty
  · obtain ⟨F1, hF1⟩ := hne
    have hGZ : GZ (Tn u) (Tn u') Z ≠ 0 := by
      have h := hF1.1.2.2
      rw [gz_eq, hF1.2.2.2.2] at h
      exact h
    obtain ⟨R, hRm⟩ := hRk D (Tn u) (Tn u') Z hGZ
    obtain ⟨Wf, hWf, hW⟩ := h1 D (Tn u') F0 Λ hF Z R hRm
    obtain ⟨Af, hAf, hAx⟩ := h2 D (Tn u') F0 Λ hF Z R hRm Wf hWf
    refine ⟨{x | Good D (Tn u') F0 Λ Z x ∧ pWf D x ∈ Wf ∧ alM D x * R ∈ Af},
      hK D (Tn u') F0 Λ hF Z R hRm Wf Af hWf hAf, fun F' hF' => ?_⟩
    have g0 := hG D (Tn u') F0 Λ Z F' hF'
    obtain ⟨n1, hn1, hw1⟩ := hW _ g0
    have g1 := good_move D (Tn u') F0 Λ Z g0 hn1
    obtain ⟨n2, hn2, hw2, ha2⟩ := hAx _ g1 hw1
    have g2 := good_move D (Tn u') F0 Λ Z g1 hn2
    refine ⟨n1.trans n2, (hN D F0 Λ).2.2 n1 hn1 n2 hn2, ?_⟩
    have hact : act D (n1.trans n2) (F'.fl.e, F'.fl.z) = act D n2 (act D n1 (F'.fl.e, F'.fl.z)) := rfl
    show act D (n1.trans n2) (F'.fl.e, F'.fl.z) ∈ _
    rw [hact]
    exact ⟨g2, hw2 ▸ hw1, ha2⟩
  · refine ⟨∅, Set.finite_empty, fun F' hF' => absurd ⟨F', hF'⟩ hne⟩

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.DetGa

open Matrix

section General

variable {R : Type*} [CommRing R] {k : ℕ}

def cornerM (k : ℕ) (s : R) : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
  Matrix.of fun a b => if a = Fin.last k ∧ b = Fin.last k then s else 0

theorem det_updateRow_last_single (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    (A.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)).det = (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row _ (Fin.last k), Finset.sum_eq_single (Fin.last k)]
  · have hs : (A.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)).submatrix (Fin.last k).succAbove
        (Fin.last k).succAbove = A.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp [Fin.succAbove_last, Matrix.updateRow_ne (Fin.castSucc_lt_last i).ne]
    rw [hs]
    simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem det_updateRow_last_zero (A : Matrix (Fin (k + 1)) (Fin (k + 1)) R) :
    (A.updateRow (Fin.last k) 0).det = 0 :=
  Matrix.det_eq_zero_of_row_eq_zero (Fin.last k) fun j => by simp

theorem det_N (Z Y : Matrix (Fin (k + 1)) (Fin (k + 1)) R) (s t : R) :
    (Matrix.fromBlocks Z (cornerM k s) (cornerM k t) Y).det =
      Z.det * Y.det - s * t * ((Z.submatrix Fin.castSucc Fin.castSucc).det *
        (Y.submatrix Fin.castSucc Fin.castSucc).det) := by
  set i : Fin (k + 1) ⊕ Fin (k + 1) := Sum.inl (Fin.last k) with hi
  set j : Fin (k + 1) ⊕ Fin (k + 1) := Sum.inr (Fin.last k) with hj
  have hij : i ≠ j := by simp [hi, hj]
  set D0 : Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) R := Matrix.fromBlocks Z 0 0 Y with hD0
  set f : ((Fin (k + 1) ⊕ Fin (k + 1)) → R) → ((Fin (k + 1) ⊕ Fin (k + 1)) → R) → R :=
    fun r1 r2 => ((D0.updateRow i r1).updateRow j r2).det with hf
  have hN : Matrix.fromBlocks Z (cornerM k s) (cornerM k t) Y =
      (D0.updateRow i (D0 i + s • Pi.single j 1)).updateRow j (D0 j + t • Pi.single i 1) := by
    ext (a | a) (b | b) <;>
      by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>
      simp [hD0, hi, hj, cornerM, Matrix.updateRow_apply, Pi.single_apply, ha, hb]

  have hlin2 : ∀ r1 u v : (Fin (k + 1) ⊕ Fin (k + 1)) → R, ∀ c : R,
      f r1 (u + c • v) = f r1 u + c * f r1 v := by
    intro r1 u v c
    simp only [hf, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]

  have hlin1 : ∀ r2 u v : (Fin (k + 1) ⊕ Fin (k + 1)) → R, ∀ c : R,
      f (u + c • v) r2 = f u r2 + c * f v r2 := by
    intro r2 u v c
    simp only [hf]
    rw [Matrix.updateRow_comm _ hij, Matrix.updateRow_comm _ hij, Matrix.updateRow_comm _ hij,
      Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
  have hdet : (Matrix.fromBlocks Z (cornerM k s) (cornerM k t) Y).det =
      f (D0 i + s • Pi.single j 1) (D0 j + t • Pi.single i 1) := by
    rw [hN]

  have h00 : f (D0 i) (D0 j) = Z.det * Y.det := by
    simp only [hf, Matrix.updateRow_eq_self, hD0, Matrix.det_fromBlocks_zero₂₁]
  have h10 : f (Pi.single j 1) (D0 j) = 0 := by
    simp only [hf]
    rw [Matrix.updateRow_comm _ hij, Matrix.updateRow_eq_self]
    have : D0.updateRow i (Pi.single j 1) =
        Matrix.fromBlocks (Z.updateRow (Fin.last k) 0) (cornerM k 1) 0 Y := by
      ext (a | a) (b | b) <;>
        by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>
        simp [hD0, hi, hj, cornerM, Matrix.updateRow_apply, Pi.single_apply, ha, hb]
    rw [this, Matrix.det_fromBlocks_zero₂₁, det_updateRow_last_zero, zero_mul]
  have h01 : f (D0 i) (Pi.single i 1) = 0 := by
    simp only [hf, Matrix.updateRow_eq_self]
    have : D0.updateRow j (Pi.single i 1) =
        Matrix.fromBlocks Z 0 (cornerM k 1) (Y.updateRow (Fin.last k) 0) := by
      ext (a | a) (b | b) <;>
        by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>
        simp [hD0, hi, hj, cornerM, Matrix.updateRow_apply, Pi.single_apply, ha, hb]
    rw [this, Matrix.det_fromBlocks_zero₁₂, det_updateRow_last_zero, mul_zero]
  have h11 : f (Pi.single j 1) (Pi.single i 1) =
      -((Z.submatrix Fin.castSucc Fin.castSucc).det * (Y.submatrix Fin.castSucc Fin.castSucc).det) := by
    simp only [hf]
    have hsw : ((D0.updateRow i (Pi.single j 1)).updateRow j (Pi.single i 1)).submatrix
        (Equiv.swap i j) id =
        Matrix.fromBlocks (Z.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)) 0 0
          (Y.updateRow (Fin.last k) (Pi.single (Fin.last k) 1)) := by
      ext (a | a) (b | b) <;>
        by_cases ha : a = Fin.last k <;> by_cases hb : b = Fin.last k <;>
        simp [hD0, hi, hj, Matrix.updateRow_apply, Pi.single_apply, Equiv.swap_apply_def, ha, hb]
    have h := Matrix.det_permute (Equiv.swap i j) ((D0.updateRow i (Pi.single j 1)).updateRow j (Pi.single i 1))
    rw [hsw, Matrix.det_fromBlocks_zero₂₁, det_updateRow_last_single, det_updateRow_last_single,
      Equiv.Perm.sign_swap hij] at h
    rw [h]
    simp
  rw [hdet, hlin2, hlin1, hlin1, h00, h10, h01, h11]
  ring

end General

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ga_eq_submatrix (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D) :
    Ga T T' Z = (Matrix.fromBlocks Z (cornerM D.R.rS (-T)) (cornerM D.R.rS (-T')) Z.conjTranspose).submatrix id
      (Equiv.sumComm _ _) := by
  ext (a | a) (b | b) <;> simp [Ga, cornerM, Matrix.fromBlocks]

theorem leadMinorE_full (D : Formalism.BasicNotions.D7) (Z : MatZ D) : leadMinorE Z (D.R.rS + 1) = Z.det := by
  unfold leadMinorE
  rw [dite_eq_left le_rfl]
  congr 1

theorem leadMinorE_prev (D : Formalism.BasicNotions.D7) (Z : MatZ D) :
    leadMinorE Z D.R.rS = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadMinorE
  rw [dite_eq_left (Nat.le_succ _)]
  congr 1

theorem det_Ga (D : Formalism.BasicNotions.D7) (T T' : D.host.E) (Z : MatZ D) :
    (Ga T T' Z).det = ((Equiv.Perm.sign (Equiv.sumComm (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1))) : ℤ) : D.host.E) *
      GZ T T' Z := by
  rw [ga_eq_submatrix, Matrix.det_permute', det_N, GZ, leadMinorE_full, leadMinorE_prev,
    Matrix.det_conjTranspose, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]
  push_cast
  ring

end PI.UnitaryGroupMassFormula.CntFormula.DetGa

namespace PI.UnitaryGroupMassFormula.CntFormula

theorem gram_determinant_ne_zero : DetGaNe := by
  intro D T T' Z hG
  rw [DetGa.det_Ga]
  refine mul_ne_zero ?_ hG
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)))) with h | h <;>
    rw [h] <;> simp

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rank_gram : RankG := by
  intro D T T' Z hG
  classical
  by_cases hdet : Z.det = 0
  · have hm : leadMinorE Z D.R.rS ≠ 0 := by
      intro hm
      apply hG
      have h1 : leadMinorE Z (D.R.rS + 1) = 0 := by
        unfold Formalism.MainNotions.S.leadMinorE
        rw [dif_pos le_rfl, Fin.castLE_rfl, Matrix.submatrix_id_id]
        exact hdet
      simp [Formalism.L2.SG.CntLocal.GZ, h1, hm]
    have h : D.R.rS ≤ D.R.rS + 1 := Nat.le_succ _
    set B := Z.submatrix (Fin.castLE h) (Fin.castLE h) with hB
    have hBdet : B.det ≠ 0 := by
      have e : leadMinorE Z D.R.rS = B.det := by
        unfold Formalism.MainNotions.S.leadMinorE
        rw [dif_pos h]
      rwa [← e]
    refine ⟨Matrix.of fun j i => if hj : (j : ℕ) < D.R.rS then B⁻¹ ⟨j, hj⟩ i else 0, ?_⟩
    have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.2 hBdet)
    ext a i
    rw [← hBB]
    simp only [Matrix.mul_apply, betaZ, Matrix.submatrix_apply, Matrix.of_apply, Fin.sum_univ_castSucc,
      Fin.coe_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, not_false_eq_true, dif_neg, mul_zero,
      add_zero, id]
    rfl
  · refine ⟨(Z⁻¹).submatrix id Fin.castSucc, ?_⟩
    have hZ : Z * Z⁻¹ = 1 := Matrix.mul_nonsing_inv Z (isUnit_iff_ne_zero.2 hdet)
    unfold betaZ
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, hZ]
    exact Matrix.submatrix_one_embedding Fin.castSuccEmb

end PI.UnitaryGroupMassFormula.CntFormula
end
end
