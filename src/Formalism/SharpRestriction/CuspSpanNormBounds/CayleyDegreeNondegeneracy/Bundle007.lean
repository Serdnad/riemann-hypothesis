module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfGluingFacts
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle005
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsCnt
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle004
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
public import Formalism.FormalDegreeBessel.FinalG
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsSiz
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTrm
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cl

variable (D : D7) (u : D.what₂.Word) (hT : Tu D u ≠ 0) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

include he in
theorem isotropic_le_orth_range : F0.X ≤ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  rw [he]
  change D.sp.hypE a ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))
  rw [Formalism.MainNotions.mem_orth_iff]
  rintro _ ⟨w, rfl⟩
  exact (D.sp.hyp_orthX a w).1

include hz in
theorem z_mem_orth_range : F0.z ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
  rw [Formalism.MainNotions.mem_orth_iff]
  rintro _ ⟨w, rfl⟩
  rw [hz]
  exact Formalism.MainNotions.hT_swap_zero (z_orth_embedding D u w)


include hT he hz in
theorem exists_decomp_orth_isotropic_plus (x : (VS D).V) (hx : x ∈ orth (hS D) F0.Xplus) :
    ∃ w, x - D.sp.iXY 0 w ∈ F0.X := by
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hx' : x ∈ Wsp D ⊔ Xsp (lf D F0) := by rw [hW]; exact hx
  obtain ⟨a, ⟨w, rfl⟩, ξ, hξ, rfl⟩ := Submodule.mem_sup.1 hx'
  exact ⟨w, by simpa using hξ⟩


include hT he hz in
theorem exists_decomp_orth_isotropic (x : (VS D).V) (hx : x ∈ orth (hS D) F0.X) :
    ∃ (w : (D.sp.X 0).V) (c : D.host.E), x - (D.sp.iXY 0 w + c • F0.z) ∈ F0.X := by
  have hT' : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hx' := (Formalism.MainNotions.mem_orth_iff _ _).1 hx
  obtain ⟨w, hw⟩ := exists_decomp_orth_isotropic_plus D u hT F0 he hz
    (x - (-((VS D).hT F0.z x) / ((Tu D u : ℕ) : D.host.E)) • F0.z) (by
      rw [Formalism.MainNotions.mem_orth_iff]
      refine Formalism.MainNotions.hT_zero_of_mem_Xplus F0 (fun a => ?_) ?_
      · rw [map_sub, map_smul, F0.z_orth a, smul_zero, sub_zero]
        exact hx' _ (Submodule.subset_span ⟨a, rfl⟩)
      · rw [map_sub, map_smul, F0.z_norm, smul_eq_mul]
        field_simp
        ring)
  refine ⟨w, -((VS D).hT F0.z x) / ((Tu D u : ℕ) : D.host.E), ?_⟩
  rw [add_comm, ← sub_sub]
  exact hw


include hT he hz in
theorem Lsub_eq_of_latticeWithZ_eq (Λ₁ Λ₂ : LatV D) (h : latticeWithZ D F0 Λ₁ = latticeWithZ D F0 Λ₂) :
    Lsub Λ₁ (lf D F0) = Lsub Λ₂ (lf D F0) := by
  have key : ∀ Λ : LatV D, ∀ x, x ∈ Lsub Λ (lf D F0) ↔
      x ∈ orth (hS D) F0.X ∧ ∀ (w : (D.sp.X 0).V) (c : D.host.E),
        x - (D.sp.iXY 0 w + c • F0.z) ∈ F0.X → (w, c) ∈ latticeWithZ D F0 Λ := by
    intro Λ x
    have hj : ∀ (w : (D.sp.X 0).V) (c : D.host.E), (w, c) ∈ latticeWithZ D F0 Λ ↔ D.sp.iXY 0 w + c • F0.z ∈ Lsub Λ (lf D F0) := by
      intro w c
      unfold latticeWithZ
      rw [Submodule.mem_comap]
      simp [embedWithZ]
    constructor
    · intro hx
      refine ⟨hx.2, fun w c hξ => ?_⟩
      rw [hj]
      have := (Lsub Λ (lf D F0)).sub_mem hx (isotropic_le_Lsub F0 Λ hξ)
      simpa using this
    · rintro ⟨hxO, hall⟩
      obtain ⟨w, c, hξ⟩ := exists_decomp_orth_isotropic D u hT F0 he hz x hxO
      have h1 := (hj w c).1 (hall w c hξ)
      have := (Lsub Λ (lf D F0)).add_mem h1 (isotropic_le_Lsub F0 Λ hξ)
      simpa using this
  ext x
  rw [key Λ₁, key Λ₂, h]

def projWAlt : (VS D).V →ₗ[D.host.E] (D.sp.X 0).V :=
  (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D)).symm.toLinearMap ∘ₗ LinearMap.fst D.host.E _ _ ∘ₗ
    (Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)).symm.toLinearMap

theorem projW_apply (w : (D.sp.X 0).V) (b : (VS D).V) (hb : b ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))) :
    projWAlt D (D.sp.iXY 0 w + b) = w := by
  have e : D.sp.iXY 0 w + b = Submodule.prodEquivOfIsCompl _ _ (isCompl_range_orth_range D)
      (LinearEquiv.ofInjective (D.sp.iXY 0) (embedding_W_injective D) w, ⟨b, hb⟩) := by
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  rw [e]
  unfold projWAlt
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.fst_apply]


include hT he hz in
theorem exists_induced_isometry_W (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hσ : σ ∈ stabF D F0) :
    ∃ γ ∈ isom (D.sp.X 0).hT, ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ w) ∈ F0.X := by
  have hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y := hσ.1
  have hX : F0.X.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := by
    have := hσ.2.1 D.R.rS
    rwa [partial_isotropic_top] at this
  have hXp : F0.Xplus.map (σ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.Xplus := by
    unfold FlagG.Xplus
    rw [Submodule.map_sup, hX, Submodule.map_span, Set.image_singleton]
    congr 3
    exact hσ.2.2
  have hWO : ∀ w, D.sp.iXY 0 w ∈ orth (hS D) F0.Xplus := by
    intro w
    have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
    have : D.sp.iXY 0 w ∈ Wsp D ⊔ Xsp (lf D F0) := Submodule.mem_sup_left ⟨w, rfl⟩
    rw [hW] at this
    exact this
  have hdec : ∀ w, ∃ w', σ (D.sp.iXY 0 w) - D.sp.iXY 0 w' ∈ F0.X := by
    intro w
    refine exists_decomp_orth_isotropic_plus D u hT F0 he hz _ ?_
    rw [Formalism.MainNotions.mem_orth_iff]
    intro x hx
    rw [← hXp] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    change (VS D).hT (σ x') (σ (D.sp.iXY 0 w)) = 0
    rw [hσ']
    exact (Formalism.MainNotions.mem_orth_iff _ _).1 (hWO w) x' hx'
  let γ0 : (D.sp.X 0).V →ₗ[D.host.E] (D.sp.X 0).V :=
    projWAlt D ∘ₗ (σ : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ D.sp.iXY 0
  have hγ0 : ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ0 w) ∈ F0.X := by
    intro w
    obtain ⟨w', hw'⟩ := hdec w
    have e : γ0 w = w' := by
      change projWAlt D (σ (D.sp.iXY 0 w)) = w'
      have : σ (D.sp.iXY 0 w) = D.sp.iXY 0 w' + (σ (D.sp.iXY 0 w) - D.sp.iXY 0 w') := by abel
      rw [this]
      exact projW_apply D w' _ (isotropic_le_orth_range D u F0 he hw')
    rw [e]
    exact hw'
  have hiso : ∀ w w', (D.sp.X 0).hT (γ0 w) (γ0 w') = (D.sp.X 0).hT w w' := by
    intro w w'
    have e1 : σ (D.sp.iXY 0 w) = D.sp.iXY 0 (γ0 w) + (σ (D.sp.iXY 0 w) - D.sp.iXY 0 (γ0 w)) := by abel
    have e2 : σ (D.sp.iXY 0 w') = D.sp.iXY 0 (γ0 w') + (σ (D.sp.iXY 0 w') - D.sp.iXY 0 (γ0 w')) := by abel
    have h1 := hσ' (D.sp.iXY 0 w) (D.sp.iXY 0 w')
    rw [e1, e2, inner_decomp_orth_range D _ _ _ _ (isotropic_le_orth_range D u F0 he (hγ0 w))
      (isotropic_le_orth_range D u F0 he (hγ0 w')), embedding_isometry_W,
      (Formalism.MainNotions.mem_orth_iff _ _).1 (isotropic_le_orth_isotropic F0 (hγ0 w')) _ (hγ0 w), add_zero] at h1
    exact h1
  have hinj : Function.Injective γ0 := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    refine (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 x (fun y => ?_))
    rw [← hiso y x, hx, map_zero]
  refine ⟨LinearEquiv.ofInjectiveEndo γ0 hinj, fun w w' => ?_, fun w => ?_⟩
  · simpa using hiso w w'
  · simpa using hγ0 w

end Cl

end Formalism.MainNotions.BridgeLemma₂

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

theorem rows_rdE_pos (D : D7) : 0 < D.host.rdE := by
  unfold Host.rdE
  exact Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _

def FamilyGramHypotheses : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    wordPairNormRelation (X x hx i) u u' ∧ @LatticeDeterminantFactorization (Fm.D x i) (X x hx i) u u' ∧
      wordPairEntriesInLattice (X x hx i) u u' ∧ wordPairTermInjective (X x hx i) (Y x hx i u u')

theorem family_gram_facts_of_hypotheses (h : FamilyGramHypotheses Fm C1 X Y) : rows_TiesF Fm C1 X Y := fun x hx i u u' =>
  ⟨rows_TermPtsTie_of _ (rows_rdE_pos _) (h x hx i u u').1, (h x hx i u u').2.1, (h x hx i u u').2.2.1⟩

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lab

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

def pairCountExponentShift (D : D7) (c Ch : ℝ) : ℝ :=
  c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f + 4 * (max (Ch - c) 0 * (D.R.m : ℝ) ^ 2 * D.R.f * ((D.R.rS : ℝ) + 1))

def pairCountExponent (D : D7) (c : ℝ) (s : ℕ) : ℝ := c * ((s : ℝ) + D.R.m) * D.R.m + c * cF D.R.f

theorem rows_gg_eq (D : D7) : gg D = (gS D : ℝ) := by unfold gg gS; push_cast; ring

theorem rows_Tr_pos (D : D7) (w : D.what₂.Word) : 0 < Tr D w := by
  unfold Tr; exact_mod_cast (D.mem w).A.T_prime.pos

theorem rows_NT_pos (D : D7) (w : D.what₂.Word) : 0 < NT D w := by
  unfold NT; exact pow_pos (rows_Tr_pos D w) _

def wordPairGramGood (X : TermTie D) (u u' : D.what₂.Word) (large₂ : SizeData₂ D) (c : ℝ) (Z : GramM D) : Prop :=
  ∃ t : D.s.Term u u', D.s.Gterm t ≠ 0 ∧ D.s.relevant t ∧ ZEquiv (termGramMatrix X t) Z ∧
    ∀ (j : ℕ) (I J : Fin j ↪o Fin (D.R.rS + 1)), (Z.submatrix I J).det ≠ 0 →
      ∏ τ, max 1 (UnitaryVolumeMass.absMinor D Z I J τ) ≤ HHZ D large₂.sc.b c (termGramMatrix X t)


open Classical in
def termReducedGramMatrix {C' Cl Cg cb Cu cT CT C0 A c : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (t : D.s.Term u u') : GramM D :=
  if h : D.s.Gterm t ≠ 0 ∧ D.s.relevant t then Classical.choose (rows_reduced_exists Y hH hHH t h.1 h.2) else 0

theorem rows_Zr_spec {C' Cl Cg cb Cu cT CT C0 A c : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hrel : D.s.relevant t) :
    ZEquiv (termGramMatrix X t) (termReducedGramMatrix Y hH hHH t) ∧ wordPairGramGood X u u' large₂ c (termReducedGramMatrix Y hH hHH t) := by
  have h := Classical.choose_spec (rows_reduced_exists Y hH hHH t hG hrel)
  have e : termReducedGramMatrix Y hH hHH t = Classical.choose (rows_reduced_exists Y hH hHH t hG hrel) := by
    unfold termReducedGramMatrix; rw [dite_eq_left ⟨hG, hrel⟩]
  rw [e]
  exact ⟨h.1, t, hG, hrel, h.1, h.2⟩

theorem rows_Gz_pos (hT : TermPtsTie X Y) (hrd : 0 < D.host.rdE) (t : D.s.Term u u') (hG : D.s.Gterm t ≠ 0)
    (hrel : D.s.relevant t) (τ : D.what₂.Tau) : 0 < Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ := by
  obtain ⟨h1, _, _, _⟩ := hT t hG hrel
  obtain ⟨hz, hz', hTz, hTz', hR⟩ := h1 τ
  rw [← d_Gf_eq Y hrd t τ]
  exact lt_of_le_of_ne (Formalism.QuantumDeterminants.gNonneg D.R.k D.R.rS _ _ hz hz' (hTz ▸ rows_Tr_pos D u) (hTz' ▸ rows_Tr_pos D u') _ hR.1)
    (Ne.symm hR.2.2)

theorem two_le_gg_of_count_hypotheses {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) : 2 ≤ gg D := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h12, _, h14, _⟩ := hH.1
  have hb := d_two_le_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have h0 : (2 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := by
    have : (2 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
    calc (2 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := this
      _ ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
  have g1 : (2 : ℝ) ≤ D.host.g 0 := h0.trans h12
  have g2 : (2 : ℝ) ≤ D.host.g 1 := h0.trans h14
  unfold gg
  nlinarith

theorem gramProductG0_pos {C' Cl Cg cb Cu cT CT C0 c : ℝ} (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hT : TermPtsTie X Y)
    {Z : GramM D} (hZ : wordPairGramGood X u u' large₂ c Z) : 0 < wordPairGramProduct D u u' Z := by
  obtain ⟨t, hG, hrel, hE, _⟩ := hZ
  rw [gramProductG0_equiv_invariant hE]
  unfold wordPairGramProduct
  have hg : 0 < (gS D : ℝ) := by rw [← rows_gg_eq]; linarith [two_le_gg_of_count_hypotheses hH]
  exact mul_pos (Finset.prod_pos fun τ _ => rows_Gz_pos Y hT (d_rdE_pos hH) t hG hrel τ) (by positivity)

theorem rows_one_le_HHZ (D : D7) (large₂ : SizeData₂ D) {c : ℝ} (hc : 0 ≤ c) (Z : GramM D) : 1 ≤ HHZ D large₂.sc.b c Z := by
  unfold HHZ
  have hb := d_two_le_b D large₂
  have h1 : 1 ≤ (large₂.sc.b ^ (c * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (c * (D.R.m : ℝ)) :=
    Real.one_le_rpow (Real.one_le_rpow (by linarith) (by positivity)) (by positivity)
  have h2 : 1 ≤ sizeZ D large₂.sc.b c Z ^ 4 := one_le_pow₀ (rows_one_le_sizeZ _ _ _)
  nlinarith

theorem gramProductG0_le_height {C' Cl Cg cb Cu cT CT C0 A c : ℝ} (hH : Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A)
    (hHH : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c) (hT : TermPtsTie X Y)
    {Z : GramM D} (hZ : wordPairGramGood X u u' large₂ c Z) : wordPairGramProduct D u u' Z ≤ HHZ D large₂.sc.b c Z := by
  obtain ⟨t, hG, hrel, hE, _⟩ := hZ
  rw [gramProductG0_equiv_invariant hE, rows_HHZ_inv hE]
  have hR : RelZ D (ZhatL (lf D Y.F0) (X.fl' t)) := by
    have h := X.pt_cell t hG hrel
    rw [Y.fl_eq t] at h
    exact ⟨_, h⟩
  obtain ⟨_, h2, _⟩ := hHH hH Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero (X.abelian₂ t) (Y.isRows.1 _ (Y.Lam_mem t)) (X.fl' t)
    (rows_isTermF Y t hG) hR
  rw [← Y.fl_eq t] at h2
  have hg := two_le_gg_of_count_hypotheses hH.1
  rw [rows_gg_eq] at hg
  have hp : ∀ τ, 0 < Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ := fun τ => rows_Gz_pos Y hT (d_rdE_pos hH.1) t hG hrel τ
  have h3 : ∏ τ, Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ ≤ HHZ D large₂.sc.b c (termGramMatrix X t) :=
    le_trans (Finset.prod_le_prod₀ (fun τ _ => (hp τ).le) fun τ _ => le_max_right _ _) h2
  unfold wordPairGramProduct
  have h4 : ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f) ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
  calc (∏ τ, Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f)
      ≤ (∏ τ, Gz D (Tu D u) (Tu D u') (termGramMatrix X t) τ) * 1 :=
        mul_le_mul_of_nonneg_left h4 (Finset.prod_nonneg fun τ _ => (hp τ).le)
    _ ≤ _ := by rw [mul_one]; exact h3

theorem rows_massS_nonneg (D : D7) (j : ℕ) : 0 ≤ massS D j := by
  unfold massS massU; exact d_mass_nonneg _ _

theorem rows_XiS_nonneg (D : D7) (w : D.what₂.Word) {HH c : ℝ} (hHH : 0 ≤ HH) (hc : 0 ≤ c) (s : ℕ) : 0 ≤ XiS D w HH c s := by
  unfold XiS Xi
  have hN := (rows_NT_pos D w).le
  split_ifs
  · exact div_nonneg (mul_nonneg (rows_massS_nonneg D _) (rows_massS_nonneg D _)) (rows_massS_nonneg D _)
  · positivity
  · exact le_rfl

theorem rows_Xi_le (D : D7) (w : D.what₂.Word) {HH P2 σ c : ℝ} (hHH : 0 ≤ HH) (hP2 : 0 ≤ P2) (hσ : 1 ≤ σ) (hc : 0 ≤ c)
    (h : HH ≤ P2 * σ ^ 4) (s : ℕ) : XiS D w HH c s ≤ XiS D w P2 c s * σ ^ (4 * (c * D.R.k)) := by
  have hσ0 : 0 < σ := by linarith
  have h1 : 1 ≤ σ ^ (4 * (c * D.R.k)) := Real.one_le_rpow hσ (by positivity)
  have hN := (rows_NT_pos D w).le
  unfold XiS Xi
  split_ifs
  · exact le_mul_of_one_le_right
      (div_nonneg (mul_nonneg (rows_massS_nonneg D _) (rows_massS_nonneg D _)) (rows_massS_nonneg D _)) h1
  · have e : (HH * NT D w) ^ (c * D.R.k) ≤ (P2 * NT D w) ^ (c * D.R.k) * σ ^ (4 * (c * D.R.k)) := by
      calc (HH * NT D w) ^ (c * D.R.k) ≤ ((P2 * NT D w) * σ ^ 4) ^ (c * (D.R.k : ℝ)) := by
            apply Real.rpow_le_rpow (by positivity) _ (by positivity)
            calc HH * NT D w ≤ (P2 * σ ^ 4) * NT D w := mul_le_mul_of_nonneg_right h hN
              _ = (P2 * NT D w) * σ ^ 4 := by ring
        _ = (P2 * NT D w) ^ (c * D.R.k) * σ ^ (4 * (c * D.R.k)) := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast σ 4, ← Real.rpow_mul hσ0.le]
            norm_num
    calc (c * D.R.k) ^ (D.R.k * D.R.f) * (HH * NT D w) ^ (c * D.R.k)
        ≤ (c * D.R.k) ^ (D.R.k * D.R.f) * ((P2 * NT D w) ^ (c * D.R.k) * σ ^ (4 * (c * D.R.k))) :=
          mul_le_mul_of_nonneg_left e (by positivity)
      _ = _ := by ring
  · simp

theorem rows_c3B_nonneg (D : D7) (large₂ : SizeData₂ D) (w : D.what₂.Word) {c : ℝ} (hc : 0 ≤ c) (Z' Z'' : GramM D) (s : ℕ) {De : ℝ}
    (hDe : 0 ≤ De) : 0 ≤ wordSublatticeTripleBound D large₂ w c Z' Z'' s De := by
  unfold wordSublatticeTripleBound
  have h1 := rows_one_le_HHZ D large₂ hc Z'
  have h2 := rows_one_le_HHZ D large₂ hc Z''
  have hN := rows_NT_pos D w
  have hX := rows_XiS_nonneg D w (HH := HHZ D large₂.sc.b c Z' * HHZ D large₂.sc.b c Z'') (by nlinarith) hc s
  have h3 : 0 ≤ HHZ D large₂.sc.b c Z' * HHZ D large₂.sc.b c Z'' := by nlinarith
  positivity

end Lab

end Formalism.MainNotions.BridgeLemma₂

end
end
