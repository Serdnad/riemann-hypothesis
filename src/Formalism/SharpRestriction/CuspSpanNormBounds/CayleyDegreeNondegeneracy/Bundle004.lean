module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDef
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfGluingFacts
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsTrm
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle003
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ShortVectorEveryPlace
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenusOrthonormalIntegralUnimodular
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rows_q_bound {m k r c cf a2 : ℝ} (hm : m = 2 * r + 2) (hr : 0 ≤ r) (hk : m + 3 ≤ k) (hc : 0 ≤ c) (hcf : cf ≤ m)
    (ha2 : a2 ≤ k) :
    (r + 1) * (4 * (c * k) + 4 * (c * (k + m) * m + c * cf) + 4 * (c * r ^ 2) + a2 / 2 + 12 * (r + 1) ^ 2) + 1 ≤
      (9 * c + 3) * k * m ^ 2 := by
  subst hm
  have hs0 : 0 ≤ r + 1 := by linarith
  have hs1 : 1 ≤ r + 1 := by linarith
  have hk2 : 2 * (r + 1) ≤ k := by linarith
  have hk5 : 5 ≤ k := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hck : 0 ≤ c * k := mul_nonneg hc hk0
  have P1 : c * cf * (r + 1) ≤ c * (2 * r + 2) * (r + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcf hc) hs0
  have P2 : a2 * (r + 1) ≤ k * (r + 1) := mul_le_mul_of_nonneg_right ha2 hs0
  have P3 : c * r ^ 2 * (r + 1) ≤ c * (r + 1) ^ 2 * (r + 1) := by
    have : r ^ 2 ≤ (r + 1) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hc) hs0
  have hss : r + 1 ≤ (r + 1) ^ 2 := by nlinarith
  have Q1 : c * k * (r + 1) ≤ c * k * (r + 1) ^ 2 := mul_le_mul_of_nonneg_left hss hck
  have Q2 : c * (r + 1) ^ 2 * (2 * (r + 1)) ≤ c * (r + 1) ^ 2 * k :=
    mul_le_mul_of_nonneg_left hk2 (by positivity)
  have Q3 : c * (r + 1) ^ 2 * 5 ≤ c * (r + 1) ^ 2 * k :=
    mul_le_mul_of_nonneg_left hk5 (by positivity)
  have Q4 : k * (r + 1) ≤ k * (r + 1) ^ 2 := mul_le_mul_of_nonneg_left hss hk0
  have Q5 : (r + 1) ^ 2 * (2 * (r + 1)) ≤ (r + 1) ^ 2 * k :=
    mul_le_mul_of_nonneg_left hk2 (by positivity)
  have Q6 : (r + 1) ^ 2 * 5 ≤ (r + 1) ^ 2 * k := mul_le_mul_of_nonneg_left hk5 (by positivity)
  have Q7 : 1 ≤ (r + 1) ^ 2 := by nlinarith
  nlinarith [P1, P2, P3, Q1, Q2, Q3, Q4, Q5, Q6, Q7, mul_nonneg hc hs0]

section Mono

variable {D : D7} {large₂ : SizeData₂ D} {X : TermTie D} {u u' : D.what₂.Word} {C1 : ℝ} (Y : LoopTie D large₂ X u u' C1)

theorem rows_one_le_HHZ' (D : D7) (large₂ : SizeData₂ D) (c : ℝ) (Z : GramM D) : 1 ≤ HHZ D large₂.sc.b c Z := by
  have hb : 1 ≤ large₂.sc.b := by
    have h := exp_one_le_b_rpow large₂ (le_refl (1 : ℝ))
    rw [Real.rpow_one] at h
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsz : 1 ≤ Cnt.sizeZ D large₂.sc.b c Z := by
    have key : ∀ {ι : Type} (s : Finset ι) (g : ι → ℝ), (∀ i ∈ s, 1 ≤ g i) → 1 ≤ ∏ i ∈ s, g i :=
      fun s g h => by simpa using Finset.prod_le_prod₀ (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) h
    unfold Cnt.sizeZ
    exact key _ _ (fun τ _ => key _ _ (fun l _ => le_max_left _ _))
  unfold Cnt.HHZ
  rw [← Real.rpow_mul (by linarith)]
  refine one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hb ?_) (one_le_pow₀ hsz)
  have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have : c * (D.R.m : ℝ) ^ 2 * D.R.f * (c * D.R.m) = c ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f := by ring
  rw [this]
  positivity

theorem rows_HHZ_mono (large₂ : SizeData₂ D) (hrd : 0 < D.host.rdE) {c' c : ℝ} (h1 : c' ≤ c) (h2 : 2 ≤ c + c') (Z : GramM D) :
    HHZ D large₂.sc.b c' Z ≤ HHZ D large₂.sc.b c Z := by
  have hb : 1 ≤ large₂.sc.b := by
    have h := exp_one_le_b_rpow large₂ (le_refl (1 : ℝ))
    rw [Real.rpow_one] at h
    linarith [Real.add_one_le_exp (1 : ℝ)]
  refine (rows_HHZ_cmp hrd hb c' c Z).trans ?_
  unfold Cnt.HHZ
  rw [← Real.rpow_mul (by linarith)]
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hb ?_) (by positivity)
  rw [max_eq_left (by linarith)]
  have hm : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by
    exact_mod_cast Formalism.MainNotions.BridgeLemma.d_m_eq (D := D)
  rw [hm]
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have key : 0 ≤ (2 * (D.R.rS : ℝ) + 2) ^ 2 * D.R.f * (c - c') * (2 * (D.R.rS : ℝ) + 2) * (c + c' - 2) := by
    have a1 : 0 ≤ c - c' := by linarith
    have a2 : 0 ≤ c + c' - 2 := by linarith
    positivity
  have e : c * (2 * (D.R.rS : ℝ) + 2) ^ 2 * D.R.f * (c * (2 * (D.R.rS : ℝ) + 2)) -
      (c' ^ 2 * (2 * (D.R.rS : ℝ) + 2) ^ 3 * D.R.f +
        4 * ((c - c') * (2 * (D.R.rS : ℝ) + 2) ^ 2 * D.R.f * ((D.R.rS : ℝ) + 1))) =
      (2 * (D.R.rS : ℝ) + 2) ^ 2 * D.R.f * (c - c') * (2 * (D.R.rS : ℝ) + 2) * (c + c' - 2) := by ring
  linarith

theorem rows_stHH_mono {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : c' ≤ c) (h2 : 2 ≤ c + c')
    (h : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c') : UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c := by
  intro hH F0 he hz Λ hΛ F' hT hR
  obtain ⟨a1, a2, a3, Z, hZ, hm⟩ := h hH F0 he hz Λ hΛ F' hT hR
  have mono := rows_HHZ_mono large₂ (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D) h1 h2 (ZhatL (lf D F0) F')
  exact ⟨a1.trans mono, a2.trans mono, a3.trans mono, Z, hZ,
    fun j I J hd => ⟨(hm j I J hd).1.trans mono, (hm j I J hd).2.trans mono⟩⟩

theorem rows_stVol_mono {C' Cl Cg cb Cu cT CT C0 A c' c : ℝ} (h1 : c' ≤ c) (h2 : 2 ≤ c + c')
    (h : VanishingOnXAndXPlus.TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A c') :
    VanishingOnXAndXPlus.TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A c := by
  unfold VanishingOnXAndXPlus.TermVolumeSmallCellBound UnitaryVolumeMass.stVol at h ⊢
  intro hH t ht hr
  refine (h hH t ht hr).trans ?_
  have mono := rows_HHZ_mono large₂ (Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D) h1 h2 (ZhatL (X.fl t) (X.fl' t))
  have o1 := rows_one_le_HHZ' D large₂ c' (ZhatL (X.fl t) (X.fl' t))
  have o2 := rows_one_le_HHZ' D large₂ c (ZhatL (X.fl t) (X.fl' t))
  have hr2 : (0 : ℝ) ≤ (D.R.rS : ℝ) ^ 2 := by positivity
  rcases le_total 0 c' with hc' | hc'
  · calc _ ≤ HHZ D large₂.sc.b c (ZhatL (X.fl t) (X.fl' t)) ^ (c' * (D.R.rS : ℝ) ^ 2) :=
          Real.rpow_le_rpow (by linarith) mono (mul_nonneg hc' hr2)
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le o2 (mul_le_mul_of_nonneg_right h1 hr2)
  · calc _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos o1 (mul_nonpos_of_nonpos_of_nonneg hc' hr2)
      _ ≤ _ := Real.one_le_rpow o2 (mul_nonneg (by linarith) hr2)


include Y in
theorem rows_dim_pos {C' Cl Cg cb Cu cT CT C0 : ℝ} (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (hF : UnitaryVolumeMass.FormAt D u) :
    0 < dimPi (hc := D.hcW) u := by
  obtain ⟨-, hD, hC0⟩ := hH
  obtain ⟨-, -, -, -, -, -, -, -, -, hdu, -⟩ := hD
  have hlow := (hdu u).1
  have hG : 0 < (D.mem u).A.GamP ^ (-2 : ℤ) := zpow_pos (lt_trans zero_lt_one (D.mem u).A.one_lt_gammaP) _
  have hpos : 0 < (D.duS u : ℝ) :=
    lt_of_lt_of_le (div_pos (mul_pos hG (d_Dstar_pos (D := D))) (by linarith)) hlow
  have hform := hF Y.F0 Y.flag_e_eq_hyperbolic Y.formsAtZero Y.what₂ Y.isRows
  have hnn : 0 ≤ dimPi (hc := D.hcW) u := by
    unfold dimPi
    exact Finset.prod_nonneg fun τ _ => Nat.cast_nonneg _
  rcases hnn.lt_or_eq with h | h
  · exact h
  · rw [← h, mul_zero] at hform
    rw [← hform] at hpos
    exact absurd hpos (lt_irrefl 0)

end Mono

section Fam

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

def rows_TiesF : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    TermPtsTie (X x hx i) (Y x hx i u u') ∧ @LatticeDeterminantFactorization (Fm.D x i) (X x hx i) u u' ∧ wordPairEntriesInLattice (X x hx i) u u'

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence.LatticeLiftIndependence

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tr

variable (D : D7)

theorem gmap_inf_cayley_degree_nondegeneracy {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (g : V ≃ₗ[D.host.E] V) (A B : Submodule (𝓞 D.host.E) V) :
    gmap g (A ⊓ B) = gmap g A ⊓ gmap g B := by
  ext x
  simp only [isomAct_mem_gmap, Submodule.mem_inf]

theorem gmap_sup_cayley_degree_nondegeneracy {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (g : V ≃ₗ[D.host.E] V) (A B : Submodule (𝓞 D.host.E) V) :
    gmap g (A ⊔ B) = gmap g A ⊔ gmap g B := Submodule.map_sup _ _ _

variable {D}

theorem isLattice_gmap_of_flag_isometry {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hσ : σ ∈ isom (VS D).hT) (hX : ∀ x ∈ F0.X, σ.symm x = x) (hz : σ.symm F0.z = F0.z) (Λ : LatV D)
    (hΛ : IsRowLat D F0 Λ) :
    IsRowLat D F0 (gmap σ Λ) ∧ Lsub (gmap σ Λ) (lf D F0) = gmap σ (Lsub Λ (lf D F0)) := by
  have hσ' : ∀ x y, (VS D).hT (σ x) (σ y) = (VS D).hT x y := hσ
  have hgX : gmap σ (toO (hS D) F0.X) = toO (hS D) F0.X := by
    ext x
    rw [isomAct_mem_gmap]
    constructor
    · intro h
      have h' : σ.symm x ∈ F0.X := h
      have := hX _ h'
      have e : σ.symm x = x := by
        apply σ.symm.injective
        exact this
      rw [e] at h
      exact h
    · intro h
      have h' : x ∈ F0.X := h
      rw [hX x h']
      exact h
  have hgO : gmap σ (toO (hS D) (orth (hS D) F0.X)) = toO (hS D) (orth (hS D) F0.X) := by
    ext y
    rw [isomAct_mem_gmap]
    change σ.symm y ∈ orth (hS D) F0.X ↔ y ∈ orth (hS D) F0.X
    rw [Formalism.MainNotions.mem_orth_iff, Formalism.MainNotions.mem_orth_iff]
    refine forall₂_congr fun x hx => ?_
    rw [← hσ' x (σ.symm y), LinearEquiv.apply_symm_apply]
    have : σ x = x := by
      rw [← LinearEquiv.eq_symm_apply, hX x hx]
    rw [this]
  have hXLam : XLam (gmap σ Λ) (lf D F0) = XLam Λ (lf D F0) := by
    have h1 : XLam (gmap σ Λ) (lf D F0) = gmap σ (XLam Λ (lf D F0)) := by
      unfold XLam
      rw [gmap_inf_cayley_degree_nondegeneracy]
      change gmap σ Λ ⊓ toO (hS D) F0.X = gmap σ Λ ⊓ gmap σ (toO (hS D) F0.X)
      rw [hgX]
    rw [h1]
    ext x
    rw [isomAct_mem_gmap]
    constructor
    · intro h
      have h' : σ.symm x ∈ F0.X := h.2
      have e : σ.symm x = x := σ.symm.injective (hX _ h')
      rw [e] at h
      exact h
    · intro h
      have h' : x ∈ F0.X := h.2
      rw [hX x h']
      exact h
  have hLsub : Lsub (gmap σ Λ) (lf D F0) = gmap σ (Lsub Λ (lf D F0)) := by
    unfold Lsub Lrep
    rw [gmap_inf_cayley_degree_nondegeneracy, gmap_sup_cayley_degree_nondegeneracy, gmap_inf_cayley_degree_nondegeneracy]
    change (gmap σ Λ ⊓ toO (hS D) (orth (hS D) F0.X) ⊔ toO (hS D) F0.X) ⊓ toO (hS D) (orth (hS D) F0.X) =
      (gmap σ Λ ⊓ gmap σ (toO (hS D) (orth (hS D) F0.X)) ⊔ gmap σ (toO (hS D) F0.X)) ⊓
        gmap σ (toO (hS D) (orth (hS D) F0.X))
    rw [hgX, hgO]
  refine ⟨?_, hLsub⟩
  obtain ⟨⟨hlat1, hgen1⟩, ⟨hL, hU, hLift, hConv⟩, hXS⟩ := hΛ
  obtain ⟨_, hloc, _, huni, _⟩ := isomAct (𝓞 D.host.E) D.host.E (VS D).V (VS D).hT σ hσ Λ
  have hfull : Submodule.IsFullLattice D.host.E (gmap σ Λ) := by
    refine { toIsLattice := isomAct_lattice σ Λ hlat1.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E ((σ : (VS D).V →ₗ[D.host.E] (VS D).V) '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, hlat1.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact σ.surjective
  refine ⟨⟨hfull, fun p hp => ?_⟩,
    ⟨isomAct_lattice σ Λ hL, huni.2 hU, ⟨?_, hLift.2⟩, ?_, fun c hc => hConv.2 c ?_⟩, hXLam.trans hXS⟩
  · obtain ⟨g, hg, e⟩ := hgen1 p hp
    exact ⟨σ * g, (isom (VS D).hT).mul_mem hσ hg, by rw [gmap_mul, e, hloc p]⟩
  · rw [isomAct_mem_gmap]
    change σ.symm F0.z ∈ Λ
    rw [hz]
    exact hLift.1
  · rw [hXLam]
    exact hConv.1
  · rw [hLsub, isomAct_mem_gmap, map_smul] at hc
    change c • σ.symm F0.z ∈ _ at hc
    rw [hz] at hc
    exact hc

variable (D)

theorem isometries_transport_lattices (u : D.what₂.Word) : IsometriesTransportLattices D u := by
  intro _ _ _ F0 he hz γ hγ Λ₁ hΛ₁
  have hzO : F0.z ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
    rw [Formalism.MainNotions.mem_orth_iff]
    rintro _ ⟨w, rfl⟩
    rw [hz]
    exact Formalism.MainNotions.hT_swap_zero (z_orth_embedding D u w)
  have hXO : F0.X ≤ orth (hS D) (LinearMap.range (D.sp.iXY 0)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    rw [he]
    change D.sp.hypE a ∈ orth (hS D) (LinearMap.range (D.sp.iXY 0))
    rw [Formalism.MainNotions.mem_orth_iff]
    rintro _ ⟨w, rfl⟩
    exact (D.sp.hyp_orthX a w).1
  obtain ⟨hrow, hLsub⟩ := isLattice_gmap_of_flag_isometry F0 (extendByIdentity D γ) (extendByIdentity_mem_isom D γ hγ)
    (fun x hx => extendByIdentity_symm_fix_orth D γ x (hXO hx)) (extendByIdentity_symm_fix_orth D γ _ hzO) Λ₁ hΛ₁
  refine ⟨gmap (extendByIdentity D γ) Λ₁, hrow, ?_⟩
  ext ⟨w, c⟩
  unfold latticeWithZ
  rw [Submodule.mem_comap, hLsub, isomAct_mem_gmap, isomAct_mem_gmap, Submodule.mem_comap]
  have e1 : ((embedWithZ D F0).restrictScalars (𝓞 D.host.E)) (w, c) = D.sp.iXY 0 w + c • F0.z := by
    simp [embedWithZ]
  have e2 : ((embedWithZ D F0).restrictScalars (𝓞 D.host.E)) ((extendByOne D γ).symm (w, c)) =
      D.sp.iXY 0 (γ.symm w) + c • F0.z := by
    have : (extendByOne D γ).symm (w, c) = (γ.symm w, c) := rfl
    rw [this]
    simp [embedWithZ]
  rw [e1, e2, extendByIdentity_symm_apply D γ w _ (Submodule.smul_mem _ c hzO)]

theorem gluing_mass_of_iso_aut_count_genus (u : D.what₂.Word) (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (h1 : LatticeClassesIff D u) (h2 : CardAutEqCardIsometryStabilizer D u) (h4 : GluingCount D u)
    (h5 : OrthLatticesOneGenus D u) : WordRowsGluing D u :=
  gluing_mass_of_gluing_facts D u hpos hlat h1 h2 (isometries_transport_lattices D u) h4 h5

end Tr

end Formalism.MainNotions.BridgeLemma₂

end
end

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.HermitianLatticesTheory

def SecondOrthogonalVector (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → IsIntegralLat h M → dual h M = M →
    ∀ x ∈ M, x ≠ 0 → ∃ y ∈ M, y ≠ 0 ∧ h x y = 0 ∧ ∀ φ : K →+* ℂ, ‖φ (h y y)‖ ≤ ‖φ (h x x)‖ * rootDiscriminant K

def PlaneClassCount (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ s : Finset (Submodule (𝓞 K) V), Formalism.ThetaLiftIndependence.IsClassReps h L s → ∀ B₁ B₂ : ℝ,
    (∀ M ∈ s, IsIntegralLat h M) →
    (∀ M ∈ s, ∃ x ∈ M, ∃ y ∈ M, x ≠ 0 ∧ y ≠ 0 ∧ h x y = 0 ∧
      ∀ φ : K →+* ℂ, ‖φ (h x x)‖ ≤ B₁ ∧ ‖φ (h y y)‖ ≤ B₂) →
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * B₂) ^ (2 * finrank ℚ K) *
      (B₁ * B₂) ^ (4 * finrank ℚ K)

theorem card_class_reps_plane_le (K : Type) [Field K] [NumberField K] [StarRing K] (B₁ : ℝ)
    (hA : ShortVectorEveryPlace K B₁) (hB : SecondOrthogonalVector K) (hC : PlaneClassCount K) (hrd : 0 ≤ rootDiscriminant K)
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hs : h.IsSymm) (hL : IsOrthoLattice h L 2)
    (s : Finset (Submodule (𝓞 K) V)) (hreps : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * (B₁ * rootDiscriminant K)) ^ (2 * finrank ℚ K) *
      (B₁ * (B₁ * rootDiscriminant K)) ^ (4 * finrank ℚ K) := by
  refine hC V h L hs hL s hreps B₁ (B₁ * rootDiscriminant K)
    (fun M hM => (genus_orthonormal_integral_unimodular h hs L hL M (hreps.1 M hM)).1) fun M hM => ?_
  have hg := hreps.1 M hM
  have hMlat : Submodule.IsLattice K M := hg.1.toIsLattice
  obtain ⟨hint, huni⟩ := genus_orthonormal_integral_unimodular h hs L hL M hg
  obtain ⟨x, hx, hx0, hxB⟩ := hA V h L hs hL M hg
  obtain ⟨y, hy, hy0, hxy, hyB⟩ := hB V h L hs hL M hMlat hint huni x hx hx0
  exact ⟨x, hx, y, hy, hx0, hy0, hxy, fun φ =>
    ⟨hxB φ, (hyB φ).trans (mul_le_mul_of_nonneg_right (hxB φ) hrd)⟩⟩

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem plane_mass_bound_of_facts (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C B₁ : ℝ)
    (hA : ShortVectorEveryPlace D.host.E B₁) (hB : SecondOrthogonalVector D.host.E) (hCt : PlaneClassCount D.host.E)
    (hB0 : 0 ≤ B₁) (hB1 : B₁ ≤ 4 * D.R.f * D.host.rdE) (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : UnitaryVolumeMass.Mass2At D large₂ C := by
  intro V _ _ _ _ h L hs ho
  obtain ⟨-, -, h3, -, h5, -, -, -, -, -, h11, -, -, -, -, -, -, -, h19, -⟩ := hH
  have hm := D.R.two_le_m
  have hf : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) h3
  have hL1 : 1 ≤ large₂.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hrd : 2 ≤ D.host.rdE := by
    have e : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [← e]; linarith
  have hlrd : Real.log D.host.rdE ≤ max 1 (1 / Cl) * large₂.sc.L := by
    refine le_trans h11 ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  have hlf : Real.log (D.R.f : ℝ) ≤ (D.R.m : ℝ) := by
    refine le_trans h5 ?_
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : D.R.rS ≤ D.R.m := by unfold Ranks.rS; omega
    have h2 : (D.R.rS : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast h1
    have h3 : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hrdE : rootDiscriminant D.host.E = D.host.rdE := rfl
  have hnum := mass_pow_le_exp_rpow D.R.f D.R.m D.host.rdE large₂.sc.L B₁ C (max 1 (1 / Cl)) hf hm hrd hL1 (le_max_left _ _) hlf hlrd hB0 hB1 hC
  have hb : large₂.sc.b = Real.exp large₂.sc.L := rfl
  rw [hb]
  refine mass_le_of_card_class_reps_le h L _ (by positivity) fun s hreps => ?_
  have hc := card_class_reps_plane_le D.host.E B₁ hA hB hCt (by rw [hrdE]; linarith) V h L hs ho s hreps
  rw [hrdE, Formalism.MainNotions.StandardLattice.finrank_host] at hc
  exact hc.trans hnum

end Formalism.MainNotions.BridgeLemma₂

end
end
