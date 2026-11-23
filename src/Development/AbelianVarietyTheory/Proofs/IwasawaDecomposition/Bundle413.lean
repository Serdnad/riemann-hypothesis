module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle383
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle065
public import Formalism.SharpRestriction.Divisibility.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle010
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle027
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle018
import Formalism.DoubleCosetMeasures.Statement
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Polynomial

noncomputable section

namespace GlobalTheory.TeichAt

open Formalism.L2.NT GlobalTheory.ParRay

theorem orderOf_coprime {g : ℕ} [hg : Fact g.Prime] {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) : (orderOf x).Coprime g := by
  have hpos := (isOfFinOrder_fbar hx).orderOf_pos
  set n := orderOf x with hn
  refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hg.out).2 ?_))
  intro hdvd
  have hm : g ^ n.factorization g * (n / g ^ n.factorization g) = n := Nat.ordProj_mul_ordCompl_eq_self n g
  have h1 : x ^ (g ^ n.factorization g * (n / g ^ n.factorization g)) = 1 := by rw [hm, hn, pow_orderOf_eq_one]
  have h2 : x ^ (n / g ^ n.factorization g) = 1 := pow_eq_one_of_charP g x _ _ h1
  have h3 : n ∣ n / g ^ n.factorization g := orderOf_dvd_of_pow_eq_one h2
  exact Nat.not_dvd_ordCompl hg.out hpos.ne' (hdvd.trans h3)

theorem map_zero_of_inj {Ω : Type} [Field Ω] {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* Ω)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  have h : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
  by_contra h0
  have h1 : t 0 = 1 := (mul_eq_left₀ h0).1 h
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  apply hx.2
  refine ht x 1 hx.1 one_ne_zero ?_
  have : t x = t x * t 0 := by rw [h1, mul_one]
  rw [this, ← map_mul, mul_zero, h1, map_one]

theorem exists_teich_reindex : ∀ (g : ℕ) [Fact g.Prime] (A : ValuationSubring ℂ)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ),
    (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ t₀ : Formalism.CyclotomicNorms.Fbar g →* ℂ,
      Formalism.L2.NT.IsTeich A κ t₀ ∧ ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t₀ x = t₀ y → x = y := by
  intro g _ A κ t ht
  set s := redHom A κ t with hs_def
  have hs : ∀ x, s x = redThrough A κ (t x) := fun x => rfl
  have ht0 : t 0 = 0 := map_zero_of_inj t ht
  have hs0 : s 0 = 0 := by
    rw [hs, ht0]; unfold redThrough; rw [dite_eq_left (zero_mem A)]
    have : (⟨0, zero_mem A⟩ : A) = 0 := rfl
    rw [this, map_zero, map_zero]
  have hsne : ∀ x, x ≠ 0 → s x ≠ 0 := by
    intro x hx h0
    have hpos := (isOfFinOrder_fbar hx).orderOf_pos
    have : s x ^ orderOf x = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [h0, zero_pow hpos.ne'] at this
    exact zero_ne_one this
  have hinj : Function.Injective s := by
    intro x y h
    rcases eq_or_ne x 0 with rfl | hx
    · rcases eq_or_ne y 0 with rfl | hy
      · rfl
      · exact absurd (h.symm.trans hs0) (hsne y hy)
    · rcases eq_or_ne y 0 with rfl | hy
      · exact absurd (h.trans hs0) (hsne x hx)
      · exact redHom_inj A κ t ht x y hx hy (orderOf_coprime hx) (orderOf_coprime hy) h
  have hsurj : Function.Surjective s := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, hs0⟩
    have hn := (isOfFinOrder_fbar hy).orderOf_pos
    set n := orderOf y
    have hmem : ∀ z : Formalism.CyclotomicNorms.Fbar g, z ∈ nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g) ↔ z ^ n = 1 :=
      fun z => mem_nthRootsFinset hn 1
    obtain ⟨a, -, ha⟩ := Finset.surj_on_of_inj_on_of_card_le (s := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g))
      (t := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g)) (fun a _ => s a)
      (fun a ha => (hmem _).2 (by rw [← map_pow, (hmem a).1 ha, map_one]))
      (fun a₁ a₂ _ _ h => hinj h) le_rfl y ((hmem y).2 (pow_orderOf_eq_one y))
    exact ⟨a, ha.symm⟩
  let e : Formalism.CyclotomicNorms.Fbar g ≃* Formalism.CyclotomicNorms.Fbar g := MulEquiv.ofBijective s ⟨hinj, hsurj⟩
  have he : ∀ x, e x = s x := fun x => rfl
  refine ⟨t.comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro x
    refine ⟨mem_of_monoidHom A t _, ?_⟩
    have h1 : s (e.symm x) = x := by rw [← he, MulEquiv.apply_symm_apply]
    have h2 := hs (e.symm x)
    unfold redThrough at h2
    rw [dite_eq_left (mem_of_monoidHom A t _)] at h2
    exact h2.symm.trans h1
  · intro x y hx hy h
    have hx' : e.symm x ≠ 0 := fun h0 => hx (by rw [← e.apply_symm_apply x, h0, he, hs0])
    have hy' : e.symm y ≠ 0 := fun h0 => hy (by rw [← e.apply_symm_apply y, h0, he, hs0])
    exact e.symm.injective (ht _ _ hx' hy' h)

end GlobalTheory.TeichAt

end
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.PlaceOverPair

theorem exists_mem_pvSet {R : Ranks} (H : Formalism.BasicNotions.Host R) {p : ℕ} (hp : p.Prime) (𝔭 : HeightOneSpectrum (𝓞 H.K))
    (h𝔭 : (p : 𝓞 H.K) ∈ 𝔭.asIdeal) (v : HeightOneSpectrum (𝓞 H.F)) (hv : OverPF H p v) : ∃ w, w ∈ PvSet H 𝔭 v := by
  obtain ⟨w, h1, h2⟩ := exists_over_both H hp 𝔭 h𝔭 v hv
  refine ⟨w, ?_, h2⟩
  rw [aboveF, Set.Finite.mem_toFinset]
  exact h1

end GlobalTheory.PlaceOverPair
end

section

open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.Mem

theorem card_GL_eq_pow_mul_qE (k : Type) [Field k] [Fintype k] (r : ℕ) :
    (Nat.card (GL (Fin r) k) : ℝ)
      = (Fintype.card k : ℝ) ^ (r * r) * Formalism.MainNotions.ZetaProductPairs.qE (Fintype.card k : ℝ) 1 r := by
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hq0 : (Fintype.card k : ℝ) ≠ 0 := by
    have : 0 < Fintype.card k := by omega
    exact_mod_cast this.ne'
  have hconst : (Fintype.card k : ℝ) ^ (r * r)
      = ∏ _j ∈ Finset.Icc 1 r, (Fintype.card k : ℝ) ^ r := by
    rw [Finset.prod_const, Nat.card_Icc, Nat.add_sub_cancel, ← pow_mul]
  rw [Matrix.card_GL_field, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range
      (fun i => ((Fintype.card k ^ r - Fintype.card k ^ i : ℕ) : ℝ)) r,
    hconst, Formalism.MainNotions.ZetaProductPairs.qE, ← Finset.prod_mul_distrib]
  refine Finset.prod_nbij' (fun i => r - i) (fun j => r - j) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr (by omega)
  · intro j hj
    have := Finset.mem_Icc.mp hj
    exact Finset.mem_range.mpr (by omega)
  · intro i hi
    have := Finset.mem_range.mp hi
    show r - (r - i) = i
    omega
  · intro j hj
    have := Finset.mem_Icc.mp hj
    show r - (r - j) = j
    omega
  · intro i hi
    have hir : i < r := Finset.mem_range.mp hi
    have hle : Fintype.card k ^ i ≤ Fintype.card k ^ r :=
      Nat.pow_le_pow_right (by omega) hir.le
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one]
    congr 1
    have hcast : (-((r - i : ℕ) : ℤ)) = (i : ℤ) - (r : ℤ) := by
      rw [Nat.cast_sub hir.le]; ring
    rw [hcast, zpow_sub₀ hq0, zpow_natCast, zpow_natCast]
    field_simp

end GlobalTheory.Mem
end

section

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.BlockTransporter

theorem exists_unitary_mul_upper {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ t : Matrix (Fin n) (Fin n) ℂ, t.BlockTriangular id ∧ y = u * t := by
  first
  | exact @_root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular
  | exact _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular
  | (apply _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitaryUpperTriangular.exists_unitary_mul_upperTriangular ..)

theorem exists_unitary_block {r p : ℕ} (B : Matrix (Fin r) (Fin r) ℂ) (hB : B.det ≠ 0)
    (h0 : ∀ a c : Fin r, (c : ℕ) < p → ¬ (a : ℕ) < p → B a c = 0) :
    ∃ u t : Matrix (Fin r) (Fin r) ℂ, u ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
      (∀ a c : Fin r, (c : ℕ) < p → ¬ (a : ℕ) < p → u a c = 0) ∧
      t.det ≠ 0 ∧ (∀ a c : Fin r, c < a → t a c = 0) ∧ B = u * t := by
  obtain ⟨u, hu, t, ht, e⟩ := exists_unitary_mul_upper B
  have hud : u.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 hu)
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have htd : t.det ≠ 0 := by
    intro h; rw [e, det_mul, h, mul_zero] at hB; exact hB rfl
  letI := invertibleOfIsUnitDet t htd.isUnit
  have hti : (t⁻¹).BlockTriangular id := blockTriangular_inv_of_blockTriangular ht
  have hu' : u = B * t⁻¹ := by rw [e, Matrix.mul_nonsing_inv_cancel_right _ _ htd.isUnit]
  refine ⟨u, t, hu, fun a c hc ha => ?_, htd, fun a c h => ht h, e⟩
  rw [hu', Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ≤ c
  · rw [h0 a k (lt_of_le_of_lt (Fin.le_def.1 hk) hc) ha, zero_mul]
  · rw [hti (not_le.1 hk), mul_zero]

end GlobalTheory.BlockTransporter

namespace GlobalTheory.BlockTransporter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def unitBlock (X : Data E r) : Set (Frame X.Ψ r) :=
  {u | ∀ τ, mat u τ ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
    ∀ a c : Fin r, (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0}

theorem isCompact_unitBlock (X : Data E r) : IsCompact (unitBlock X) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have : unitBlock X = ⋂ τ, ({u : Frame X.Ψ r | star (mat u τ) * mat u τ = 1} ∩
        ⋂ a : Fin r, ⋂ c : Fin r, {u | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0}) := by
      ext u
      simp only [unitBlock, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
      simp only [Matrix.mem_unitaryGroup_iff']
    rw [this]
    refine isClosed_iInter fun τ => IsClosed.inter ?_ (isClosed_iInter fun a => isClosed_iInter fun c => ?_)
    · have hc : Continuous fun u : Frame X.Ψ r => mat u τ := continuous_apply τ
      exact isClosed_eq (hc.star.matrix_mul hc) continuous_const
    · by_cases h : (c : ℕ) < X.p0 ∧ ¬ (a : ℕ) < X.p0
      · have : {u : Frame X.Ψ r | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0} = {u | u τ a c = 0} := by
          ext u; simp only [Set.mem_setOf_eq]; exact ⟨fun hu => hu h.1 h.2, fun hu _ _ => hu⟩
        rw [this]
        exact isClosed_eq ((continuous_apply c).comp ((continuous_apply a).comp (continuous_apply τ)))
          continuous_const
      · have : {u : Frame X.Ψ r | (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u τ a c = 0} = Set.univ := by
          ext u; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; intro h1 h2; exact absurd ⟨h1, h2⟩ h
        rw [this]; exact isClosed_univ
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun u hu => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun τ => ?_
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun a => ?_
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.2 fun c => ?_
    exact entry_norm_bound_of_unitary (hu τ).1 a c

theorem continuous_rmul (X : Data E r) : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2 := by
  refine continuous_pi fun τ => ?_
  have h1 : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => mat p.1 τ := (continuous_apply τ).comp continuous_fst
  have h2 : Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => mat p.2 τ := (continuous_apply τ).comp continuous_snd
  exact h1.matrix_mul h2

end GlobalTheory.BlockTransporter

namespace GlobalTheory.BlockTransporter

theorem finite_blockTransporter : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (K : Set (ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r)), IsCompact K → K ⊆ X.dom →
    {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ x ∈ K, ∃ y ∈ K, ∃ b : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r,
      (∀ τ, (ReciprocityTheory.ChartRestriction.G.FD.mat b τ).det ≠ 0) ∧
      (∀ τ (a c : Fin r), (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → b τ a c = 0) ∧
      ReciprocityTheory.ChartRestriction.G.FD.lact γ x = ReciprocityTheory.ChartRestriction.G.FD.rmul y b}.Finite := by
  intro E _ _ _ r X K hK hKd
  set K' := (fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2) '' (K ×ˢ unitBlock X) with hK'
  have hK'c : IsCompact K' := (hK.prod (isCompact_unitBlock X)).image (continuous_rmul X)
  have hK'd : K' ⊆ X.dom := by
    rintro _ ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩
    refine GlobalTheory.PointOfFrames.rmul_mem_dom X (hKd hy) u (fun τ h => ?_) (fun τ => (hu τ).2)
    have := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 (hu τ).1)
    rw [det_mul, h, mul_zero, det_one] at this
    exact zero_ne_one this
  have hfin := GlobalTheory.PropDiscCompare.compact_of_local X (GlobalTheory.propDisc_of_flagDomainData E r X) (K ∪ K')
    (hK.union hK'c) (Set.union_subset hKd hK'd)
  refine hfin.subset ?_
  rintro γ ⟨hγ, x, hx, y, hy, b, hb, h0, e⟩
  have key : ∀ τ : X.Ψ, ∃ u t : Matrix (Fin r) (Fin r) ℂ, u ∈ Matrix.unitaryGroup (Fin r) ℂ ∧
      (∀ a c : Fin r, (c : ℕ) < X.p0 → ¬ (a : ℕ) < X.p0 → u a c = 0) ∧
      t.det ≠ 0 ∧ (∀ a c : Fin r, c < a → t a c = 0) ∧ mat b τ = u * t :=
    fun τ => exists_unitary_block (mat b τ) (hb τ) (h0 τ)
  choose u t hu hu0 htd ht hbut using key
  refine ⟨hγ, x, Or.inl hx, rmul y (fun τ => u τ), Or.inr ⟨(y, fun τ => u τ), ⟨hy, fun τ => ⟨hu τ, hu0 τ⟩⟩, rfl⟩,
    fun τ => t τ, fun τ => ⟨htd τ, ht τ⟩, ?_⟩
  rw [e]
  funext τ
  show mat y τ * mat b τ = (mat y τ * u τ) * t τ
  rw [Matrix.mul_assoc, ← hbut τ]

end GlobalTheory.BlockTransporter
end
