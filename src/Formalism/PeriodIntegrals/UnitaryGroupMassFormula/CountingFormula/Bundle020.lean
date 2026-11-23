module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.HTIntLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle009
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CommonMult
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle010
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle018
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle003
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodularSpan

@[expose] public section

section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem trace_one_unramified : TraceOne := fun D =>
  Formalism.MainNotions.BridgeLemma.l_theta D.host.E D.sp.cm.cmUnram

section Dual

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem exists_dual0 : ∃ g0 : Fin D.R.rS → (VS D).V, IsDual0 F0 g0 := by
  let Φ : (VS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) := LinearMap.pi (fun a => (VS D).hT (F0.e a))
  have hsurj : LinearMap.range Φ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    set μ : Fin D.R.rS → D.host.E := fun a => f (fun j => if a = j then 1 else 0) with hμdef
    have hv : ∀ v, ∑ a, (VS D).hT (F0.e a) v * μ a = 0 := by
      intro v
      have h1 : f (Φ v) = 0 := hle (LinearMap.mem_range_self Φ v)
      rw [LinearMap.pi_apply_eq_sum_univ f (Φ v)] at h1
      simpa [Φ, LinearMap.pi_apply, smul_eq_mul, μ] using h1
    have hx : ∑ a, star (μ a) • F0.e a = 0 := by
      apply (VS D).nondeg.1
      intro v

      rw [map_sum, LinearMap.sum_apply]
      simp only [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
      rw [← hv v]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    have hμ : ∀ a, μ a = 0 := by
      intro a
      have := Fintype.linearIndependent_iff.1 F0.e_indep (fun a => star (μ a)) hx a
      simpa using this
    apply hf0
    apply LinearMap.ext
    intro u
    rw [LinearMap.pi_apply_eq_sum_univ f u]
    simp only [LinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro a _
    have : f (fun j => if a = j then 1 else 0) = 0 := hμ a
    rw [this, smul_zero]
  refine ⟨fun b => Classical.choose (LinearMap.range_eq_top.1 hsurj (Pi.single b 1)), ?_⟩
  intro a b
  have h := Classical.choose_spec (LinearMap.range_eq_top.1 hsurj (Pi.single b 1))
  have h2 := congrFun h a
  simp only [Φ, LinearMap.pi_apply] at h2
  rw [h2, Pi.single_apply]

end Dual

theorem row_dual_frame : RowDualFrame := by
  intro D u F0 Λ hΛ
  obtain ⟨g0, hg0⟩ := exists_dual0 F0
  have hlat : Submodule.IsLattice D.host.E Λ := hΛ.2.1.1
  have hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hiso : ∀ x ∈ F0.X, ∀ y ∈ F0.X, (VS D).hT x y = 0 := fun x hx y hy => hX_X F0 hx hy
  obtain ⟨P, P', hadj, hid, hX, _, hint', _⟩ :=
    Formalism.MainNotions.BridgeLemma.l_iso Formalism.MainNotions.BridgeLemma.l_adj Formalism.MainNotions.BridgeLemma.l_retr Formalism.MainNotions.BridgeLemma.l_theta
      D.host.E (VS D) Λ F0.X D.sp.cm.cmUnram hlat hu hiso

  have hker : ∀ w ∈ perpS (VS D) F0.X, P' w = 0 := by
    intro w hw
    apply (VS D).nondeg.2
    intro x
    rw [← hadj x w]
    exact hw _ (hX x)
  refine ⟨fun b => P' (g0 b), ?_, ?_⟩
  · intro a b
    show (VS D).hT (F0.e a) (P' (g0 b)) = _
    rw [← hadj, hid _ (e_mem_X F0 a), hg0 a b]
  · intro v hv
    have hg0' : ∀ a b, (VS D).hT (F0.e a) (g0 b) = if a = b then 1 else 0 := hg0
    have hyc : ycL F0 (fun b => P' (g0 b)) v = P' (ycL F0 g0 v) := by

      rw [ycL_apply, ycL_apply, map_sum]
      exact Finset.sum_congr rfl (fun b _ => by rw [map_smul])
    have hperp : v - ycL F0 g0 v ∈ perpS (VS D) F0.X := by
      apply mem_perp_of F0
      intro a

      rw [map_sub, ycL_apply, map_sum]
      simp [hg0']
    have h1 : P' (ycL F0 g0 v) = P' v := by
      have := hker _ hperp
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    rw [hyc, h1]
    exact hint' v hv

theorem rowClass_of_zunit (h : RowZUnit) : RowClass :=
  rowClass_of_three row_dual_frame h trace_one_unramified

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem stage1_span_eq_top_of_unimodular (D : Formalism.BasicNotions.D7) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hL : Λ.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    Submodule.span D.host.E (Λ : Set (VS D).V) = ⊤ := by
  exact Formalism.HermitianLatticesTheory.IsUnimodular.span_eq_top hU (VS D).herm hL


theorem inW_neg (D : Formalism.BasicNotions.D7) {x : (VS D).V} (hx : InW D x) : InW D (-x) := by
  simpa using inW_smul D (-1) hx

theorem stage1_of_unipotentIntegralIsGroup (hN : UnipotentIntegralIsGroup) : Stage1 := by
  intro D T T' F0 Λ hF Z R hR
  have hF' := hF
  obtain ⟨hlat, hU, he, heΛ0, c0, hc0, hz⟩ := hF
  have heΛ : ∀ a, D.sp.hypE a ∈ Λ := fun a => by rw [← he]; exact heΛ0 a
  let : Submodule.IsLattice D.host.E Λ := hlat
  have hfull : Submodule.IsFullLattice D.host.E Λ :=
    ⟨stage1_span_eq_top_of_unimodular D hlat.fg hU⟩
  obtain ⟨d, hd0, hdv, hdk⟩ := common_mult D hfull
    (Finset.univ.image D.sp.hypF ∪ {((D.sp.T : D.host.E)⁻¹) • D.sp.zm})
    (Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2) ∪
      Finset.univ.image (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => Pm D Z R p.1 p.2))
  have hdF : ∀ a, (d : D.host.E) • D.sp.hypF a ∈ Λ := fun a =>
    hdv _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ a)))
  have hdz : ((d : D.host.E) * (D.sp.T : D.host.E)⁻¹) • D.sp.zm ∈ Λ := by
    rw [← smul_smul]; exact hdv _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have hdR : ∀ b a, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (d : D.host.E) * R b a := fun b a =>
    hdk _ (Finset.mem_union_left _ (Finset.mem_image_of_mem (fun p : Fin (D.R.rS + 1) × Fin D.R.rS => R p.1 p.2)
      (Finset.mem_univ (b, a))))
  have hdP : ∀ b' b, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (d : D.host.E) * Pm D Z R b' b :=
    fun b' b => hdk _ (Finset.mem_union_right _ (Finset.mem_image_of_mem
      (fun p : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) => Pm D Z R p.1 p.2) (Finset.mem_univ (b', b))))
  have hd2 : ∀ v ∈ Λ, (d : D.host.E) ^ 2 • pW D v ∈ Λ := fun v hv => pW_lat D hU heΛ d hdF hdz hv
  have hdE : (d : D.host.E) ≠ 0 := Int.cast_ne_zero.2 hd0
  have hd3 : (d : D.host.E) ^ 3 ≠ 0 := pow_ne_zero 3 hdE
  have hΛfg : (Λ.restrictScalars ℤ).FG := Submodule.FG.restrictScalars hlat.fg

  let Sb : Fin (D.R.rS + 1) → Set (VS D).V := fun b =>
    {w | w ∈ Λ.restrictScalars ℤ ∧ (∀ a, (VS D).hT (D.sp.hypE a) w = 0) ∧ (∀ a, (VS D).hT (D.sp.hypF a) w = 0) ∧
      (VS D).hT D.sp.zm w = 0 ∧ (VS D).hT w w = (d : D.host.E) ^ 6 * kap D T' Z R c0 b}
  have hSb : ∀ b, (Sb b).Finite := fun b => definite_finite D _ hΛfg _
  let Tset : Fin (D.R.rS + 1) → Set (VS D).V := fun b => (fun w => (((d : D.host.E) ^ 3)⁻¹) • w) '' Sb b

  have hLWfg : ((LamW D Λ).restrictScalars ℤ).FG := Submodule.FG.of_le hΛfg (fun y hy => hy.1)
  obtain ⟨Rs, hRs, hred⟩ := gen_red _ hLWfg (2 * d ^ 3) (mul_ne_zero two_ne_zero (pow_ne_zero 3 hd0))
  refine ⟨(fun p : (Fin (D.R.rS + 1) → (VS D).V) × (Fin D.R.rS → (VS D).V) =>
      fun b => p.1 b + (((d : D.host.E) ^ 3)⁻¹) • ∑ a, betaZ D Z a b • p.2 a) ''
      (Set.pi Set.univ Tset ×ˢ Set.pi Set.univ (fun _ => Rs)), ?_, ?_⟩
  · exact ((Set.Finite.pi (fun b => (hSb b).image _)).prod (Set.Finite.pi (fun _ => hRs))).image _
  intro x hx
  have hbeta : ∀ (a : Fin D.R.rS) b, (VS D).hT (D.sp.hypE a) (fr D x b) = betaZ D Z a b := by
    intro a b
    have := hx.2.1 (Fin.castSucc a) b
    simpa [brS, FlagG.fvec, he, betaZ] using this

  have hw2 : ∀ b, (d : D.host.E) ^ 2 • pWf D x b ∈ LamW D Λ := fun b =>
    ⟨hd2 _ (hx.1 b), inW_smul D _ (inW_pW D _)⟩
  have hu : ∀ a, (d : D.host.E) ^ 3 • (∑ b, R b a • pWf D x b) ∈ (LamW D Λ).restrictScalars ℤ := by
    intro a
    have : (d : D.host.E) ^ 3 • (∑ b, R b a • pWf D x b) =
        ∑ b, ((d : D.host.E) * R b a) • ((d : D.host.E) ^ 2 • pWf D x b) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [smul_smul, smul_smul]; ring_nf
    rw [Submodule.restrictScalars_mem, this]
    refine Submodule.sum_mem _ fun b _ => ?_
    obtain ⟨o, ho⟩ := hdR b a
    rw [← ho, algebraMap_smul]
    exact (LamW D Λ).smul_mem o (hw2 b)
  choose q hq ρ hρ hqρ using fun a => hred _ (hu a)
  obtain ⟨n, hn, hpW⟩ := eich_all hN D F0 Λ hF' (fun a => -q a) (fun a => inW_neg D (hq a).2)
    (fun a => Λ.neg_mem (hq a).1)
  refine ⟨n, hn, ⟨(tv D Z R x, ρ), ⟨fun b _ => ?_, fun a _ => hρ a⟩, ?_⟩⟩
  ·
    refine ⟨(d : D.host.E) ^ 3 • tv D Z R x b, ⟨?_, ?_, ?_, ?_, ?_⟩, inv_smul_smul₀ hd3 _⟩
    · rw [Submodule.restrictScalars_mem]
      have : (d : D.host.E) ^ 3 • tv D Z R x b =
          ∑ b', ((d : D.host.E) * Pm D Z R b' b) • ((d : D.host.E) ^ 2 • pWf D x b') := by
        rw [tv, Finset.smul_sum]
        exact Finset.sum_congr rfl fun b' _ => by rw [smul_smul, smul_smul]; ring_nf
      rw [this]
      refine Submodule.sum_mem _ fun b' _ => smul_int_mem D (hdP b' b) (hw2 b').1
    all_goals have hW : InW D ((d : D.host.E) ^ 3 • tv D Z R x b) :=
      inW_smul D _ (inW_sum D _ _ fun b' => inW_smul D _ (inW_pW D _))
    · exact hW.1
    · exact hW.2.1
    · exact hW.2.2
    · simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply,
        star_pow, star_intCast]
      rw [tv_norm D T' F0 Λ Z R hR he hc0 hz hx b]
      ring
  ·
    funext b
    have h2q : ∀ a, (2 : D.host.E) • q a = (∑ b', R b' a • pWf D x b') - (((d : D.host.E) ^ 3)⁻¹) • ρ a := by
      intro a
      have e1 := hqρ a
      rw [← Int.cast_smul_eq_zsmul D.host.E] at e1
      have e2 : ((2 * d ^ 3 : ℤ) : D.host.E) • q a = (d : D.host.E) ^ 3 • (∑ b', R b' a • pWf D x b') - ρ a := by
        rw [e1]; abel
      have e3 : (2 : D.host.E) • q a = (((d : D.host.E) ^ 3)⁻¹) • (((2 * d ^ 3 : ℤ) : D.host.E) • q a) := by
        rw [smul_smul]; congr 1; push_cast; field_simp
      rw [e3, e2, smul_sub, inv_smul_smul₀ hd3]
    symm
    show pW D (fr D (act D n x) b) = tv D Z R x b + (((d : D.host.E) ^ 3)⁻¹) • ∑ a, betaZ D Z a b • ρ a
    rw [fr_act, hpW]
    have e4 : ∀ a, (VS D).hT (D.sp.hypE a) (fr D x b) • ((2 : D.host.E) • -q a) =
        -(betaZ D Z a b • (∑ b', R b' a • pWf D x b')) + (((d : D.host.E) ^ 3)⁻¹) • (betaZ D Z a b • ρ a) := by
      intro a
      rw [hbeta, smul_neg, h2q, smul_neg, smul_sub, smul_comm (betaZ D Z a b) (((d : D.host.E) ^ 3)⁻¹) (ρ a)]
      abel
    rw [Finset.sum_congr rfl fun a _ => e4 a, Finset.sum_add_distrib, ← Finset.smul_sum]
    simp only [tv, Pm, Matrix.sub_apply, Matrix.one_apply, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mul_apply, Finset.sum_smul,
      Finset.sum_neg_distrib, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm (f := fun a b' => (betaZ D Z a b * R b' a) • pWf D x b')]
    have e5 : ∀ b' a, (betaZ D Z a b * R b' a) • pWf D x b' = (R b' a * betaZ D Z a b) • pWf D x b' :=
      fun b' a => by rw [mul_comm]
    simp only [e5]
    show pW D (fr D x b) + _ = _
    have e6 : pWf D x b = pW D (fr D x b) := rfl
    rw [← e6]
    abel

end PI.UnitaryGroupMassFormula.CntFormula
end
end

section

open NumberField Module IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Dedekind

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem count_span_unit (v : HeightOneSpectrum R) (s : R) (hs : s ∉ v.asIdeal) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K s)) = 0 := by
  have hs0 : s ≠ 0 := fun h => hs (h ▸ v.asIdeal.zero_mem)
  have hsp : Ideal.span {s} ≠ ⊥ := by simpa using hs0
  rw [← FractionalIdeal.coeIdeal_span_singleton, count_coe_eq_multiplicity v hsp]
  have : multiplicity v.asIdeal (Ideal.span {s}) = 0 := by
    apply multiplicity_eq_zero_of_not_dvd
    rwa [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  simp [this]

theorem count_le_of_mem (v : HeightOneSpectrum R) {I : FractionalIdeal (nonZeroDivisors R) K} {y : K}
    (hy : y ∈ I) (hy0 : y ≠ 0) :
    FractionalIdeal.count K v I ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ y) :=
  FractionalIdeal.count_mono K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy0)
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr hy)

theorem exists_exact_ideal (v : HeightOneSpectrum R) (T : Finset R) (hT : T.Nonempty) (h0 : ∀ g ∈ T, g ≠ 0) :
    ∃ g ∈ T, multiplicity v.asIdeal (Ideal.span {g}) = multiplicity v.asIdeal (Ideal.span (T : Set R)) := by
  classical
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, Finset.mem_singleton_self a, by simp⟩
  | cons a T ha hT ih =>
    have hT0 : ∀ g ∈ T, g ≠ 0 := fun g hg => h0 g (Finset.mem_cons_of_mem hg)
    obtain ⟨g, hg, hgm⟩ := ih hT0
    have ha0 : Ideal.span {a} ≠ ⊥ := by simpa using h0 a (Finset.mem_cons_self a T)
    have hT' : Ideal.span (T : Set R) ≠ ⊥ := by
      intro hb
      have : g ∈ Ideal.span (T : Set R) := Ideal.subset_span hg
      rw [hb, Ideal.mem_bot] at this
      exact hT0 g hg this
    have hspan : Ideal.span ((Finset.cons a T ha : Finset R) : Set R) = Ideal.span {a} ⊔ Ideal.span (T : Set R) := by
      rw [Finset.coe_cons, Ideal.span_insert]
    rw [hspan, HeightOneSpectrum.multiplicity_sup v ha0 hT']
    rcases le_total (multiplicity v.asIdeal (Ideal.span {a})) (multiplicity v.asIdeal (Ideal.span (T : Set R))) with h | h
    · exact ⟨a, Finset.mem_cons_self a T, (min_eq_left h).symm⟩
    · exact ⟨g, Finset.mem_cons_of_mem hg, by rw [min_eq_right h, hgm]⟩

theorem exists_exact (v : HeightOneSpectrum R) {I : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) :
    ∃ y ∈ I, y ≠ 0 ∧
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors R) y) = FractionalIdeal.count K v I := by
  classical
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    apply hI
    rw [hIJ, FractionalIdeal.coeIdeal_bot, mul_zero]
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian J : J.FG)
  set T' := T.filter (· ≠ 0)
  have hT' : Ideal.span (T' : Set R) = J := by
    rw [← hT]
    apply le_antisymm
    · exact Ideal.span_mono (by intro z hz; exact (Finset.mem_filter.mp hz).1)
    · rw [Ideal.span_le]
      intro z hz
      by_cases hz0 : z = 0
      · rw [hz0]; exact Ideal.zero_mem _
      · exact Ideal.subset_span (Finset.mem_filter.mpr ⟨hz, hz0⟩)
  have hne : T'.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hJ0
    rw [← hT', hemp, Finset.coe_empty, Ideal.span_empty]
  obtain ⟨g, hgT, hgm⟩ := exists_exact_ideal v T' hne (fun g hg => (Finset.mem_filter.mp hg).2)
  have hg0 : g ≠ 0 := (Finset.mem_filter.mp hgT).2
  have hgJ : g ∈ J := hT' ▸ Ideal.subset_span hgT
  have ha' : algebraMap R K a ≠ 0 := (IsFractionRing.injective R K).ne_iff.mpr ha |>.trans_eq (map_zero _) |> fun h => by
    simpa using (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr ha
  have hg' : algebraMap R K g ≠ 0 := (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hg0
  refine ⟨(algebraMap R K a)⁻¹ * algebraMap R K g, ?_, mul_ne_zero (inv_ne_zero ha') hg', ?_⟩
  · rw [hIJ]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hgJ)
  · have hsa : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a)⁻¹ ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero ha')
    have hsg : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K g) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hg'
    have hJc : (J : FractionalIdeal (nonZeroDivisors R) K) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have hsp : Ideal.span {g} ≠ ⊥ := by simpa using hg0
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K v hsa hsg, hIJ,
      FractionalIdeal.count_mul K v hsa hJc, ← FractionalIdeal.coeIdeal_span_singleton,
      count_coe_eq_multiplicity v hsp, count_coe_eq_multiplicity v hJ0, hgm, hT']

theorem prod_mem_prod' {ι : Type*} (s : Finset ι) (𝔞 : ι → FractionalIdeal (nonZeroDivisors R) K)
    (m : ι → K) (hm : ∀ i, m i ∈ 𝔞 i) : ∏ i ∈ s, m i ∈ ∏ i ∈ s, 𝔞 i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact FractionalIdeal.mul_mem_mul (hm j) ih

theorem det_mem_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔞 : ι → FractionalIdeal (nonZeroDivisors R) K)
    (M : Matrix ι ι K) (hM : ∀ i k, M i k ∈ 𝔞 i) : M.det ∈ ∏ i, 𝔞 i := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hp : ∏ i, M (σ i) i ∈ ∏ i, 𝔞 i := by
    have : ∏ i, M (σ i) i = ∏ j, M j (σ.symm j) := by
      rw [← Equiv.prod_comp σ (fun j => M j (σ.symm j))]
      simp
    rw [this]
    exact prod_mem_prod' _ 𝔞 _ fun j => hM j _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul]; exact Submodule.neg_mem _ hp

end Dedekind

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end
