module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle121
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.RootOfRealisationTelescoping
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AmpleHeightBounds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle141
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle155
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle041
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle160
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle083
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle007
public import Development.WeilBound.CoreStatements.AmpleLineBundles.ExistsPointsOverNumberFields
public import Development.WeilBound.CoreStatements.AmpleLineBundles.IntersectionNumberEqLineHeight
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle156
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle012
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011

@[expose] public section

section

noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hermLine_eq_of_a_h {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {A B : HermLine ι}
    (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  simp_all

theorem exists_tensorPow_last {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hI : IsIntersectionFamily I)
    {W : Ideal (MRing ι)} {n : ℕ} {L : Fin n → HermLine ι} (hW : IsArithVar W (n + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) {B : HermLine ι} (hB : IsSmoothHerm B) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : HermLine ι, IsSmoothHerm C ∧ (∀ k, C.a k = m * B.a k) ∧ (∀ z, C.h z = B.h z ^ m) ∧
      I W (n + 1) (Fin.snoc L C) = m * I W (n + 1) (Fin.snoc L B) := by
  induction m, hm using Nat.le_induction with
  | base => exact ⟨B, hB, by simp, by simp, by simp⟩
  | succ m hm ih =>
    obtain ⟨C, hC, ha, hh, hi⟩ := ih
    refine ⟨C.tensor B, ContDiffOn.mul hC hB, fun k => ?_, fun z => ?_, ?_⟩
    · simp only [HermLine.tensor, Pi.add_apply, ha]
      push_cast
      ring
    · simp only [HermLine.tensor, hh, pow_succ]
    · rw [hI.2.1 W n L C B hW hL hC hB, hi]
      push_cast
      ring

theorem IsUnitSec.mono {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    {f g : MRing ι} (h : IsUnitSec P f g) (hPW : P ≤ W) : IsUnitSec W f g := by
  intro W' h1 h2 h3
  obtain ⟨a, b, ha, hb, hab⟩ := h W' h1 (hPW.trans h2) h3
  exact ⟨a, b, ha, hb, hPW hab⟩

theorem FlatHerm.inter_eq_neg_integral : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type)
    [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω)
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ) (u : ((Σ k, ι k) → ℂ) → ℝ),
    IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W →
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsPlaceWeight y φ (fun σ => Real.log (S.κ σ)) u →
    I W (n + 1) (Fin.snoc L A) = -ptsIntegral W (pot L) u := by
  intro K _ ι _ Ω _ F _ _ y φ I W n L A S d u hI hP hY hPW hW hL hA hu
  have hnu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → (fun z => -u z) (fun p => c p.1 * z p) = (fun z => -u z) z :=
    fun c z hc => by simp only [hu.inv c z hc]

  set B : HermLine ι := A.tensor (HermLine.ofWeight (fun z => -u z) hnu) with hBdef
  have hBh : ∀ z, B.h z = A.h z * Real.exp (u z) := fun z => by
    simp [hBdef, HermLine.tensor, HermLine.ofWeight]
  have hBa : ∀ k, B.a k = A.a k := fun k => by
    simp [hBdef, HermLine.tensor, HermLine.ofWeight]
  have hexp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.exp (u z)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    Real.contDiff_exp.comp_contDiffOn hu.smooth
  have hB : IsSmoothHerm B := by
    have e : B.h = fun z => A.h z * Real.exp (u z) := funext hBh
    unfold IsSmoothHerm
    rw [e]
    exact ContDiffOn.mul hA hexp
  have hBA : B.tensor (HermLine.ofWeight u hu.inv) = A := by
    refine hermLine_eq_of_a_h ?_ ?_
    · funext k
      simp [HermLine.tensor, HermLine.ofWeight, hBa]
    · funext z
      have : (B.tensor (HermLine.ofWeight u hu.inv)).h z = B.h z * Real.exp (-u z) := rfl
      rw [this, hBh, mul_assoc, ← Real.exp_add]
      simp
  have hchange : I W (n + 1) (Fin.snoc L A) = I W (n + 1) (Fin.snoc L B) - ptsIntegral W (pot L) u := by
    have := metricChange K ι I hI W n L B u hu.inv hW hL hB hu.smooth
    rwa [hBA] at this

  obtain ⟨C, hC, hCa, hCh, hCI⟩ := exists_tensorPow_last hI hW hL hB (m := S.M) S.M_pos
  obtain ⟨f', g', df', dg', hf', hg', hdeg, hfW, hgW, -, hun, hnorm⟩ :=
    GlobalTheory.T.flat_herm_unit_section_avoid K ι Ω F y φ A S d W hY hP hA hW.2.1 hPW
  have hunW := IsUnitSec.mono hun hPW
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.T.unit_section_divisor_eq K ι W f' g' hunW
  have hvert := GlobalTheory.T.vertical_statement_holds K ι I hI W n L C f' g' hW hL hC
    ⟨df', dg', hf', hg', hfW, hgW, fun k => by rw [hdeg k, hCa k, hBa k]⟩
    (fun W' _ => by rw [c1]) (fun W' _ hm => c2 W' hm) (fun z hz => by
      have hzP : z ∈ mcPts (mCoordIdeal y) := ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
      obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.complex_point_existsUnique_embedding K ι Ω F y φ hY z hzP
      have hz1 : u z = Real.log (S.κ σ) := (hu.near σ z hσ).self_of_nhds
      have hn := hnorm σ z hσ
      have hCz : C.h z = (S.κ σ * A.h z) ^ S.M := by
        rw [hCh, hBh, hz1, Real.exp_log (S.κ_pos σ), mul_comm]
      rw [hCz, mul_comm]
      exact hn)
  have hzero : I W (n + 1) (Fin.snoc L B) = 0 := by
    have h0 : (S.M : ℝ) * I W (n + 1) (Fin.snoc L B) = 0 := by
      rw [← hCI, hvert, c3 n L, sub_self]
    have hM : (S.M : ℝ) ≠ 0 := by exact_mod_cast S.M_pos.ne'
    exact (mul_eq_zero.mp h0).resolve_left hM
  rw [hchange, hzero, zero_sub]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LinesDeg

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem block_chart {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {c : (k : K) → J k} {p : Cpt ξ}
    (h : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) :
    InChart ξ (fun i : J k => y ⟨k, i⟩) (c k) p := by
  classical
  obtain ⟨h0, hr⟩ := h
  have hne : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.mp h0) k (Finset.mem_univ k)
  refine ⟨hne k, fun j => ?_⟩
  have hreg := hr (Function.update c k j)
  have e : (∏ k', y ⟨k', Function.update c k j k'⟩) / ∏ k', y ⟨k', c k'⟩ = y ⟨k, j⟩ / y ⟨k, c k⟩ := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', Function.update c k j k'⟩) (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c k'⟩) (Finset.mem_univ k)]
    have hrest : ∏ k' ∈ Finset.univ.erase k, y ⟨k', Function.update c k j k'⟩ =
        ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ :=
      Finset.prod_congr rfl fun k' hk' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk')]
    have hP : ∏ k' ∈ Finset.univ.erase k, y ⟨k', c k'⟩ ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k' _ => hne k'
    simp only [hrest, Function.update_self]
    exact mul_div_mul_right _ _ hP
  rw [← e]
  exact hreg

theorem segre_chart {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {c : (k : K) → J k} {p : Cpt ξ}
    (h : ∀ k, InChart ξ (fun i : J k => y ⟨k, i⟩) (c k) p) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p := by
  refine ⟨Finset.prod_ne_zero_iff.mpr fun k _ => (h k).1, fun c' => ?_⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ regAt ξ p
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => (h k).2 (c' k)

theorem exists_chart_of_gen {Q : Type} {t : Q → Ω} {d : Ω} (hd : d ≠ 0) {L : Lat ξ Ω} {p : Cpt ξ}
    (hm : ∀ i, t i / d ∈ L p) (hg : ∃ i, L.IsGenAt p (t i / d)) : ∃ i, InChart ξ t i p := by
  obtain ⟨i, hi0, hi⟩ := hg
  have ht : t i ≠ 0 := fun h => hi0 (by simp [h])
  refine ⟨i, ht, fun j => ?_⟩
  have hj := hm j
  rw [hi, Submodule.mem_span_singleton] at hj
  obtain ⟨r, hr⟩ := hj
  rw [Subring.smul_def, smul_eq_mul] at hr
  have : t j / t i = r := by
    field_simp at hr ⊢
    exact hr.symm
  rw [this]
  exact r.2

theorem isGen_of_chart {Q : Type} {t : Q → Ω} {d : Ω} (hd : d ≠ 0) {L : Lat ξ Ω} {p : Cpt ξ} {i₀ : Q}
    (hc : InChart ξ t i₀ p) (hm : ∀ i, t i / d ∈ L p) (hg : ∃ i, L.IsGenAt p (t i / d)) :
    L p = Submodule.span (regAt ξ p) {t i₀ / d} := by
  obtain ⟨i, -, hi⟩ := hg
  refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr (hm i₀))
  rw [hi, Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  refine ⟨⟨t i / t i₀, hc.2 i⟩, ?_⟩
  rw [Subring.smul_def, smul_eq_mul]
  have := hc.1
  show t i / t i₀ * (t i₀ / d) = t i / d
  field_simp

abbrev joinJ {K I : Type} (J : K → Type) (J₂ : I → Type) : K ⊕ I → Type := Sum.elim J J₂

def joinY {K I : Type} {J : K → Type} {J₂ : I → Type} (y : (Σ k, J k) → Ω) (s : (Σ i, J₂ i) → Ω) :
    (Σ k, joinJ J J₂ k) → Ω
  | ⟨Sum.inl k, j⟩ => y ⟨k, j⟩
  | ⟨Sum.inr i, j⟩ => s ⟨i, j⟩

def joinFintype {K I : Type} {J : K → Type} {J₂ : I → Type} [∀ k, Fintype (J k)] [∀ i, Fintype (J₂ i)] :
    ∀ k, Fintype (joinJ J J₂ k)
  | Sum.inl k => inferInstanceAs (Fintype (J k))
  | Sum.inr i => inferInstanceAs (Fintype (J₂ i))

end GlobalTheory.CompanionTheory.Ar.LinesDeg

namespace GlobalTheory.CompanionTheory.Ar


open LinesDeg in
theorem exists_addBlocks_isDegOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ i, (Λ i).IsVB 1 ⊤) → ∃ (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k)) (y' : (Σ k, J' k) → Ω) (κ : K → K') (v : ∀ k, J k ≃ J' (κ k)), Function.Injective κ ∧ (∀ k i, y' ⟨κ k, v k i⟩ = y ⟨k, i⟩) ∧ CoordTie ℤ ξ (fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) ∧ ∀ i, ∃ (a : K' → ℤ) (e₀ : Ω), (Λ i).IsDegOn Set.univ y' a e₀ := by
  intro X Ω _ ξ K _ J _ y I _ Λ ht hvb
  classical
  have key := fun i => GlobalTheory.T.line_bundle_global_generators X Ω ξ ((k : K) → J k) (fun c' => ∏ k, y ⟨k, c' k⟩) (Λ i) ht (hvb i)
  choose n m s hmem hgen using key
  let J₂ : I → Type := fun i => Fin (m i + 1)
  let s₂ : (Σ i, J₂ i) → Ω := fun q => s q.1 q.2
  have hbpf : ∀ (i : I) (p : Cpt ξ), ∃ j, InChart ξ (fun j' : J₂ i => s₂ ⟨i, j'⟩) j p := by
    intro i p
    obtain ⟨c, hc⟩ := ht.cover p
    exact exists_chart_of_gen (t := s i) (pow_ne_zero _ hc.1) (hmem i p c hc) (hgen i p c hc)
  have hadd := GlobalTheory.T.coords_join_blocks X Ω ξ K J y I J₂ s₂ ht hbpf
  refine ⟨K ⊕ I, inferInstance, joinJ J J₂, joinFintype, joinY y s₂, Sum.inl, fun k => Equiv.refl _,
    Sum.inl_injective, fun k i => rfl, ?_, fun i => ?_⟩
  · have e : (fun c' : (k : K ⊕ I) → joinJ J J₂ k => ∏ k, joinY y s₂ ⟨k, c' k⟩) =
        fun c' : (k : K ⊕ I) → Sum.elim J J₂ k =>
          (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, s₂ ⟨k, c' (Sum.inr k)⟩ :=
      funext fun c' => Fintype.prod_sum_type (fun k => joinY y s₂ ⟨k, c' k⟩)
    rw [e]
    exact hadd
  · refine ⟨Sum.elim (fun _ => -(n i : ℤ)) (fun i' => if i' = i then 1 else 0), 1, one_ne_zero, ?_⟩
    intro p _ c hc
    have hb := block_chart hc
    let c₀ : (k : K) → J k := fun k => c (Sum.inl k)
    have hx : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c₀ p :=
      segre_chart fun k => hb (Sum.inl k)
    have hs : InChart ξ (s i) (c (Sum.inr i)) p := hb (Sum.inr i)
    have hP : ∏ k, y ⟨k, c₀ k⟩ ≠ 0 := hx.1
    have hgen' := isGen_of_chart (t := s i) (pow_ne_zero (n i) hP) hs (hmem i p c₀ hx) (hgen i p c₀ hx)
    have hprod : (∏ k : K ⊕ I, joinY y s₂ ⟨k, c k⟩ ^
        (Sum.elim (fun _ => -(n i : ℤ)) (fun i' => if i' = i then 1 else 0) k : ℤ)) • (1 : Ω) =
        s i (c (Sum.inr i)) / (∏ k, y ⟨k, c₀ k⟩) ^ n i := by
      rw [Fintype.prod_sum_type, smul_eq_mul, _root_.mul_one]
      have h1 : ∏ k : K, joinY y s₂ ⟨Sum.inl k, c (Sum.inl k)⟩ ^
          (Sum.elim (fun _ => -(n i : ℤ)) (fun i' => if i' = i then (1 : ℤ) else 0) (Sum.inl k : K ⊕ I) : ℤ) =
          ((∏ k, y ⟨k, c₀ k⟩) ^ n i)⁻¹ := by
        simp only [Sum.elim_inl]
        rw [Finset.prod_zpow, zpow_neg, zpow_natCast]
        rfl
      have h2 : ∏ i' : I, joinY y s₂ ⟨Sum.inr i', c (Sum.inr i')⟩ ^
          (Sum.elim (fun _ => -(n i : ℤ)) (fun i' => if i' = i then (1 : ℤ) else 0) (Sum.inr i' : K ⊕ I) : ℤ) =
          s i (c (Sum.inr i)) := by
        rw [Fintype.prod_eq_single i]
        · simp only [Sum.elim_inr, if_true, zpow_one]
          rfl
        · intro i' hi'
          simp [hi']
      rw [h1, h2, div_eq_mul_inv, _root_.mul_comm]
    rw [hprod]
    exact hgen'

end GlobalTheory.CompanionTheory.Ar
end
end

section

open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_rootFlat_of_realis : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (S : GlobalTheory.CompanionTheory.Ar.PB.AnSys (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) (Option (Ψ × Fin N))) (Re : GlobalTheory.CompanionTheory.Ar.PB.Realis S M.P) (τ : Ψ) (i₀ : Fin N) (F : Type) [Field F] [NumberField F] (φ : F →+* M.Ω) (A : HermLine M.ι) (Sf : FlatHerm M.y φ A), OverInt M.y φ → IsSmoothHerm A → (i₀ : ℕ) + 1 = N → 0 < S.t₀ → A.a = ∑ i, M.xdeg (τ, i) → (∀ (σ : Ψ) (i : Fin N), M.xdeg (σ, i) + (Re.ref (some (σ, i))).a = if h : 0 < (i : ℕ) then (Re.ref (some (σ, ⟨i - 1, by omega⟩))).a else 0) → (∀ t, 0 < t → t ≤ S.t₀ → ∀ (σ : Ψ) (i : Fin N), ∀ z ∈ mcPts M.P, (M.x t (σ, i)).h z * (Re.line (some (σ, i)) t).h z = if h : 0 < (i : ℕ) then (Re.line (some (σ, ⟨i - 1, by omega⟩)) t).h z else 1) → (∀ x, Re.π x ∈ S.open' → -Real.log (A.h (Re.R.lift x x)) = Real.log ((Re.ref (some (τ, i₀))).h (Re.R.lift x x)) + S.ph (some (τ, i₀)) (Re.π x)) → ∃ R : RootFlat M τ, R.ht = Sf.ht :=
  PositivityTheory.Xgn.root_of_realisation_telescoping

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.ample_height_bounds : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ A : HermLine ι, IsSmoothHerm A → AmpleQ y A.a → (∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), -C ≤ lineHt A L w) ∧ ∀ B : HermLine ι, IsSmoothHerm B → ∃ n C : ℝ, 0 ≤ n ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt B L w| ≤ n * lineHt A L w + C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd.height_bound | exact GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd.height_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.AmpleBd.height_bound <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht.FlatLine

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hasVal_inv {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} (hu : u ≠ 0) {𝕜 : Type} [Field 𝕜]
    {z : (Σ k, ι k) → 𝕜} (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {val : 𝕜} (hv : val ≠ 0)
    (h : HasVal y a u z val) : HasVal y (-a) u⁻¹ z val⁻¹ := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, hfz, hgz⟩ := h
  have hfy : aeval y f ≠ 0 := fun h0 =>
    hfz (hz.2 f ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hf).2 h0))
  refine ⟨dh, dg, f, g, hf, hg, fun k => ?_, ?_, ?_, ?_⟩
  · have := hd k
    simp only [Pi.neg_apply]
    omega
  · rw [hy, inv_mul_cancel_left₀ hu]
  · rw [hgz]
    exact mul_ne_zero hv hfz
  · rw [hgz, inv_mul_cancel_left₀ hv]

theorem aeval_embed {L 𝕜 : Type} [Field L] [Field 𝕜] (σ : L →+* 𝕜) (z : (Σ k, ι k) → L) (f : MRing ι) :
    aeval (fun p => σ (z p)) f = σ (aeval z f) :=
  (MvPolynomial.comp_aeval_apply (R := ℤ) z σ.toIntAlgHom f).symm

theorem ptsOver_embed {L 𝕜 : Type} [Field L] [Field 𝕜] (σ : L →+* 𝕜) {P : Ideal (MRing ι)}
    {z : (Σ k, ι k) → L} (hz : z ∈ ptsOver L P) : (fun p => σ (z p)) ∈ ptsOver 𝕜 P := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, (map_ne_zero σ).2 hi⟩
  · rw [aeval_embed, hz.2 f hf, map_zero]

theorem hasVal_embed {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} {L 𝕜 : Type} [Field L] [Field 𝕜] (σ : L →+* 𝕜)
    {z : (Σ k, ι k) → L} {val : L} (h : HasVal y a u z val) : HasVal y a u (fun p => σ (z p)) (σ val) := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, hfz, hgz⟩ := h
  refine ⟨dg, dh, g, f, hg, hf, hd, hy, ?_, ?_⟩
  · rw [aeval_embed]
    exact (map_ne_zero σ).2 hfz
  · rw [aeval_embed, aeval_embed, hgz, map_mul]

theorem isSmoothHerm_powH {A : HermLine ι} (hA : IsSmoothHerm A) (k : ℕ) : IsSmoothHerm (powH A k) :=
  ContDiffOn.pow hA k

theorem ptHt_pow (A : HermLine ι) (k : ℕ) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) :
    ptHt (fun b => (((k : ℤ) * A.a b : ℤ) : ℝ)) (fun z => (k : ℝ) * Real.log (A.h z)) L w = k * lineHt A L w := by
  have e : ∀ v : FinitePlace L, ∑ b, (((k : ℤ) * A.a b : ℤ) : ℝ) * Real.log (⨆ i, v (w ⟨b, i⟩)) =
      (k : ℝ) • ∑ b, (A.a b : ℝ) * Real.log (⨆ i, v (w ⟨b, i⟩)) := fun v => by
    rw [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  simp only [ptHt, lineHt, e]
  rw [← smul_finsum, ← Finset.mul_sum, smul_eq_mul]
  ring

theorem exists_arch_bound {y : (Σ k, ι k) → Ω} {d : ℕ} (hAr : IsArithVar (mCoordIdeal y) d) (hB : Birational y)
    {A : HermLine ι} {k : ℕ} {u : Ω} {c : ℝ} (hS : IsSmoothHerm A)
    (hV : VertBound y (fun b => k * A.a b) u c) :
    ∃ C : ℝ, ∀ z ∈ ptsOver ℂ (mCoordIdeal y), ∀ val : ℂ, val ≠ 0 → HasVal y (fun b => k * A.a b) u z val →
      |(k : ℝ) * Real.log (A.h z) - Real.log ‖val‖| ≤ C := by
  obtain ⟨hu, q, m, hq, hm, -, h1, h2⟩ := hV
  have hP := isSmoothHerm_powH hS k
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.archimedean_value_bound K ι Ω y d hAr hB (powH A k) q m u hP hq hm h1
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.archimedean_value_bound K ι Ω y d hAr hB (powH A k).inv q m u⁻¹ (isSmoothHerm_inv hP) hq hm h2
  refine ⟨max C₁ C₂, fun z hz val hv hval => ?_⟩
  have hp : 0 < A.h z := A.pos z hz.1
  have hn : 0 < ‖val‖ := norm_pos_iff.2 hv
  have b₁ : ‖val‖ ≤ Real.exp C₁ * A.h z ^ k := hC₁ z hz val hval
  have b₂ : ‖val⁻¹‖ ≤ Real.exp C₂ * (A.h z ^ k)⁻¹ := hC₂ z hz val⁻¹ (hasVal_inv hu hz hv hval)
  have l₁ : Real.log ‖val‖ ≤ C₁ + k * Real.log (A.h z) := by
    have := Real.log_le_log hn b₁
    rwa [Real.log_mul (Real.exp_pos _).ne' (pow_pos hp k).ne', Real.log_exp, Real.log_pow] at this
  have l₂ : -Real.log ‖val‖ ≤ C₂ - k * Real.log (A.h z) := by
    have := Real.log_le_log (norm_pos_iff.2 (inv_ne_zero hv)) b₂
    rwa [norm_inv, Real.log_inv, Real.log_mul (Real.exp_pos _).ne' (inv_pos.2 (pow_pos hp k)).ne', Real.log_exp,
      Real.log_inv, Real.log_pow, ← sub_eq_add_neg] at this
  rw [abs_le]
  constructor
  · have := le_max_left C₁ C₂
    linarith
  · have := le_max_right C₁ C₂
    linarith

end GlobalTheory.CompanionTheory.Ar.Ht.FlatLine


open GlobalTheory.CompanionTheory.Ar.Ht.FlatLine in
theorem GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (A : HermLine ι) (k : ℕ) (u : Ω) (c : ℝ), IsSmoothHerm A → 0 < k → GenUnit y (fun b => k * A.a b) u → VertBound y (fun b => k * A.a b) u c → ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt A L w| ≤ C := by
  intro K _ ι _ Ω _ y d hAr hB A k u c hS hk hG hV
  obtain ⟨C, hC⟩ := exists_arch_bound hAr hB hS hV
  refine ⟨(c + C) / k, fun L _ _ w hw => ?_⟩
  obtain ⟨val, hv, hval⟩ := hG L w hw
  have hU := GlobalTheory.T.vertical_bound_height_compare K ι Ω y d hAr hB (fun b => k * A.a b) u c hV
    (fun z => (k : ℝ) * Real.log (A.h z)) L w hw val hv hval
  rw [ptHt_pow] at hU
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  set S := ∑ σ : L →+* ℂ, ((k : ℝ) * Real.log (A.h fun p => σ (w p)) - Real.log ‖σ val‖) with hSdef
  have hSb : |S| ≤ (Module.finrank ℚ L : ℝ) * C := by
    calc |S| ≤ ∑ σ : L →+* ℂ, |(k : ℝ) * Real.log (A.h fun p => σ (w p)) - Real.log ‖σ val‖| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : L →+* ℂ, C := Finset.sum_le_sum fun σ _ =>
          hC _ (ptsOver_embed σ hw) _ ((map_ne_zero σ).2 hv) (hasVal_embed σ hval)
      _ = (Module.finrank ℚ L : ℝ) * C := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NumberField.Embeddings.card]
  have hm : |(Module.finrank ℚ L : ℝ)⁻¹ * S| ≤ C := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hd), inv_mul_le_iff₀ hd]
    exact hSb
  have hT : |(k : ℝ) * lineHt A L w| ≤ c + C := by
    have := abs_sub_abs_le_abs_sub ((k : ℝ) * lineHt A L w) ((Module.finrank ℚ L : ℝ)⁻¹ * S)
    linarith
  rw [le_div_iff₀ hk']
  rwa [abs_mul, abs_of_pos hk', mul_comm] at hT
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

theorem _root_.GlobalTheory.T.line_height_invariant_scaling : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (L : Type) [Field L] [NumberField L] (L' : Type) [Field L'] [NumberField L'] (e : L →+* L') (w : (Σ k, ι k) → L) (c : K → L'), (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ k, c k ≠ 0) → lineHt A L' (fun p => c p.1 * e (w p)) = lineHt A L w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale | exact GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.lineHt_map_scale <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.CoverDense

theorem preimage_dense : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (Q : (L : Type) → [Field L] → ((Σ k, R.ι k) → L) → Prop), (∀ f : MRing R.ι, (∃ a, IsMultiHomog f a) → f ∉ R.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L R.P, aeval w f ≠ 0 ∧ Q L w) → ∀ f : MRing M.ι, (∃ a, IsMultiHomog f a) → f ∉ M.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (w : (Σ k, R.ι k) → L), ∃ z ∈ ptsOver L' (mCoordIdeal (joinOf M R i)), w ∈ ptsOver L R.P ∧ Q L w ∧ (fun p => z (joinInr M.ι R.ι p)) = (fun p => e (w p)) ∧ aeval (fun p => z (joinInl M.ι R.ι p)) f ≠ 0 :=
  CoverDenseAlt.exists_points_over_number_fields

end GlobalTheory.CompanionTheory.Ar.CoverDense
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht

theorem height_eq_intersection_number :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem), IsIntersectionSystem II → ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (w : (Σ k, ι k) → L), W = mCoordIdeal w ∧ w ∈ ptsOver L W ∧ ∀ A : HermLine ι, IsSmoothHerm A → II K ι W 1 ![A] / (degC W : ℝ) = lineHt A L w := by
  exact @CoverDenseAlt.intersection_number_eq_line_height

end GlobalTheory.CompanionTheory.Ar.Ht
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.abelian_part_lie_mult_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S) (P : AbPart t z), ∃ r : ℕ, ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k) (n : ℕ), LieMult P.tK.act (spMap g) τ n → r ≤ n ∧ LieMult P.tB.act (spMap g) τ (n - r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbMult.lieMult_abPart | exact GlobalTheory.CompanionTheory.Ar.AbMult.lieMult_abPart | (intros; apply GlobalTheory.CompanionTheory.Ar.AbMult.lieMult_abPart <;> assumption)
end
