module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle006
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle002
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle001
import GroundTheory.LocalFields.Uniqueness
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ElemPairJ
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem mem_diag (g : GL (Fin n) k) :
    g ∈ (diagT k (Fin n)).range ↔ ∀ i j, i ≠ j → (g : Matrix (Fin n) (Fin n) k) i j = 0 := by
  constructor
  · rintro ⟨t, rfl⟩ i j hij
    rw [val_diagT, diagonal_apply_ne _ hij]
  · intro h
    have hd : (g : Matrix (Fin n) (Fin n) k) = diagonal fun i => (g : Matrix (Fin n) (Fin n) k) i i := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · rw [diagonal_apply_ne _ hij, h i j hij]
    have hdet : (g : Matrix (Fin n) (Fin n) k).det ≠ 0 := g.isUnit.map Matrix.detMonoidHom |>.ne_zero
    have hne : ∀ i, (g : Matrix (Fin n) (Fin n) k) i i ≠ 0 := by
      intro i
      rw [hd, det_diagonal] at hdet
      exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
    refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
    ext : 1
    rw [val_diagT]
    simp only [Units.val_mk0]
    exact hd.symm

private theorem isClosed_diag : IsClosed ((diagT k (Fin n)).range : Set (GL (Fin n) k)) := by
  haveI := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField k
  have he : ((diagT k (Fin n)).range : Set (GL (Fin n) k)) =
      Units.val ⁻¹' {M : Matrix (Fin n) (Fin n) k | ∀ i j, i ≠ j → M i j = 0} := by
    ext g
    exact mem_diag g
  rw [he]
  refine IsClosed.preimage Units.continuous_val ?_
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
  exact (continuous_apply j).comp (continuous_apply i)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem sg_refl (g : GL (Fin n) k) : sg (RingEquiv.refl k) g = g := by
  ext i j
  simp [sg]

private theorem cent_diag {γ y : GL (Fin n) k} {x : Fin n → kˣ} (hx : Strict x)
    (hy : y⁻¹ * γ * y = diagT k (Fin n) x) {t : GL (Fin n) k} (ht : t ∈ Subgroup.centralizer {γ}) :
    y⁻¹ * t * y ∈ (diagT k (Fin n)).range := by
  have hc : γ * t = t * γ := Subgroup.mem_centralizer_iff.1 ht γ (Set.mem_singleton γ)
  have hcyc : Cyc (RingEquiv.refl k) 1 := ⟨fun _ => rfl, one_pos, fun _ => rfl⟩
  have hz : (y⁻¹ * t * y)⁻¹ * diagT k (Fin n) x * sg (RingEquiv.refl k) (y⁻¹ * t * y) =
      diagT k (Fin n) x := by
    rw [sg_refl, ← hy]
    simp only [_root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc γ t y, hc, mul_assoc t, inv_mul_cancel_left]
  obtain ⟨s, hs⟩ := strictNormal k n (RingEquiv.refl k) 1 hcyc x x hx hx _ hz
  exact ⟨s, hs.symm⟩

end

theorem UpperTheory.Gal.InertialTypesAlt.L.volRatio :
    UpperTheory.Gal.InertialTypesAlt.L.VolRatio := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hgen n _ _ r r' hr0 hr1 hr0' hr1' hrr'
  haveI : T2Space k := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField k
  have hemb : Topology.IsClosedEmbedding (incl : GL (Fin n) k →* GL (Fin n) E) :=
    ((bridge k E σ).2.2 n).2.2.2.1
  obtain ⟨KE, hKE, -, -⟩ := ballSub E n r hr0 hr1
  obtain ⟨Kk, hKk, hKko, -⟩ := ballSub k n r' hr0' hr1'
  set D : Subgroup (GL (Fin n) k) := (diagT k (Fin n)).range with hD
  set Cr : Subgroup (GL (Fin n) k) := D ⊓ KE.comap (incl : GL (Fin n) k →* GL (Fin n) E) with hCr
  set Hr : Subgroup (GL (Fin n) k) := D ⊓ Kk with hHr
  have hincl : ∀ (g : GL (Fin n) k) (i j : Fin n),
      ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j = algebraMap k E ((g : Matrix (Fin n) (Fin n) k) i j) := by
    intro g i j
    rfl
  have hHC : Hr ≤ Cr := by
    rintro d ⟨⟨s, rfl⟩, hd⟩
    refine ⟨⟨s, rfl⟩, ?_⟩
    have hd' : diagT k (Fin n) s ∈ ball n r' := by
      rw [← hKk]
      exact hd
    show incl (diagT k (Fin n) s) ∈ KE
    rw [← SetLike.mem_coe, hKE]
    intro i j
    rw [hincl, val_diagT]
    by_cases hij : i = j
    · subst hij
      have h1 := hd' i i
      rw [val_diagT] at h1
      simpa using hrr' (s i) (by simpa using h1)
    · simp [diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hCrc : IsCompact (Cr : Set (GL (Fin n) k)) := by
    have h1 : IsCompact ((incl : GL (Fin n) k →* GL (Fin n) E) ⁻¹' (KE : Set (GL (Fin n) E))) :=
      hemb.isCompact_preimage (by rw [hKE]; exact BallG.isCompact_ball hr1)
    exact h1.inter_left isClosed_diag
  have hidx : Hr.relIndex Cr ≠ 0 := by
    haveI : CompactSpace Cr := isCompact_iff_compactSpace.mp hCrc
    have hopen : IsOpen ((Hr.subgroupOf Cr : Subgroup Cr) : Set Cr) := by
      have he : ((Hr.subgroupOf Cr : Subgroup Cr) : Set Cr) = Subtype.val ⁻¹' (Kk : Set (GL (Fin n) k)) := by
        ext g
        simp only [Subgroup.coe_subgroupOf, Set.mem_preimage, SetLike.mem_coe]
        exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
      rw [he]
      exact continuous_subtype_val.isOpen_preimage _ hKko
    haveI := Subgroup.quotient_finite_of_isOpen _ hopen
    exact Subgroup.index_ne_zero_of_finite
  refine ⟨(Hr.relIndex Cr : ℝ), Nat.cast_pos.2 (Nat.pos_of_ne_zero hidx), ?_⟩
  intro γ y x hx hy ν hν
  let c : GL (Fin n) k →* GL (Fin n) k :=
    { toFun := fun g => y⁻¹ * g * y
      map_one' := by simp
      map_mul' := by
        intro a b
        group }
  have hcs : Function.Surjective c := fun g => ⟨y * g * y⁻¹, by simp [c, mul_assoc]⟩
  set C : Subgroup (GL (Fin n) k) := Cr.comap c with hC
  set H : Subgroup (GL (Fin n) k) := Hr.comap c with hH
  have hTc : IsClosed ((Subgroup.centralizer {γ} : Subgroup (GL (Fin n) k)) : Set (GL (Fin n) k)) :=
    Set.isClosed_centralizer _
  have hCT : C ≤ Subgroup.centralizer {γ} := by
    intro g hg
    obtain ⟨s, hs⟩ := hg.1
    rw [Subgroup.mem_centralizer_iff]
    rintro h rfl
    have hγ : h = y * diagT k (Fin n) x * y⁻¹ := by
      rw [← hy]
      group
    have hg' : g = y * diagT k (Fin n) s * y⁻¹ := by
      rw [hs]
      simp only [c, MonoidHom.coe_mk, OneHom.coe_mk]
      group
    rw [hγ, hg']
    simp only [mul_assoc, inv_mul_cancel_left]
    congr 1
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm]
  have hCc : IsCompact (C : Set (GL (Fin n) k)) :=
    ((Homeomorph.mulLeft y⁻¹).trans (Homeomorph.mulRight y)).isCompact_preimage.2 hCrc
  have hcD : ∀ t : Subgroup.centralizer {γ}, c t ∈ D := fun t => cent_diag hx hy t.2
  have hHo : IsOpen {t : Subgroup.centralizer {γ} | (t : GL (Fin n) k) ∈ H} := by
    have he : {t : Subgroup.centralizer {γ} | (t : GL (Fin n) k) ∈ H} =
        (fun t : Subgroup.centralizer {γ} => y⁻¹ * (t : GL (Fin n) k) * y) ⁻¹' (Kk : Set (GL (Fin n) k)) := by
      ext t
      exact ⟨fun h => h.2, fun h => ⟨hcD t, h⟩⟩
    rw [he]
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).isOpen_preimage _ hKko
  have hv := (volIdx (GL (Fin n) k) (Subgroup.centralizer {γ}) C H hTc ν hν hCT hCc
    (Subgroup.comap_mono hHC) hHo).2
  have hri : H.relIndex C = Hr.relIndex Cr := by
    rw [hH, hC, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hcs]
  have e1 : {t : Subgroup.centralizer {γ} | incl (y⁻¹ * (t : GL (Fin n) k) * y) ∈ ball n r} =
      {t : Subgroup.centralizer {γ} | (t : GL (Fin n) k) ∈ C} := by
    ext t
    show _ ↔ c t ∈ D ∧ incl (c t) ∈ KE
    rw [← SetLike.mem_coe (p := KE), hKE]
    exact ⟨fun h => ⟨hcD t, h⟩, fun h => h.2⟩
  have e2 : {t : Subgroup.centralizer {γ} | y⁻¹ * (t : GL (Fin n) k) * y ∈ ball n r'} =
      {t : Subgroup.centralizer {γ} | (t : GL (Fin n) k) ∈ H} := by
    ext t
    show _ ↔ c t ∈ D ∧ c t ∈ Kk
    rw [← SetLike.mem_coe (p := Kk), hKk]
    exact ⟨fun h => ⟨hcD t, h⟩, fun h => h.2⟩
  rw [e1, e2, hv, hri]
end
end

section

open MeasureTheory PositivityTheory.Rg.Tf.Loc

private theorem exists_reps {G ι : Type} [Group G] (H U : Subgroup G) (R : Finset ι) (x : ι → G)
    (hd : ∀ i ∈ R, ∀ j ∈ R, (∃ h ∈ H, ∃ u ∈ U, x i = h * x j * u) → i = j) :
    ∃ r : G → G, (∀ g, ∃ h ∈ H, ∃ u ∈ U, g = h * r g * u) ∧ (∀ g, ∀ h ∈ H, ∀ u ∈ U, r (h * g * u) = r g) ∧
      ∀ i ∈ R, r (x i) = x i := by
  classical
  let S : Setoid G :=
    { r := fun g g' => ∃ h ∈ H, ∃ u ∈ U, g = h * g' * u
      iseqv :=
        { refl := fun g => ⟨1, H.one_mem, 1, U.one_mem, by simp⟩
          symm := by
            rintro g g' ⟨h, hh, u, hu, rfl⟩
            exact ⟨h⁻¹, H.inv_mem hh, u⁻¹, U.inv_mem hu, by group⟩
          trans := by
            rintro g g' g'' ⟨h₁, hh₁, u₁, hu₁, rfl⟩ ⟨h₂, hh₂, u₂, hu₂, rfl⟩
            exact ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, u₂ * u₁, U.mul_mem hu₂ hu₁, by group⟩ } }
  let f : Quotient S → G := fun q =>
    if hq : ∃ i ∈ R, Quotient.mk S (x i) = q then x hq.choose else q.out
  have hf : ∀ g, S.r g (f (Quotient.mk S g)) := by
    intro g
    by_cases hq : ∃ i ∈ R, Quotient.mk S (x i) = Quotient.mk S g
    · simp only [f, dif_pos hq]
      exact Quotient.exact (hq.choose_spec.2.symm)
    · simp only [f, dif_neg hq]
      exact Quotient.exact (Quotient.out_eq (Quotient.mk S g)).symm
  refine ⟨fun g => f (Quotient.mk S g), hf, ?_, ?_⟩
  · intro g h hh u hu
    have : Quotient.mk S (h * g * u) = Quotient.mk S g := Quotient.sound ⟨h, hh, u, hu, rfl⟩
    simp only [this]
  · intro i hi
    have hq : ∃ j ∈ R, Quotient.mk S (x j) = Quotient.mk S (x i) := ⟨i, hi, rfl⟩
    simp only [f, dif_pos hq]
    rw [hd _ hq.choose_spec.1 i hi (Quotient.exact hq.choose_spec.2)]

theorem UpperTheory.Gal.InertialTypesAlt.L.cosetSum :
    UpperTheory.Gal.InertialTypesAlt.L.CosetSum := by
  intro G _ _ _ _ _ _ _ _ μ hμ K H hKo hKc hHc hcomm ν hν ι R x V S hV hS hd
  classical
  haveI : SFinite μ := inferInstance
  haveI : LocallyCompactSpace H := hHc.locallyCompactSpace
  haveI : SFinite ν := inferInstance
  letI cH : CommGroup H :=
    { (inferInstance : Group H) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  haveI : ν.IsInvInvariant := @Measure.IsHaarMeasure.isInvInvariant_of_regular H cH _ _ _ _ ν hν _ _
  obtain ⟨rep, hrep, hinv, hfix⟩ := exists_reps H K R x hd
  let W : G → Set H := fun y => {h | y⁻¹ * (h : G) * y ∈ K}
  have hWcont : ∀ y : G, Continuous fun h : H => y⁻¹ * (h : G) * y := fun y => by fun_prop
  have hWopen : ∀ y, IsOpen (W y) := fun y => hKo.preimage (hWcont y)
  have hWpos : ∀ y, ν (W y) ≠ 0 := fun y =>
    ((hWopen y).measure_pos ν ⟨1, by simp [W, K.one_mem]⟩).ne'
  have hWfin : ∀ y, ν (W y) ≠ ⊤ := by
    intro y
    have hc : IsCompact (W y) := by
      have e : W y = Subtype.val ⁻¹' ((fun k => y * k * y⁻¹) '' (K : Set G)) := by
        ext h
        simp only [W, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image]
        constructor
        · intro hk
          exact ⟨_, hk, by group⟩
        · rintro ⟨k, hk, hk'⟩
          rw [← hk']
          have e2 : y⁻¹ * (y * k * y⁻¹) * y = k := by group
          rw [e2]
          exact hk
      rw [e]
      exact hHc.isClosedEmbedding_subtypeVal.isCompact_preimage (hKc.image (by fun_prop))
    exact hc.measure_lt_top.ne
  have hrepK : ∀ g, ∀ k ∈ K, rep (g * k) = rep g := fun g k hk => by
    simpa using hinv g 1 H.one_mem k hk
  have hrepH : ∀ g, ∀ h ∈ H, rep (h * g) = rep g := fun g h hh => by
    simpa using hinv g h hh 1 K.one_mem
  let ρ : G → ENNReal := fun g => if (rep g)⁻¹ * g ∈ K then (ν (W (rep g)))⁻¹ else 0
  have hρK : ∀ g, ∀ k ∈ K, ρ (g * k) = ρ g := by
    intro g k hk
    simp only [ρ, hrepK g k hk, ← mul_assoc, K.mul_mem_cancel_right hk]
  have hρm : Measurable ρ := by
    have : IsLocallyConstant ρ := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g
      have ho : IsOpen ((fun z => g⁻¹ * z) ⁻¹' (K : Set G)) := hKo.preimage (by fun_prop)
      filter_upwards [ho.mem_nhds (by simp [K.one_mem])] with z hz
      have : z = g * (g⁻¹ * z) := by group
      rw [this, hρK g _ hz]
    exact this.continuous.measurable
  have hρn : IsQuotNormaliser H ν ρ := by
    refine ⟨hρm, fun g => ?_⟩
    obtain ⟨h0, hh0, k0, hk0, hg⟩ := hrep g
    set y := rep g with hy
    have key : ∀ h : H, ρ (↑h * g) = (W y).indicator (fun _ => (ν (W y))⁻¹) (⟨h0, hh0⟩ * h) := by
      intro h
      have hr : rep (↑h * g) = y := hrepH g h h.2
      simp only [ρ, hr, Set.indicator, W, Set.mem_setOf_eq]
      have e : y⁻¹ * (↑h * g) = (y⁻¹ * ↑(⟨h0, hh0⟩ * h : H) * y) * k0 := by
        rw [hg]
        simp only [Subgroup.coe_mul]
        rw [(hcomm h0 hh0 h h.2).eq]
        group
      rw [e, K.mul_mem_cancel_right hk0]
    simp_rw [key]
    rw [lintegral_indicator_const_comp (measurable_const_mul _) (hWopen y).measurableSet]
    rw [measure_preimage_mul, ENNReal.inv_mul_cancel (hWpos y) (hWfin y)]
  rcases R.eq_empty_or_nonempty with hR | ⟨i0, hi0⟩
  · have hS0 : S = ∅ := by
      ext g
      simp [hS g, hR]
    simp [quotIntegral, hS0, hR]
  have hWV : ∀ i ∈ R, W (x i) = V := by
    intro i hi
    ext h
    exact (hV i hi h).symm
  have hV0 : ν V ≠ 0 := hWV i0 hi0 ▸ hWpos (x i0)
  have hVt : ν V ≠ ⊤ := hWV i0 hi0 ▸ hWfin (x i0)
  have hSK : ∀ g, ∀ k ∈ K, g ∈ S → g * k ∈ S := by
    intro g k hk hg
    obtain ⟨i, hi, h, hh, κ, hκ, rfl⟩ := (hS _).1 hg
    exact (hS _).2 ⟨i, hi, h, hh, κ * k, K.mul_mem hκ hk, by group⟩
  have hSH : ∀ g, ∀ h ∈ H, h * g ∈ S ↔ g ∈ S := by
    intro g h hh
    constructor
    · intro hg
      obtain ⟨i, hi, h', hh', κ, hκ, e⟩ := (hS _).1 hg
      refine (hS _).2 ⟨i, hi, h⁻¹ * h', H.mul_mem (H.inv_mem hh) hh', κ, hκ, ?_⟩
      rw [mul_assoc (h⁻¹ * h'), mul_assoc h⁻¹, ← mul_assoc h', ← e]
      group
    · intro hg
      obtain ⟨i, hi, h', hh', κ, hκ, rfl⟩ := (hS _).1 hg
      exact (hS _).2 ⟨i, hi, h * h', H.mul_mem hh hh', κ, hκ, by group⟩
  have hSo : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun z => g⁻¹ * z) ⁻¹' (K : Set G), ?_, hKo.preimage (by fun_prop), by simp [K.one_mem]⟩
    intro z hz
    have : z = g * (g⁻¹ * z) := by group
    rw [this]
    exact hSK g _ hz hg
  let F : G → ENNReal := S.indicator 1
  have hFm : Measurable F := measurable_one.indicator hSo.measurableSet
  have hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g := by
    intro h hh g
    by_cases hg : g ∈ S
    · simp [F, hg, (hSH g h hh).2 hg]
    · simp [F, hg, mt (hSH g h hh).1 hg]
  have hex : ∃ ρ, IsQuotNormaliser H ν ρ := ⟨ρ, hρn⟩
  have hswap := lintegral_normaliser_eq (μG := μ) hFm hFH hex.choose_spec hρn
  have hpt : ∀ g, F g * ρ g =
      ∑ i ∈ R, ((fun z => (x i)⁻¹ * z) ⁻¹' (K : Set G)).indicator (fun _ => (ν V)⁻¹) g := by
    intro g
    by_cases hg : g ∈ S
    · obtain ⟨i, hi, h, hh, κ, hκ, rfl⟩ := (hS _).1 hg
      have hr : rep (h * x i * κ) = x i := by rw [hinv _ h hh κ hκ, hfix i hi]
      rw [Finset.sum_eq_single_of_mem i hi]
      · simp [F, Set.indicator_of_mem hg, ρ, hr, hWV i hi, Set.indicator]
      · intro j hj hji
        rw [Set.indicator_of_notMem]
        intro hm
        apply hji
        refine hd j hj i hi ⟨h, hh, κ * ((x j)⁻¹ * (h * x i * κ))⁻¹, K.mul_mem hκ (K.inv_mem hm), ?_⟩
        group
    · have hF0 : F g = 0 := Set.indicator_of_notMem hg _
      rw [hF0, zero_mul]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      rw [Set.indicator_of_notMem]
      intro hm
      apply hg
      exact (hS _).2 ⟨i, hi, 1, H.one_mem, (x i)⁻¹ * g, hm, by group⟩
  have hcomp : ∫⁻ g, F g * ρ g ∂μ = R.card * ((ν V)⁻¹ * μ K) := by
    rw [lintegral_congr (fun g => hpt g), lintegral_finsetSum]
    · simp_rw [lintegral_indicator_const (hKo.measurableSet.preimage (measurable_const_mul _)),
        measure_preimage_mul]
      rw [Finset.sum_const, nsmul_eq_mul]
    · intro i _
      exact measurable_const.indicator (hKo.measurableSet.preimage (measurable_const_mul _))
  have hI : ∫⁻ g, F g * hex.choose g ∂μ = R.card * ((ν V)⁻¹ * μ K) := hswap.trans hcomp
  have hfin : (R.card : ENNReal) * ((ν V)⁻¹ * μ K) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hV0) hKc.measure_lt_top.ne)
  have hpt2 : ∀ g, (S.indicator 1 g : ℂ) * (((hex.choose g).toReal : ℝ) : ℂ)
      = (((F g * hex.choose g).toReal : ℝ) : ℂ) := by
    intro g
    by_cases hg : g ∈ S <;> simp [F, hg]
  unfold quotIntegral
  rw [dif_pos hex]
  simp_rw [hpt2]
  have hm2 : Measurable fun g => F g * hex.choose g := hFm.mul hex.choose_spec.1
  rw [integral_complex_ofReal, integral_toReal hm2.aemeasurable (ae_lt_top hm2 (hI ▸ hfin)), hI]
  congr 1
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    measureReal_def, measureReal_def]
  ring
end

section

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem quotInt_smul {G T X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure X) (u : X → G) (j : T → G) (ν : Measure T) (c : ℂ) (Φ : X → ℂ) :
    quotInt μ u j ν (c • Φ) = c * quotInt μ u j ν Φ := by
  unfold quotInt
  split_ifs with h
  · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _
  · simp

private theorem orb_smul {n : ℕ} {R : Type*} [CommRing R] [TopologicalSpace R] [MeasurableSpace (GL (Fin n) R)]
    (μ : Measure (GL (Fin n) R)) (γ : GL (Fin n) R) (ν : Measure (Subgroup.centralizer {γ})) (c : ℂ)
    (f : GL (Fin n) R → ℂ) : orb μ γ ν (c • f) = c * orb μ γ ν f := by
  unfold orb
  exact quotInt_smul μ id (fun t : Subgroup.centralizer {γ} => (t : GL (Fin n) R)) ν c
    (fun x => f (x⁻¹ * γ * x))

theorem matchSmul : MatchSmul := by
  intro F E _ _ _ _ _ σ n v c hc φ f h
  intro _ _ _ _ mE mF h1 h2 h3 h4 γ hγ ν hν
  obtain ⟨hA, hB⟩ := h mE mF h1 h2 h3 h4 γ hγ ν hν
  refine ⟨fun δ hδ => ?_, fun hn => ?_⟩
  · rw [hA δ hδ, one_mul, orb_smul]
  · have := hB hn
    rw [orb_smul] at this
    exact (mul_eq_zero.1 this).resolve_left hc

end UpperTheory.Gal.InertialTypesAlt.L

end
end

section

noncomputable section

open ValuativeRel Matrix GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

def BallLev : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (r : ValueGroupWithZero k),
    0 < r → r < 1 → ∀ K : Subgroup (GL (Fin n) k), (K : Set (GL (Fin n) k)) = ball n r → IwLev K ∧ ∀ t, dcos K t = elemSet r {t}

def LevOf : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (r : ValueGroupWithZero k),
    0 < r → r < 1 → ∀ D : Subgroup (Fin n → kˣ), IsCompact (D : Set (Fin n → kˣ)) → (∀ d ∈ D, ∀ i, valuation k (d i : k) = 1) →
    ∃ K : Subgroup (GL (Fin n) k), (∀ g, g ∈ K ↔ ∃ a ∈ ball n r, ∃ d ∈ D, g = a * diagT k (Fin n) d) ∧ IwLev K ∧
      ∀ t, dcos K t = elemSet r {x | ∃ d ∈ D, x = t * d}

def SmallRad : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
    (∀ U : Set (GL (Fin n) k), U ∈ nhds 1 → ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ r' ≤ r, ball n r' ⊆ U) ∧
    (∀ W : Set (Fin n → kˣ), W ∈ nhds 1 → ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ r' ≤ r, ∀ u, Near r' u → u ∈ W) ∧
    (∀ r : ValueGroupWithZero k, r < 1 → ∃ D : Subgroup (Fin n → kˣ), (∀ u, u ∈ D ↔ Near r u) ∧ IsCompact (D : Set (Fin n → kˣ))) ∧
    Continuous (diagT k (Fin n)) ∧ (∃ t : Fin n → kˣ, Strict t) ∧ ∀ t₀ t : Fin n → kˣ, Strict t₀ → Dom t → Strict (t₀ * t)

end UpperTheory.Gal.InertialTypesAlt.L
end
end
