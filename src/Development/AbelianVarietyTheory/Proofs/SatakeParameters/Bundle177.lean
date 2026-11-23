module

public import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.Bundle001
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle169
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle170
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle018
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.Bundle009
import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
import Formalism.LocalToGlobal.KernelLattices.Bundle001
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.LtCNeZero
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle001

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.OrthDual

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem int_mem_range {t : E} (h : IsIntegral ℤ t) : t ∈ (algebraMap (𝓞 E) E).range :=
  ⟨⟨t, h⟩, rfl⟩

theorem ringHom_mem_range (τ : E →+* E) {t : E} (h : t ∈ (algebraMap (𝓞 E) E).range) :
    τ t ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨r, rfl⟩ := h
  exact int_mem_range (IsIntegral.map τ.toIntAlgHom r.isIntegral_coe)

theorem exists_int_smul_mem (M : Submodule (𝓞 E) (Fin N → E)) {v : Fin N → E}
    (hv : v ∈ Submodule.span E (M : Set (Fin N → E))) : ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, mul_ne_zero h₁ h₂, ?_⟩
    have e : ((n₁ * n₂ : ℤ) : E) • (x + y) = n₂ • ((n₁ : E) • x) + n₁ • ((n₂ : E) • y) := by
      rw [← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, smul_smul, smul_smul, smul_add]
      push_cast
      rw [mul_comm (n₂ : E)]
    rw [e]
    exact add_mem (zsmul_mem hx _) (zsmul_mem hy _)
  | smul e x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨k, hk, hki⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
    have hke := hki e (Finset.mem_singleton_self e)
    refine ⟨k * n, mul_ne_zero hk hn, ?_⟩
    have e1 : ((k * n : ℤ) : E) • (e • x) = (⟨k • e, hke⟩ : 𝓞 E) • ((n : E) • x) := by
      rw [← algebraMap_smul E (⟨k • e, hke⟩ : 𝓞 E), smul_smul, smul_smul]
      congr 1
      show ((k * n : ℤ) : E) * e = (k • e) * n
      push_cast
      rw [zsmul_eq_mul]
      ring
    rw [e1]
    exact M.smul_mem _ hx

theorem isLat_dl (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E))
    (hc : Formalism.L2.PairingIndexBounds.F.IsOrthCo (σ : E →+* E) J co) (M : Submodule (𝓞 E) (Fin N → E))
    (hM : Formalism.L2.GlobalTheoryTheory.Comp.IsLat M) : Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M) := by
  classical
  set v : Fin N → Fin N → E := fun a => co.symm (Pi.single a 1) with hv
  have key : ∀ x y, Formalism.UG.hform (σ : E →+* E) J x y = ∑ b, (σ : E →+* E) (co x b) * co y b :=
    fun x y => (hc x y).symm
  have hsingle : ∀ (a : Fin N) (c : E), Pi.single a c = c • (Pi.single a (1 : E) : Fin N → E) := by
    intro a c; ext j; simp [Pi.single_apply]
  have hexp : ∀ z : Fin N → E, z = ∑ a, co z a • v a := by
    intro z
    conv_lhs => rw [← co.symm_apply_apply z, ← Finset.univ_sum_single (co z)]

    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsingle, map_smul]
  have hcv : ∀ (c : E) a b, co (c • v a) b = if b = a then c else 0 := by
    intro c a b; simp [v, Pi.single_apply]
  have hform_v : ∀ (c : E) a x, Formalism.UG.hform (σ : E →+* E) J x (c • v a) = (σ : E →+* E) (co x a) * c := by
    intro c a x; rw [key]; simp [hcv]

  have hex : ∀ a, ∃ n : ℤ, n ≠ 0 ∧ (n : E) • v a ∈ M := fun a =>
    exists_int_smul_mem M (by rw [hM.2]; trivial)
  choose n hn0 hnM using hex
  have hle : Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M ≤
      Submodule.span (𝓞 E) (Set.range fun a => ((n a : E))⁻¹ • v a) := by
    intro y hy
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl] at hy
    have hr : ∀ a, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = (n a : E) * co y a := by
      intro a
      obtain ⟨r, hr⟩ := hy _ (hnM a)
      refine ⟨r, ?_⟩
      rw [hr, key, Finset.sum_eq_single a]
      · rw [hcv, if_pos rfl, map_intCast]
      · intro b _ hb
        rw [hcv, if_neg hb, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ a) h
    choose r hr using hr
    rw [hexp y]
    refine Submodule.sum_mem _ fun a _ => ?_
    have e3 : co y a • v a = r a • (((n a : E))⁻¹ • v a) := by
      rw [← algebraMap_smul E (r a), smul_smul, hr a, mul_comm (n a : E), mul_assoc,
        mul_inv_cancel₀ (Int.cast_ne_zero.2 (hn0 a)), mul_one]
    rw [e3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  haveI : Module.Finite (𝓞 E) (Submodule.span (𝓞 E) (Set.range fun a => ((n a : E))⁻¹ • v a)) :=
    Module.Finite.span_of_finite _ (Set.finite_range _)
  refine ⟨Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle), ?_⟩

  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hM.1
  obtain ⟨m, hm0, hmi⟩ := exists_integral_multiples ℤ ℚ (L := E)
    (s.biUnion fun x => Finset.univ.image fun b => co x b)
  have hint : ∀ a, ∀ x ∈ M, (m : E) * co x a ∈ (algebraMap (𝓞 E) E).range := by
    intro a x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      apply int_mem_range
      have := hmi (co x a) (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩⟩)
      rwa [zsmul_eq_mul] at this
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), Pi.add_apply, mul_add]; exact add_mem hx hy
    | smul t x _ hx =>
      rw [← algebraMap_smul E t x, map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm]
      exact mul_mem ⟨t, rfl⟩ hx
  have hmem : ∀ a, (m : E) • v a ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl σ J M := by
    intro a
    rw [Formalism.L2.GlobalTheoryTheory.Comp.mem_dl]
    intro x hx
    rw [hform_v]
    have e4 : (σ : E →+* E) (co x a) * (m : E) = (σ : E →+* E) ((m : E) * co x a) := by
      rw [map_mul, map_intCast, mul_comm]
    rw [e4]
    exact ringHom_mem_range _ (hint a x hx)
  rw [eq_top_iff]
  intro z _
  rw [hexp z]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
  have e5 : v a = ((m : E))⁻¹ • ((m : E) • v a) := by
    rw [smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hm0), one_smul]
  rw [e5]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem a))

end GlobalTheory.OrthDual

theorem GlobalTheory.isLat_dl_of_isOrthCo : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E), (∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) → ∀ M : Submodule (𝓞 E) (Fin N → E), Formalism.L2.GlobalTheoryTheory.Comp.IsLat M → Formalism.L2.GlobalTheoryTheory.Comp.IsLat (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J M) := by
  rintro R F E _ _ _ _ _ _ sp N J ⟨co, hc⟩ M hM
  exact GlobalTheory.OrthDual.isLat_dl sp.cm.sig J co hc M hM

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.PlaceAbove

theorem involution_conj (D : D7) (x : D.host.E) : sigD D (D.host.conj x) = x := by
  have h3 : ∀ y : D.host.E, sigD D y = D.host.conj y := fun y => bridge_star_holds D.R D.host y
  rw [h3, ← Formalism.L2.Herm.star_conj, ← Formalism.L2.Herm.star_conj, star_star]

theorem posArg_eq_self (D : D7) {n : ℕ} (s : Fin n) (x : D.host.E) :
    (if Even s.val then (if IsOddPos s then D.host.conj x else x)
      else sigD D (if IsOddPos s then D.host.conj x else x)) = x := by
  by_cases hs : s.val % 2 = 1
  · have hodd : IsOddPos s := hs
    have hne : ¬ Even s.val := by rw [Nat.not_even_iff_odd, Nat.odd_iff]; exact hs
    rw [if_neg hne, if_pos hodd, involution_conj]
  · have hodd : ¬ IsOddPos s := hs
    have hev : Even s.val := by rw [Nat.even_iff]; omega
    rw [if_pos hev, if_neg hodd]

end GlobalTheory.TwU.PlaceAbove


open GlobalTheory.TwU.PlaceAbove in
theorem GlobalTheory.TwU.lamPos_of_posEmb : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v) (e : D.what₂.LL →+* X.G.Kf), (∀ (z : D.what₂.LL) (hz : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ), E.iK (e z) = lam ⟨D.what₂.embLL z, hz⟩) → (∀ (v : X.Pl) (s : Fin (X.G.P.n' v)) (x : D.host.E), e (tEL D (pos ⟨v, s⟩) (if Even s.val then x else sigD D x)) = X.G.P.ι v ((X.G.P.σ v ^ s.val) (ρ v x))) → LamPos X E pos lam ρ := by
  intro p _ X E D pos lam ρ e hK hpos
  intro v s x
  have h1 := hpos v s (if IsOddPos s then D.host.conj x else x)
  rw [posArg_eq_self D s x] at h1
  have hz := embLL_mem_alg D (tEL D (pos ⟨v, s⟩) x)
  have h2 := hK (tEL D (pos ⟨v, s⟩) x) hz
  have he : Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x = D.what₂.embLL (tEL D (pos ⟨v, s⟩) x) := (tEL_emb D (pos ⟨v, s⟩) x).symm
  have hL : Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = lam ⟨D.what₂.embLL (tEL D (pos ⟨v, s⟩) x), hz⟩ := by
    unfold Formalism.MainNotions.TaylorLogMetric.lamC
    rw [dite_eq_left (he ▸ hz)]
    congr 1
    exact Subtype.ext he
  show Formalism.MainNotions.TaylorLogMetric.lamC lam (Formalism.MainNotions.TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = _
  rw [hL, ← h2, h1]
  rfl
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isUnit_det_frameMatrix_ofCharts : ∀ {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7} (cp : ChartPts X D) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))) (j : ℕ) (La : X.Lt j) (v : X.Pl), IsUnit ((fdOfCharts cp a bad).frM j La v).det := by
  intro p _ X D cp a bad j La v
  simp only [Formalism.L2.PairingIndexBounds.F.fdOfCharts]
  rw [Matrix.det_submatrix_equiv_self]
  erw [← RingHom.map_det]
  refine IsUnit.map _ ?_
  rw [Matrix.det_mul]
  refine IsUnit.mul ?_ ?_
  · rw [LinearMap.det_toMatrix']
    exact LinearEquiv.isUnit_det' _
  · exact Matrix.isUnits_det_units (cp.B j La)

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.UG (bc prV)
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.primeLocalization_companionLattice_eq_of_localizations : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ Λ' : Submodule (𝓞 E) (Fin N → E)), Λ.FG → Λ'.FG →
    Formalism.HermitianLatticesTheory.localization₂ q Λ = Formalism.HermitianLatticesTheory.localization₂ q Λ' →
    Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ =
      Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ' →
    Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ') := by
  first | exact @GlobalTheory.CompanLocP.locP_companion_eq | exact GlobalTheory.CompanLocP.locP_companion_eq | (intros; apply GlobalTheory.CompanLocP.locP_companion_eq <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

open Matrix

theorem isOrthCo_toLE_of_cT_mul_self {E : Type} [Field E] [NumberField E] {N : ℕ} (σ : E →+* E)
    (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E) (h : cT σ co.1 * co.1 = J) :
    IsOrthCo σ J (toLE co) := by
  intro x y
  subst h
  have ht (v : Fin N → E) : toLE co v = (co : Matrix (Fin N) (Fin N) E) *ᵥ v := rfl
  rw [ht, ht]

  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply,
  map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, j]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end GlobalTheory.TwV
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.XdInert

theorem gidx_facts : ∀ (D : D7) (T p : ℕ), GIdx D.host T p →
    5 ≤ p ∧ GL3Theta.InertK D p ∧ Nat.Coprime T p ∧ ∀ i, p ≠ D.host.g i := by
  intro D T p h
  obtain ⟨hp, h5, hc, hn, hl, hT⟩ := h
  refine ⟨h5, ?_, ?_, ?_⟩
  · exact (GlobalTheory.TwU.Served.served_facts D p hp hc hn).2.1
  · exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hT).symm
  · intro i hi
    exact hl (hi ▸ D.host.g_level i)

end GlobalTheory.TwU.XdInert
end

section

noncomputable section

namespace GlobalTheory.DetBasisNorm

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

theorem norm_det_le_one {p : ℕ} [Fact p.Prime] {N : ℕ} {C : Matrix (Fin N) (Fin N) ℂ_[p]}
    (h : ∀ a b, ‖C a b‖ ≤ 1) : ‖C.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ_[p])‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
  rw [hs, one_mul]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => h _ _

theorem col_mem {E : Type} [Field E] {N : ℕ} {L₀ L : Submodule (𝓞 E) (Fin N → E)}
    (h₀ : ∀ x, x ∈ L₀ ↔ ∀ k, IsIntegral ℤ (x k)) {A : Matrix (Fin N) (Fin N) E}
    (hA : ∀ v ∈ L₀, A.mulVec v ∈ L) (b : Fin N) : (fun i => A i b) ∈ L := by
  have := hA (Pi.single b 1) ((h₀ _).2 fun k => by
    by_cases hk : k = b
    · subst hk; simpa using isIntegral_one
    · simpa [Pi.single_eq_of_ne hk] using isIntegral_zero)
  rwa [Matrix.mulVec_single_one] at this

theorem mulVec_mem {E : Type} [Field E] {N : ℕ} {L₀ L : Submodule (𝓞 E) (Fin N → E)}
    (h₀ : ∀ x, x ∈ L₀ ↔ ∀ k, IsIntegral ℤ (x k)) {A : Matrix (Fin N) (Fin N) E}
    (hA : ∀ b, (fun i => A i b) ∈ L) : ∀ v ∈ L₀, A.mulVec v ∈ L := by
  intro v hv
  have e : A.mulVec v = ∑ b, (⟨v b, (h₀ v).1 hv b⟩ : 𝓞 E) • (fun i => A i b) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    change _ = v b * A i b
    ring
  rw [e]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hA b)

theorem norm_det_eq_nrmId : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (N : ℕ) (L0 L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (B : Matrix (Fin N) (Fin N) ℂ_[p]), (∀ x, x ∈ L0 ↔ ∀ k, IsIntegral ℤ (x k)) → B.det ≠ 0 → (∀ x ∈ L, ∀ a, ‖(B⁻¹.mulVec fun i => tauEmb D lam τ (x i)) a‖ ≤ 1) → (∀ a, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (x : Fin n → Fin N → D.host.E), (∀ k, ‖r k‖ ≤ 1) ∧ (∀ k, x k ∈ L) ∧ ∀ i, B i a = ∑ k, r k * tauEmb D lam τ (x k i)) → ‖B.det‖ = nrmId D lam τ (detId D L0 L) := by
  intro D p _ lam τ N L0 L B h0 hdet hup hlow
  set ψ := GlobalTheory.KernelScalarUnit.lamTau D lam τ with hψdef
  have hψ : ∀ x, tauEmb D lam τ x = ψ x := fun x => congrFun (GlobalTheory.KernelScalarUnit.tauEmb_eq D lam τ) x
  have hn : (fun x : D.host.E => ‖lamC lam (embT D τ x)‖) = fun x => ‖ψ x‖ := funext fun x => by
    rw [← hψ]; rfl

  have hgen : ∀ A : Matrix (Fin N) (Fin N) D.host.E, (∀ v ∈ L0, A.mulVec v ∈ L) → ‖ψ A.det‖ ≤ ‖B.det‖ := by
    intro A hA
    have hC : ∀ a b, ‖(B⁻¹ * A.map ψ) a b‖ ≤ 1 := fun a b => by
      have := hup _ (col_mem h0 hA b) a
      simp only [hψ] at this
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    have e : A.map ψ = B * (B⁻¹ * A.map ψ) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mul]
    have e2 : ψ A.det = (A.map ψ).det := ψ.map_det A
    rw [e2, e, Matrix.det_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_det_le_one hC)
  have hall : ∀ x ∈ detId D L0 L, ‖ψ x‖ ≤ ‖B.det‖ := by
    have : detId D L0 L ≤ GlobalTheory.KernelScalarUnit.ball ψ ‖B.det‖ (norm_nonneg _) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨A, hA, rfl⟩
      exact hgen A hA
    exact fun x hx => this hx
  have hbdd : BddAbove ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)) := by
    refine ⟨‖B.det‖, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hall x hx
  have hne : ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)).Nonempty :=
    ⟨_, 0, Submodule.zero_mem _, rfl⟩
  have hS0 : 0 ≤ sSup ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)) :=
    (norm_nonneg _).trans (le_csSup hbdd ⟨0, Submodule.zero_mem _, rfl⟩)

  choose n r x hr hx hB using hlow
  have hlow : ‖B.det‖ ≤ sSup ((fun x => ‖ψ x‖) '' (detId D L0 L : Set D.host.E)) := by
    let f := (Matrix.detRowAlternating : (Fin N → ℂ_[p]) [⋀^Fin N]→ₗ[ℂ_[p]] ℂ_[p]).toMultilinearMap
    have e1 : B.det = f (fun a => ∑ k, r a k • fun i => ψ (x a k i)) := by
      rw [← Matrix.det_transpose]
      change Matrix.detRowAlternating _ = Matrix.detRowAlternating _
      congr 1
      funext a i
      simp only [Matrix.transpose_apply, hB, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hψ]

    rw [e1, f.map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hS0 fun c _ => ?_
    rw [f.map_smul_univ, smul_eq_mul,
      norm_mul, norm_prod]
    refine (mul_le_of_le_one_left (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun a _ => hr a (c a))).trans ?_
    let A : Matrix (Fin N) (Fin N) D.host.E := Matrix.of fun i a => x a (c a) i
    have hA : ∀ v ∈ L0, A.mulVec v ∈ L := mulVec_mem h0 fun b => hx b (c b)
    have e3 : f (fun a i => ψ (x a (c a) i)) = ψ A.det := by
      rw [ψ.map_det A, ← Matrix.det_transpose]
      rfl
    rw [e3]
    exact le_csSup hbdd ⟨A.det, Submodule.subset_span ⟨A, hA, rfl⟩, rfl⟩
  unfold nrmId
  rw [hn]
  exact le_antisymm hlow (csSup_le hne fun _ ⟨y, hy, e⟩ => e ▸ hall y hy)

end GlobalTheory.DetBasisNorm
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

variable {D : D7}

theorem analyticOnNhd_of_differentiable_vc {N N' : ℕ} (H : TaylorLogMetric.VC D N N' → ℂ) (hH : Differentiable ℂ H) :
    AnalyticOnNhd ℂ H Set.univ := by
  let e : TaylorLogMetric.VC D N N' ≃L[ℂ] (Fin (Module.finrank ℂ (TaylorLogMetric.VC D N N')) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun])
  have h1 : AnalyticOnNhd ℂ (H ∘ e.symm) Set.univ :=
    ReciprocityTheory.AnForm.Osgood.osgood _ Set.univ (H ∘ e.symm) isOpen_univ
      (hH.comp e.symm.differentiable).differentiableOn
  have h2 : H = (H ∘ e.symm) ∘ e := by
    funext z
    simp
  rw [h2]
  exact h1.comp (e.toContinuousLinearMap.analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)

theorem entire_algCoef_comb : ∀ (D : D7) {N N' m : ℕ} (c : Fin m → ℂ) (G : Fin m → TaylorLogMetric.VC D N N' → ℂ), (∀ k, c k ∈ TaylorLogMetric.Qbar) → (∀ k, Differentiable ℂ (G k) ∧ TaylorLogMetric.CoefIn D (G k) TaylorLogMetric.Qbar) → Differentiable ℂ (fun z => ∑ k, c k * G k z) ∧ TaylorLogMetric.CoefIn D (fun z => ∑ k, c k * G k z) TaylorLogMetric.Qbar := by
  intro D N N' m c G hc hG
  have hd : ∀ k, Differentiable ℂ (G k) := fun k => (hG k).1
  refine ⟨by fun_prop, fun α => ?_⟩
  have hsm : ∀ k (n : ℕ), ContDiff ℂ n (G k) := fun k n =>
    Formalism.L2.KerInert.ie_smooth (analyticOnNhd_of_differentiable_vc (G k) (hd k)) n
  rw [Formalism.L2.KerInert.ie_taylor_lin c G hsm α]
  exact sum_mem fun k _ => mul_mem (hc k) ((hG k).2 α)

end GlobalTheory
end
end
