module

public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle007
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Module

open Classical

variable {D : D7}

section Exp

variable (L : SizeData₂ D)

def hN : ℕ := ⌊Formalism.MainNotions.TwistedPlaces.hB L⌋₊

def eA (CA : ℝ) (l : ℕ) : ℕ :=
  ⌈CA * (1 + ((hN L + hN L : ℕ) : ℝ) / (l : ℝ) + (1 + Real.logb l (((hN L + hN L : ℕ) : ℝ) + 1)))⌉₊

end Exp

section RowA

def lenA (i : D.nd.Loc) (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i) (e' : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) : ℚ :=
  if lam ∈ dc.col then (2 * (locDeg D.host.E lam : ℚ) * D.R.m + 1) * e' else 0

variable (L : SizeData₂ D) (tb : Formalism.MainNotions.TwistedPlaces.Tab L)
  (len0 : ∀ i : D.nd.Loc, D.nd.X i → HeightOneSpectrum (𝓞 D.host.E) → ℝ)

end RowA

section Star

variable (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)

def localErrorBoundPlaces (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ) : ℚ :=
  (∑ u ∈ dc.col, ((locDeg D.host.E u : ℚ) * (D.R.m : ℚ) * D.nd.vdel i + 2 * D.nd.vdel i + Br.h0W i u ρ π +
      (D.R.r : ℚ) * (c0 u : ℚ))) +
    (D.R.t : ℚ) * (∑ w ∈ dc.row, ((locDeg D.host.E w : ℚ) + 2) * (cB : ℚ)) +
    4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i +
    (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col

end Star

end Formalism.MainNotions.N

end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem class_map_naturality_of_herr (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F) : Formalism.MainNotions.LiftingTheory.adm21 D HW F := by
  intro l _ K s LL hg
  obtain ⟨hA, -, hN⟩ := h l K s LL hg
  refine ⟨hN, fun _ hl => ?_⟩
  intro T T' f pr pr' hpr
  have h2 : Formalism.MainNotions.LocalSituation.ell (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL hg) = 2 →
      ∃ i : (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL hg).K, i ^ 2 = -1 := by
    intro h2
    exact absurd (((D.loc l).PD_p K).symm.trans h2) hl
  exact ((hA h2 T).2.2 T' f pr pr' hpr).symm

end Formalism.MainNotions.N
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

open NumberField IsDedekindDomain

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V'] {ρ' : Representation LL G V'}
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    {L : Lattice (O := O) ρ} {L' : Lattice (O := O) ρ'}

theorem LiftF_mono (F : LatHom L L') {e e' : ℕ} (he : e ≤ e') (h : F.LiftF PD e) : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (h c hc)

end Gen

section Fields

variable {l : ℕ} [Fact l.Prime]

theorem Ks_mono (K : FinExt l) {s s' : ℕ} (h : s ≤ s') : Ks K s ≤ Ks K s' := by
  unfold Formalism.BasicNotions.Loc.Ks
  refine sup_le_sup_left ?_ _
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  apply IntermediateField.subset_adjoin
  simp only [Set.mem_setOf_eq] at hx ⊢
  obtain ⟨c, hc⟩ := pow_dvd_pow l h
  rw [hc, pow_mul, hx, one_pow]

theorem caseA_of_unram (P : LocPrime l) (H : LocHW l P) {K : FinExt l} {LL : FinExt l} (h : Good K 1 LL)
    (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) : Formalism.MainNotions.LiftingTheory.CaseA (H.W K 1 LL h) := by
  refine ⟨⟨RingHom.injective (algebraMap ↥(K0 K) ↥K.1), fun y =>
    ⟨⟨(y : Om l), IntermediateField.mem_inf.mpr ⟨y.2, hK y.2⟩⟩, by ext; rfl⟩⟩, H.W_s K 1 LL h, ?_⟩
  rw [P.PD_p K]
  exact hl

end Fields

theorem Hmax_const_le (n M h : ℕ) : Formalism.MainNotions.LiftingTheory.Hmax n (fun _ => M) (fun _ => h) ≤ M + h := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax
  exact Finset.sup_le fun _ _ => le_rfl

end Formalism.MainNotions.N
end
end

section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions

theorem lifting_local_of_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.ConclusionL D HW F := h.1

theorem wach_of_lifting_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.ConclusionW D HW F := h.2.1

theorem lift_of_lifting_package (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C CA CB CK : ℝ) (h : Formalism.MainNotions.LiftingTheory.aux₃ D HW F C CA CB CK) :
    Formalism.MainNotions.LiftingTheory.LiftTheoremAllCases D HW F CA CB CK := h.2.2.2.2.2.2.2

end Formalism.MainNotions.N
end
end
