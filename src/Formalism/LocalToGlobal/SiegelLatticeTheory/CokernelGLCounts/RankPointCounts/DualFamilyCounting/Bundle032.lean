module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle028
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlgebraMapIntCastSmul
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle032
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle041
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InvMemLocROfUnimod
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle011
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle005
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle001

@[expose] public section

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev CBlk (r : ℕ) : Type := (LsNc5.LtPair r ⊕ Fin r) ⊕ (LsNc5.LtPair r ⊕ Fin r)

def CSpc (ι : Type) (k : ℕ) {r : ℕ} : CBlk r → Type
  | Sum.inl (Sum.inl _) => ι → ℂ
  | Sum.inl (Sum.inr _) => ι → Fin (k + 1) → ℂ
  | Sum.inr (Sum.inl _) => ι → ℂ
  | Sum.inr (Sum.inr _) => ι → ℝ

section Inst

variable (ι : Type) [Fintype ι] (k : ℕ) {r : ℕ}

instance instAddCommGroupCSpc : ∀ p : CBlk r, AddCommGroup (CSpc ι k p)
  | Sum.inl (Sum.inl _) => inferInstanceAs (AddCommGroup (ι → ℂ))
  | Sum.inl (Sum.inr _) => inferInstanceAs (AddCommGroup (ι → Fin (k + 1) → ℂ))
  | Sum.inr (Sum.inl _) => inferInstanceAs (AddCommGroup (ι → ℂ))
  | Sum.inr (Sum.inr _) => inferInstanceAs (AddCommGroup (ι → ℝ))

instance instMeasurableSpaceCSpc : ∀ p : CBlk r, MeasurableSpace (CSpc ι k p)
  | Sum.inl (Sum.inl _) => inferInstanceAs (MeasurableSpace (ι → ℂ))
  | Sum.inl (Sum.inr _) => inferInstanceAs (MeasurableSpace (ι → Fin (k + 1) → ℂ))
  | Sum.inr (Sum.inl _) => inferInstanceAs (MeasurableSpace (ι → ℂ))
  | Sum.inr (Sum.inr _) => inferInstanceAs (MeasurableSpace (ι → ℝ))

instance instMeasurableAdd₂CSpc : ∀ p : CBlk r, MeasurableAdd₂ (CSpc ι k p)
  | Sum.inl (Sum.inl _) => inferInstanceAs (MeasurableAdd₂ (ι → ℂ))
  | Sum.inl (Sum.inr _) => inferInstanceAs (MeasurableAdd₂ (ι → Fin (k + 1) → ℂ))
  | Sum.inr (Sum.inl _) => inferInstanceAs (MeasurableAdd₂ (ι → ℂ))
  | Sum.inr (Sum.inr _) => inferInstanceAs (MeasurableAdd₂ (ι → ℝ))

def cMeas : ∀ p : CBlk r, Measure (CSpc ι k p)
  | Sum.inl (Sum.inl _) => (volume : Measure (ι → ℂ))
  | Sum.inl (Sum.inr _) => (volume : Measure (ι → Fin (k + 1) → ℂ))
  | Sum.inr (Sum.inl _) => (volume : Measure (ι → ℂ))
  | Sum.inr (Sum.inr _) => (volume : Measure (ι → ℝ))

instance instSigmaFiniteCMeas : ∀ p : CBlk r, SigmaFinite (cMeas ι k p)
  | Sum.inl (Sum.inl _) => inferInstanceAs (SigmaFinite (volume : Measure (ι → ℂ)))
  | Sum.inl (Sum.inr _) => inferInstanceAs (SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)))
  | Sum.inr (Sum.inl _) => inferInstanceAs (SigmaFinite (volume : Measure (ι → ℂ)))
  | Sum.inr (Sum.inr _) => inferInstanceAs (SigmaFinite (volume : Measure (ι → ℝ)))

instance instRightInvCMeas : ∀ p : CBlk r, (cMeas ι k p).IsAddRightInvariant
  | Sum.inl (Sum.inl _) => inferInstanceAs ((volume : Measure (ι → ℂ)).IsAddRightInvariant)
  | Sum.inl (Sum.inr _) => inferInstanceAs ((volume : Measure (ι → Fin (k + 1) → ℂ)).IsAddRightInvariant)
  | Sum.inr (Sum.inl _) => inferInstanceAs ((volume : Measure (ι → ℂ)).IsAddRightInvariant)
  | Sum.inr (Sum.inr _) => inferInstanceAs ((volume : Measure (ι → ℝ)).IsAddRightInvariant)

end Inst

def cHgt {r : ℕ} : CBlk r → ℕ
  | Sum.inl (Sum.inl p) => p.1.2.val - p.1.1.val
  | Sum.inl (Sum.inr b) => r + (r - b.val)
  | Sum.inr (Sum.inl p) => 2 * r + 1 + (2 * r - (p.1.1.val + p.1.2.val))
  | Sum.inr (Sum.inr a) => 2 * r + 1 + (2 * r - 2 * a.val)

section HidaSetting

variable {D : D7} (X : HidaSetting D)

def blk (u : D.what₂.Word) (s : X.B.I.Ginf) :
    ∀ p : CBlk D.R.rS, CSpc (InfinitePlace X.B.I.F) D.R.k p
  | Sum.inl (Sum.inl p) => fun v => LsNc5.xMat X v s p.1.1 p.1.2
  | Sum.inl (Sum.inr b) => fun v j =>
      if h : j.val < D.R.k then LsNc5.phiMat X u v s b ⟨j.val, h⟩ else LsNc5.yVec X u v s b
  | Sum.inr (Sum.inl p) => fun v => (LsNc5.mMat X v s p.1.1 p.1.2 - star (LsNc5.mMat X v s p.1.2 p.1.1)) / 2
  | Sum.inr (Sum.inr a) => fun v => (LsNc5.mMat X v s a a).im

def embV (t : D.host.E) : InfinitePlace X.B.I.F → ℂ := fun v => embS D (X.pl v) t

def rowV (u : D.what₂.Word) (x : (VS D).V) : InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ := fun v j =>
  if h : j.val < D.R.k then hJ (X.B.I.ε v) (rv X.B.I v (X.crd x)) (X.wfr u v ⟨j.val, h⟩)
  else hJ (X.B.I.ε v) (rv X.B.I v (X.crd x)) (rv X.B.I v (X.zR u))

def aaLb (b : Fin D.R.rS) : Set (VS D).V :=
  (Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l} : Set (VS D).V)

def cLat (u : D.what₂.Word) : ∀ p : CBlk D.R.rS, AddSubgroup (CSpc (InfinitePlace X.B.I.F) D.R.k p)
  | Sum.inl (Sum.inl p) => AddSubgroup.closure (embV X '' ((aaD D p.1.1 * (aaD D p.1.2)⁻¹ :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E))
  | Sum.inl (Sum.inr b) => AddSubgroup.closure (rowV X u '' aaLb X b)
  | Sum.inr (Sum.inl p) => AddSubgroup.closure (embV X '' ((aaD D p.1.1 * aaD D p.1.2 :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E))
  | Sum.inr (Sum.inr a) => AddSubgroup.closure ((fun t v => (embS D (X.pl v) t).im) ''
      {t | t ∈ ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ∧
        D.host.conj t = -t})

def cVal (u : D.what₂.Word) : CBlk D.R.rS → ℝ
  | Sum.inl (Sum.inl p) => (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((p.1.2 : ℕ) - (p.1.1 : ℕ) : ℝ))
  | Sum.inl (Sum.inr b) => Tw u ^ Fintype.card (InfinitePlace X.B.I.F) *
      (2 : ℝ)⁻¹ ^ (Fintype.card (InfinitePlace X.B.I.F) * (D.R.k + 1)) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - (b : ℕ))))
  | Sum.inr (Sum.inl p) => (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((D.R.rS : ℝ) - (p.1.1 : ℕ)) - 2 * ((D.R.rS : ℝ) - (p.1.2 : ℕ)))
  | Sum.inr (Sum.inr a) => |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - (a : ℕ)))

end HidaSetting

def KapLaw : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word), ∃ B : ∀ p : CBlk D.R.rS,
      (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) →
        CSpc (InfinitePlace X.B.I.F) D.R.k p,
    (∀ p, Measurable (fun z : (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) ×
      (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) => B p z.1 z.2)) ∧
    (∀ p (x x' y y' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q),
      (∀ q, cHgt q < cHgt p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y') ∧
    (∀ p (x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q), B p x 0 = 0) ∧
    ∀ s ∈ X.NinfU u, ∀ s' ∈ X.NinfU u, blk X u (s * s') = Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B (blk X u s) (blk X u s')

def KapSurj : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word), ∃ σ : (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → X.B.I.Ginf,
    Measurable σ ∧ ∀ t, σ t ∈ X.NinfU u ∧ blk X u (σ t) = t

def NOfib : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ⊆ X.NinfU u ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      δ * δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, δ⁻¹ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    ∃ τ : ∀ p : CBlk D.R.rS, (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → CSpc (InfinitePlace X.B.I.F) D.R.k p,
      (∀ p (x x' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q), (∀ q, cHgt q < cHgt p → x q = x' q) → τ p x = τ p x') ∧
      ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
        x ∈ blk X u '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔ ∀ p, x p - τ p x ∈ cLat X u p

def BlockCovol : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (p : CBlk D.R.rS),
    Countable (cLat X u p) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k p), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u p, (a : CSpc (InfinitePlace X.B.I.F) D.R.k p) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k p), MeasurableSet F →
      (∀ v, ∃! a : cLat X u p, (a : CSpc (InfinitePlace X.B.I.F) D.R.k p) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k p F = ENNReal.ofReal (cVal X u p)

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FrameRow : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u w : D.what₂.Word) (v : InfinitePlace X.B.I.F),
    ∃ L : (LsNc5.CIdx D.R.rS D.R.k → ℝ) →ₗ[ℝ] (LsNc5.CIdx D.R.rS D.R.k → ℝ),
      (∀ s : X.B.I.Ginf, (fun i => LsNc5.kapV X w v s i) = L (fun i => LsNc5.kapV X u v s i)) ∧
      |LinearMap.det L| = (Tw w / Tw u) ^ D.R.rS

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem isLatIn_cut {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsFullLattice K Λ) (X : Submodule K V) :
    IsLatIn X (Λ ⊓ X.restrictScalars (𝓞 K)) := by
  refine ⟨?_, le_antisymm (Submodule.span_le.mpr fun x hx => hx.2) fun x hx => ?_⟩
  · have := isNoetherian_of_fg_of_noetherian _ hΛ.fg
    exact Submodule.FG.of_le_of_isNoetherian (inf_le_left : Λ ⊓ X.restrictScalars (𝓞 K) ≤ Λ)
  · obtain ⟨r, hr, hrx⟩ := StabilizerLattices.exists_smul_mem hΛ x
    have h1 : r • x ∈ Λ ⊓ X.restrictScalars (𝓞 K) := ⟨hrx, (X.restrictScalars (𝓞 K)).smul_mem r hx⟩
    have hr' : algebraMap (𝓞 K) K r ≠ 0 := by simpa using hr
    have e : x = (algebraMap (𝓞 K) K r)⁻¹ • (r • x) := by
      rw [← algebraMap_smul K r x, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem nondegenerate_of {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h) :
    h.Nondegenerate := by
  constructor
  · exact hnd
  · intro y hy
    refine hnd y fun x => ?_
    rw [← hs.eq x y, hy x, map_zero]

theorem finite_fibS (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    (fibS h U 𝔭 M T).Finite := by
  have hp := h𝔭.isPrime
  have hN := isLattice_sup hUc hM hT
  have hNfull : Submodule.IsFullLattice K (M ⊔ T) := by
    refine { toIsLattice := hN, span_eq_top := ?_ }
    apply top_unique
    rw [← hUc.sup_eq_top]
    refine sup_le ?_ ?_
    · rw [← hM.2]
      exact Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_left)
    · rw [← hT.2]
      exact Submodule.span_mono (SetLike.coe_subset_coe.mpr le_sup_right)
  letI := hNfull
  letI hDfull : Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) :=
    (Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs (nondegenerate_of hs hnd) Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range _ hNfull).1
  have hD := hDfull.toIsLattice
  have hND : Submodule.IsFullLattice K ((M ⊔ T) ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) := inferInstance
  have key : ∀ Λ ∈ fibS h U 𝔭 M T, locF 𝔭 (M ⊔ T) ≤ Λ ∧ Λ ≤ locF 𝔭 (Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) ∧
      locF 𝔭 Λ = Λ := by
    rintro Λ ⟨⟨Λ', -, rfl⟩, h1, h2, h3⟩
    have hle : locF 𝔭 (M ⊔ T) ≤ locF 𝔭 Λ' := by
      have hs' : M ⊔ T ≤ locF 𝔭 Λ' := sup_le
        ((LocF.le_locF 𝔭 M).trans (h2 ▸ inf_le_left)) ((LocF.le_locF 𝔭 T).trans (h3 ▸ inf_le_left))
      exact (LocF.locF_mono 𝔭 hs').trans (LocF.locF_idem 𝔭 Λ').le
    refine ⟨hle, ?_, LocF.locF_idem 𝔭 Λ'⟩
    rw [G7.locF_dual hF h hN.fg hp]
    calc locF 𝔭 Λ' = dualF h 𝔭 (locF 𝔭 Λ') := h1.symm
      _ ≤ dualF h 𝔭 (locF 𝔭 (M ⊔ T)) := dualF_anti h 𝔭 hle
  refine Set.Finite.of_finite_image (f := fun Λ => Λ ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T))
    ((BrB.finite_between hND hD inf_le_right).subset ?_) ?_
  · rintro _ ⟨Λ, hΛ, rfl⟩
    obtain ⟨k1, -, -⟩ := key Λ hΛ
    exact ⟨inf_le_inf_right _ ((LocF.le_locF 𝔭 _).trans k1), inf_le_right⟩
  · intro Λ₁ h1 Λ₂ h2 he
    obtain ⟨-, a1, b1⟩ := key Λ₁ h1
    obtain ⟨-, a2, b2⟩ := key Λ₂ h2
    have e1 : locF 𝔭 (Λ₁ ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) = Λ₁ := by
      rw [LIOrb.locF_inf_locF h𝔭, b1]; exact inf_eq_left.2 a1
    have e2 : locF 𝔭 (Λ₂ ⊓ Formalism.HermitianLatticesTheory.dual h (M ⊔ T)) = Λ₂ := by
      rw [LIOrb.locF_inf_locF h𝔭, b2]; exact inf_eq_left.2 a2
    rw [← e1, ← e2]
    exact congrArg (locF 𝔭) he

theorem fibP_ne_zero_iff (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M T : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    fibP h U 𝔭 M T ≠ 0 ↔ (fibS h U 𝔭 M T).Nonempty := by
  have hfin := finite_fibS hF hs hnd hUc hM hT h𝔭
  rw [fibP_eq, Nat.card_ne_zero]
  constructor
  · rintro ⟨⟨x, hx⟩, -⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨⟨x, hx⟩⟩, hfin.to_subtype⟩

theorem fibP_congr (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M : Submodule (𝓞 K) V)
    {T T' : Submodule (𝓞 K) V} (e : locF 𝔭 T = locF 𝔭 T') : fibP h U 𝔭 M T = fibP h U 𝔭 M T' := by
  unfold fibP
  rw [e]

theorem fibP_ne_zero_of_genus (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hnd : Nondeg h) {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M : Submodule (𝓞 K) V}
    (hM : IsLatIn U M) {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M) {T : Submodule (𝓞 K) V}
    (hg : SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) T)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : fibP h U 𝔭 M T ≠ 0 := by
  obtain ⟨g, hg, he⟩ := hg 𝔭 h𝔭
  have hΛ₀full : Submodule.IsFullLattice K Λ₀ :=
    { toIsLattice := hΛ₀.1, span_eq_top :=
      GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs (nondegenerate_of hs hnd) hΛ₀.1 hΛ₀.2.1 }
  have hT₀ := isLatIn_cut hΛ₀full (orthK h U)
  rw [← fibP_congr h U 𝔭 M (show locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K))) = locF 𝔭 T
      by rw [← LocalizedFibreSets.gmap_locF, he]), G6.fibP_gmap hM 𝔭 _ hg,
    fibP_ne_zero_iff hF hs hnd hUc hM hT₀ h𝔭]
  exact ⟨_, locF_mem_fibS hF hΛ₀.1 hΛ₀.2.1 hΛ₀.2.2 rfl h𝔭⟩

end Formalism.L2.SG.Pf.G8
end
end
