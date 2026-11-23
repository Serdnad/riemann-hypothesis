module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle153
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle123
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle516
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle503
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle519
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastWittLineOfBesselJacobiLatticesGood
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle518
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle483
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle517
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle474
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle016
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LowerBlockParam

variable {D : D7}

theorem val_lev {c : Com D} {s : PiLocalization₂ D} (u : s.CC c) (v : SmT s.M) {κ : GA D s.V}
    (hκ : κ ∈ Lev.levG s.V s.β s.L) (g : GA D s.V) :
    PiLocalization₂.val u v (g * κ) = Lev.levChi s.V s.β s.L κ * PiLocalization₂.val u v g := by
  obtain ⟨T, hT, hu⟩ := u.2
  have hM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T).1 hT
  have hκ' : κ ∈ levS s.V s.β s.L := hκ
  show (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v (g * κ) = _ * (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v g
  rw [← hu]
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe]
    rw [hM.lev f κ hκ' g]; ring
  | add x y hx hy =>
    simp only [map_add (f := _), Pi.add_apply, hx, hy]; ring

theorem chart_fin : ∀ (D : D7) (s : PiLocalization₂ D) (j : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (ι : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) →* GA D s.V), IsChart s j φ ι → ∀ y, ι y ∈ GfC s.V := by
  intro D s j v φ ι hι y
  obtain ⟨ε, -, hy⟩ := hι
  rw [← (hy y).1]
  exact GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC s.V v _

theorem hecke_keeps : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : SplitProj D v), IsProjAt φ PP → ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ ι, IsChart s j φ ι →
    ∀ (ϖ : (Fv D.host.F v)ˣ) (e : Blocks j D.R.t → ℤ) (R : Finset (GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v)))
      (d : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) → (Fv D.host.F v)ˣ),
      GlobalTheory.ParHecke.IsReps (GlobalTheory.ZonalCellDecomposition.mtor ϖ e) R d → ∀ u : s.CC c, ∃ u' : s.CC c, ∀ v',
        PiLocalization₂.val u' v' = fun h => ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * PiLocalization₂.val u v' (h * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ξl hξ ι hι ϖ e R d hR u
  obtain ⟨T, hT, hu⟩ := u.2
  have hM := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T).1 hT
  let T' : MMap s.M := ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) • heckeOn s.M {ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)} T
  have hT'v : ∀ vv h, T' vv h = ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * T vv (h * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) := by
    intro vv h
    simp [T', heckeOn, postOn_apply, heckeLin_apply]
  have h0 : T' ∈ Mult c.θ s.M ∅ (Lev.levChi s.V s.β s.L) := by
    refine Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact GlobalTheory.HeckeParts.isMultMap_heckeOn hM
      (fun a ha => by rw [Finset.mem_singleton] at ha; subst ha; exact chart_fin D s j v φ ι hι _) (fun _ _ hk => hk.elim)
  have h1 := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T').1 h0
  have hIs : IsMultMap c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) T' := by
    refine ⟨h1.aut, h1.cusp, ?_, h1.equiv, h1.cont⟩
    intro vv κ hκ g
    rw [hT'v, hT'v]
    exact GlobalTheory.T.lowerBlockDoubleCosetOperator_keeps_levelCharacter D c w hw j hj s hs PP hPP v φ hφ ξl hξ ι hι ϖ e R d hR (T vv) (fun κ hκ g => hM.lev vv κ hκ g) κ hκ g
  refine ⟨⟨PiTensorProduct.lift T', (mem_multT _ _ _ _ _).2 (by
    rw [LinearEquiv.symm_apply_apply]; exact (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ T').2 hIs)⟩, fun v' => ?_⟩
  funext h
  show PiTensorProduct.lift T' v' h = ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v' (h * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e))
  rw [← hu]
  induction v' using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, PiTensorProduct.lift.tprod, Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe, hT'v, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => by ring
  | add x y hx hy =>
    simp only [map_add (f := _), Pi.add_apply, hx, hy, mul_add, Finset.sum_add_distrib]

theorem qOfVal : ∀ D : D7, SoftQ D → QOfVal D := by
  intro D hS c w hw j hj s hs
  obtain ⟨-, -, hinj, -⟩ := hS c w hw j hj s hs
  have hdict := GlobalTheory.T.splitPlaceChart_parahoric_level_stabiliser_height D c w hw j hj s hs
  have htype : ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ξl,
      LiftsChar φ PP ξl (w.ξ PP) → ∀ ι, IsChart s j φ ι → ∀ y ∈ parahoric (Fv D.host.F v) _ _, ∀ d : (Fv D.host.F v)ˣ,
      (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → ∀ (u : s.CC c) v' g,
        PiLocalization₂.val u v' (g * ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) * PiLocalization₂.val u v' g := by
    intro PP hPP v φ hφ ξl hξ ι hι y hy d hd u v' g
    obtain ⟨-, -, -, -, hch⟩ := hdict PP hPP v φ hφ
    obtain ⟨-, hlev, hchi⟩ := hch ι hι
    rw [val_lev u v' ((hlev y).2 hy) g, hchi ξl hξ y hy d hd]

  have hπ : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ι : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) →* GA D s.V) y
      (F : GA D s.V → ℂ), ((GlobalTheory.PRep.rightReg ℂ (GA D s.V) ℂ).comp ι) y F = fun h => F (h * ι y) := by
    intro v ι y F; rfl
  clear hdict
  refine ⟨?_, ?_⟩
  · intro x v0 hne hQ v' PP hPP v φ hφ xx ϖ hϖ ξl hξ ι hι
    obtain ⟨hty0, hcard, hT0⟩ := hQ PP hPP v φ hφ xx ϖ hϖ ξl hξ ι hι
    clear hQ
    obtain ⟨g0, hg0⟩ := Function.ne_iff.1 hne
    have hunit : ∀ y ∈ parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t), ∀ d : (Fv D.host.F v)ˣ,
        (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → starRingEnd ℂ (((ξl d)⁻¹ : ℂˣ) : ℂ) = ((ξl d : ℂˣ) : ℂ) := by
      intro y hy d hd
      have h1 := congrFun (hty0 y hy d hd) g0
      rw [hπ] at h1
      simp only [Pi.smul_apply, smul_eq_mul] at h1
      rw [htype PP hPP v φ hφ ξl hξ ι hι y hy d hd x v0 g0, map_mul] at h1
      exact mul_right_cancel₀ ((map_ne_zero _).2 hg0) h1
    refine ⟨?_, hcard, ?_⟩
    · intro y hy d hd
      funext h
      rw [hπ]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [htype PP hPP v φ hφ ξl hξ ι hι y hy d hd x v' h, map_mul, hunit y hy d hd]
    · intro S R dd hR
      have e0 := hT0 S R dd hR
      obtain ⟨u', hu'⟩ := hecke_keeps D c w hw j hj s hs PP hPP v φ hφ ξl hξ ι hι ϖ (GlobalTheory.ParHecke.indic S) R dd hR x
      generalize GlobalTheory.ParHecke.genVal _ _ _ _ _ = c0 at e0 ⊢
      have hcoef : ∀ y ∈ R, starRingEnd ℂ ((ξl (dd y) : ℂˣ) : ℂ) = (((ξl (dd y))⁻¹ : ℂˣ) : ℂ) := by
        intro y hy
        rw [← hunit y (hR.1 y hy).1 (dd y) (hR.1 y hy).2, Complex.conj_conj]
      have hv0 : PiLocalization₂.val u' v0 = (starRingEnd ℂ c0) • PiLocalization₂.val x v0 := by
        rw [hu']; funext h
        have := congrArg (starRingEnd ℂ) (congrFun e0 h)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hπ] at this

        simp only [map_sum (starRingEnd ℂ), (starRingEnd ℂ).map_mul, Complex.conj_conj] at this
        rw [Pi.smul_apply, smul_eq_mul, this]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hunit y (hR.1 y hy).1 (dd y) (hR.1 y hy).2]
      have hv0ne : v0 ≠ 0 := by
        rintro rfl; exact hne (by simp [PiLocalization₂.val])
      have heq : u' = (starRingEnd ℂ c0) • x := by
        refine sub_eq_zero.1 (hinj _ v0 hv0ne ?_)
        simp only [PiLocalization₂.val, Submodule.coe_sub, Submodule.coe_smul, LinearMap.sub_apply, LinearMap.smul_apply] at hv0 ⊢
        rw [hv0, sub_self]
      funext h
      have := congrArg (starRingEnd ℂ) (congrFun (hu' v') h)
      rw [heq] at this

      simp only [PiLocalization₂.val, Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, (starRingEnd ℂ).map_mul,
      Complex.conj_conj, map_sum (starRingEnd ℂ)] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hπ]
      refine this.trans (Finset.sum_congr rfl fun y hy => ?_)
      rw [hcoef y hy]
  · intro hj0 x v' PP hPP v φ hφ xx ϖ hϖ ξl hξ ι hι
    subst hj0
    have hE : IsEmpty (Blocks 0 D.R.t) := ⟨fun b => b.1.elim0⟩
    have hd1 : ∀ y : GL (Fin D.R.r ⊕ Blocks 0 D.R.t) (Fv D.host.F v), ∀ d : (Fv D.host.F v)ˣ,
        (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → d = 1 := by
      intro y d hd; ext; rw [hd, Matrix.det_isEmpty]; rfl
    have hty : (fun g => starRingEnd ℂ (PiLocalization₂.val x v' g)) ∈
        GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.typeSpace ((GlobalTheory.PRep.rightReg ℂ (GA D s.V) ℂ).comp ι) ξl := by
      intro y hy d hd
      funext h
      rw [hπ]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [htype PP hPP v φ hφ ξl hξ ι hι y hy d hd x v' h, hd1 y d hd]
      simp
    refine ⟨hty, ?_, ?_⟩
    · show (0 : Multiset ℂˣ).card = _
      simp
    · intro S R dd hR
      have hS0 : S = ∅ := Finset.eq_empty_of_isEmpty S
      subst hS0
      have hfun : (fun i : Fin D.R.r ⊕ Blocks 0 D.R.t => ϖ ^ (Sum.elim (0 : Fin D.R.r → ℤ) (GlobalTheory.ParHecke.indic (∅ : Finset (Blocks 0 D.R.t))) i)) = 1 := by
        funext i
        rcases i with i | i
        · simp
        · exact isEmptyElim i
      have hg : (GlobalTheory.ZonalCellDecomposition.mtor ϖ (GlobalTheory.ParHecke.indic (∅ : Finset (Blocks 0 D.R.t))) :
          GL (Fin D.R.r ⊕ Blocks 0 D.R.t) (Fv D.host.F v)) = 1 := by
        unfold GlobalTheory.ZonalCellDecomposition.mtor GlobalTheory.GLDoubling.torusElt
        rw [hfun, map_one]
      rw [hg] at hR ⊢
      obtain ⟨j0, ⟨hj0R, -⟩, huniq⟩ := hR.2 1 (one_mem _)
      have hRs : R = {j0} := by
        ext y; simp only [Finset.mem_singleton]; constructor
        · intro hy; exact huniq y ⟨hy, by simpa using inv_mem (hR.1 y hy).1⟩
        · rintro rfl; exact hj0R
      subst hRs
      rw [Finset.sum_singleton, mul_one, hty j0 (hR.1 j0 hj0R).1 (dd j0) (hR.1 j0 hj0R).2, smul_smul]
      have hq : qPar c PP xx 0 = 0 := rfl
      simp [GlobalTheory.ParHecke.genVal, hq, Multiset.esymm]

end GlobalTheory.LowerBlockParam
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw

theorem restore_holds : ∀ D : D7, Restore D := by
  intro D _ c w hw k hk s s' hs hs' _ _
  obtain ⟨hr, -, hfl⟩ := hs
  obtain ⟨hr', -, hfl'⟩ := hs'
  have h1 : s.V.rank = D.R.rankY k := hfl.rank
  have h2 : s'.V.rank = D.R.rankY k + D.R.t := by
    have h : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    rw [h]; simp only [Formalism.BasicNotions.Ranks.rankY]; ring
  have h3 : D.R.rankY k + D.R.t = D.R.r + (k + 1) * D.R.t := by
    simp only [Formalism.BasicNotions.Ranks.rankY]; ring
  obtain ⟨hL, hL₀⟩ := GlobalTheory.T.twistEulerFactors_restore_quotientLValues D c w hw k hk
  obtain ⟨hd0, hd⟩ := GlobalTheory.T.twistEulerFactors_restore_normalizingFactor D c w hw (D.R.rankY k)
  refine ⟨hL, hL₀, ?_, ?_⟩
  · unfold dS; rw [h1, h2]; exact hd0
  · unfold dS; rw [h1, h2, hd, h3]

end GlobalTheory.ChainTw
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem transvTrivial_of_descent (D : D7) (hD : Descent D) : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvTrivial D := by
  intro S S₀ T ρ d ψ χS χT om hom μ 𝓕 hμ a v hv u hu x hx f hf
  obtain ⟨om₀, hom₀⟩ := (hD ψ S T χS χT om hom).1 S₀ ρ d
  obtain ⟨m, b, c, rfl, hdet, hk⟩ := GlobalTheory.T.unitaryTransvection_eq_leviUnipotentProduct D S S₀ ρ d _ v hv u hu
  obtain ⟨h1, h2, h3⟩ := hk T x hx
  have F := fun g hg => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ S S₀ T ρ d χS χT om om₀ hom hom₀ μ 𝓕 hμ g hg
  have hc := hom.om_pres (d.nC c, 1) f hf
  have hb := hom.om_pres (d.nB b, 1) _ hc
  have e : om (d.levi m * d.nB b * d.nC c, 1) f = om (d.levi m, 1) (om (d.nB b, 1) (om (d.nC c, 1) f)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      mul_one, mul_one]
  have hq : symplOH S T (d.extX T x) (d.extY T (x ⬝ c.1)) = 0 := h3
  rw [e]
  change I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d T ψ μ 𝓕 _ x = I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d T ψ μ 𝓕 f x
  rw [(F _ hb).levi, h1, (F _ hc).unip, h2, GlobalTheory.MixPer.heisO_zero, (F _ hf).centre, hq, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet]
  simp

theorem transvLemma_of_descent : ∀ D : D7, Descent D → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvLemma D := fun D hD =>
  ⟨(GlobalTheory.T.unitaryTransvection_unitary_and_conjugation D).1, (GlobalTheory.T.unitaryTransvection_unitary_and_conjugation D).2, transvTrivial_of_descent D hD⟩

end GlobalTheory.Unf
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.doubleStep_eq_two_thetaColumnLifts : ∀ D : D7, ContrLaw D := by
  first | exact @GlobalTheory.Unf.Contr.contrLaw | exact GlobalTheory.Unf.Contr.contrLaw | (intros; apply GlobalTheory.Unf.Contr.contrLaw <;> assumption)
end

section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inv_diag_torus_integral_besselJacobi_unramified : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.InvStep.inv_int | exact GlobalTheory.FinPl.InvStep.inv_int | (intros; apply GlobalTheory.FinPl.InvStep.inv_int <;> assumption)
end
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.smallPairPairingAllGluedPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.SmallAll D := by
  first | exact @GlobalTheory.FinPl.SmallAllPf.main | exact GlobalTheory.FinPl.SmallAllPf.main | (intros; apply GlobalTheory.FinPl.SmallAllPf.main <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.doubleStepSmallPairsValueAllGluedSplitPlaces_proof : ∀ D : D7, GlobalTheory.FinPl.VertexAll D := by
  first | exact @GlobalTheory.FinPl.vertexAll | exact GlobalTheory.FinPl.vertexAll | (intros; apply GlobalTheory.FinPl.vertexAll <;> assumption)
end

section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.seeSawLatticeShapeExists_proof : ∀ D : D7, GlobalTheory.SeeSaw.ShapeEx D := by
  first | exact @GlobalTheory.SeeSaw.ShapeExProof.shapeEx | exact GlobalTheory.SeeSaw.ShapeExProof.shapeEx | (intros; apply GlobalTheory.SeeSaw.ShapeExProof.shapeEx <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

theorem _root_.GlobalTheory.T.unramifiedThetaCorrespondence_all_goodPrimes : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, UnrCorr R i t (fun _ => True) := by
  first | exact @GlobalTheory.UnrAll.unrCorr_all | exact GlobalTheory.UnrAll.unrCorr_all | (intros; apply GlobalTheory.UnrAll.unrCorr_all <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaInnerProductFormulaDefinite_of_rallisConvergent : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.Convergent D → (∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)) → InnerProductFormulaC R F := by
  first | exact @GlobalTheory.IPFConv.innerProductFormulaC_of_convergent | exact GlobalTheory.IPFConv.innerProductFormulaC_of_convergent | (intros; apply GlobalTheory.IPFConv.innerProductFormulaC_of_convergent <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.lastWittLine_of_besselJacobiLatticesGood : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : GlobalTheory.FinPl.Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → LastAt ψ B.d (vecB B.o B.ζ) LV LV₀ v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.lastAt_of_goodBF | exact GlobalTheory.Core.Mi.LatMatch.lastAt_of_goodBF | (intros; apply GlobalTheory.Core.Mi.LatMatch.lastAt_of_goodBF <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Fam.goodBF_of_normalFrames : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), ∀ j ρ h, GlobalTheory.FinPl.GoodBF (commOf (pk W) u (mkGeo m b₀)).ψ ((commOf (pk W) u (mkGeo m b₀)).B j ρ h) ((commOf (pk W) u (mkGeo m b₀)).J j ρ h) (N₁ j) (M₁ j ρ h) (N₁ (j + 1)) ((commOf (pk W) u (mkGeo m b₀)).x (j + 1)).L ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hgram hτ hNT hζ hSD hgP htP hdisj hPre hOrth hbas FY sc hNF N₁ M₁ hN₁ hFY hM₁ hcore PP hP j ρ h
  have hx : ∀ j, j ≤ D.R.m → (a.x j).Is := fun j hj => hIs.x j hj
  exact ⟨GlobalTheory.FinPl.TamePlaces.tame D _, hN₁ j (by omega), hM₁ j ρ h, hN₁ (j + 1) (by omega), (hIs.x (j + 1) (by omega)).sd,
    GlobalTheory.T.besselLattice_splits_along_witt_normalFrames _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.fourierJacobiLattice_splits_at_normalFrame_place _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.besselPeriodCharacter_primitive_normalFrames _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.besselToJacobiMap_carries_normalFrameLines _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.normalFrame_place_yZero_primitive_in_hom_lattice _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h⟩
end
