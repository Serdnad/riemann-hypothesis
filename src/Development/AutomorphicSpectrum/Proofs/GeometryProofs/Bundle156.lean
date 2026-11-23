module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle145
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle021
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle147
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProject
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
public import Development.WeilBound.CoreStatements.AmpleLineBundles.Bundle001
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogX
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087

@[expose] public section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.projective_over_coords_exist : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (X : Scheme.{0}) (s : X ⟶ Sp o), IsProjOver s → ∀ (Ω : Type) [Field Ω] [Algebra o Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ξ ≫ s = spMap (algebraMap o Ω) → ∃ (n : ℕ) (x : Fin n → Ω), CoordTie o ξ x := by
  first | exact @GlobalTheory.CompanionTheory.Relay.projective_over_coords_exist | exact GlobalTheory.CompanionTheory.Relay.projective_over_coords_exist | (intros; apply GlobalTheory.CompanionTheory.Relay.projective_over_coords_exist <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht.ALine

section Cross

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Cmp

variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type}
  [∀ k, Fintype (ι₁ k)] [∀ k, Fintype (ι₂ k)] {Ω : Type} [Field Ω]

theorem cross_mem (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (a₁ b₁ : ι₁ k₁) (a₂ b₂ : ι₂ k₂)
    (h : y₁ ⟨k₁, a₁⟩ * y₂ ⟨k₂, b₂⟩ = y₁ ⟨k₁, b₁⟩ * y₂ ⟨k₂, a₂⟩) :
    (X (joinInl ι₁ ι₂ ⟨k₁, a₁⟩) * X (joinInr ι₁ ι₂ ⟨k₂, b₂⟩) +
        -(X (joinInl ι₁ ι₂ ⟨k₁, b₁⟩) * X (joinInr ι₁ ι₂ ⟨k₂, a₂⟩)) : MRing (joinIdx ι₁ ι₂)) ∈
      mCoordIdeal (joinVec y₁ y₂) := by
  classical
  have hl : ∀ a : ι₁ k₁, IsMultiHomog (X (joinInl ι₁ ι₂ ⟨k₁, a⟩) : MRing (joinIdx ι₁ ι₂))
      (Pi.single (Sum.inl k₁) 1) := fun a => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inl k₁) a
  have hr : ∀ a : ι₂ k₂, IsMultiHomog (X (joinInr ι₁ ι₂ ⟨k₂, a⟩) : MRing (joinIdx ι₁ ι₂))
      (Pi.single (Sum.inr k₂) 1) := fun a => ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inr k₂) a
  refine Small.LineModel.mem_of_aeval _
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhAdd (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhMul (hl a₁) (hr b₂))
      (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhNeg (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhMul (hl b₁) (hr a₂)))) ?_
  simp only [map_add (f := _), map_neg, map_mul, aeval_X]
  show y₁ ⟨k₁, a₁⟩ * y₂ ⟨k₂, b₂⟩ + -(y₁ ⟨k₁, b₁⟩ * y₂ ⟨k₂, a₂⟩) = 0
  rw [h]; ring

theorem cross_eq (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (a₁ b₁ : ι₁ k₁) (a₂ b₂ : ι₂ k₂)
    (h : y₁ ⟨k₁, a₁⟩ * y₂ ⟨k₂, b₂⟩ = y₁ ⟨k₁, b₁⟩ * y₂ ⟨k₂, a₂⟩)
    {L : Type} [Field L] {z : (Σ k, joinIdx ι₁ ι₂ k) → L}
    (hz : z ∈ Small.ptsOver L (mCoordIdeal (joinVec y₁ y₂))) :
    z (joinInl ι₁ ι₂ ⟨k₁, a₁⟩) * z (joinInr ι₁ ι₂ ⟨k₂, b₂⟩) =
      z (joinInl ι₁ ι₂ ⟨k₁, b₁⟩) * z (joinInr ι₁ ι₂ ⟨k₂, a₂⟩) := by
  have h0 := hz.2 _ (cross_mem y₁ y₂ a₁ b₁ a₂ b₂ h)
  simp only [map_add (f := _), map_neg, map_mul, aeval_X] at h0
  linear_combination h0

theorem hasVal_one (y₁ : (Σ k, ι₁ k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {k₁ : K₁} {k₂ : K₂}
    (a₁ : ι₁ k₁) (a₂ : ι₂ k₂) (h : y₁ ⟨k₁, a₁⟩ = y₂ ⟨k₂, a₂⟩)
    (d : K₁ ⊕ K₂ → ℤ) (hd₁ : d (Sum.inl k₁) = 1) (hd₂ : d (Sum.inr k₂) = -1)
    (hd : ∀ k, k ≠ Sum.inl k₁ → k ≠ Sum.inr k₂ → d k = 0)
    {L : Type} [Field L] (z : (Σ k, joinIdx ι₁ ι₂ k) → L)
    (hz : z (joinInr ι₁ ι₂ ⟨k₂, a₂⟩) ≠ 0) :
    Small.HasVal (joinVec y₁ y₂) d 1 z
      (z (joinInl ι₁ ι₂ ⟨k₁, a₁⟩) / z (joinInr ι₁ ι₂ ⟨k₂, a₂⟩)) := by
  classical
  refine ⟨Pi.single (Sum.inl k₁) 1, Pi.single (Sum.inr k₂) 1, X (joinInl ι₁ ι₂ ⟨k₁, a₁⟩),
    X (joinInr ι₁ ι₂ ⟨k₂, a₂⟩), ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inl k₁) a₁,
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_X' (ι := joinIdx ι₁ ι₂) (Sum.inr k₂) a₂, fun k => ?_, ?_, ?_, ?_⟩
  · by_cases e₁ : k = Sum.inl k₁
    · subst e₁; simp [hd₁]
    · by_cases e₂ : k = Sum.inr k₂
      · subst e₂; simp [hd₂]
      · simp [hd k e₁ e₂, e₁, e₂]
  · simp only [aeval_X, one_mul]
    exact h
  · simpa only [aeval_X] using hz
  · simp only [aeval_X]
    field_simp

end Cross

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 ∧ ∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), ∀ v : ℂ, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 w v → M.A.h (fun p => w (Cmp.joinInl M.ι R.ι p)) = ‖v‖ * R.A.h (fun p => w (Cmp.joinInr M.ι R.ι p)) := by
  intro E _ _ _ H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi
  classical
  have hy : ∀ a, M.y ⟨o.k₀, o.ix a⟩ = i (R.y ⟨o₀.k₀, o₀.ix a⟩) := fun a => by
    rw [o.y_eq, o₀.y_eq, ← hi]; rfl
  have hd₁ : Ht.joinDeg M R none (Sum.inl o.k₀) = 1 := o.A_deg.1
  have hd₂ : Ht.joinDeg M R none (Sum.inr o₀.k₀) = -1 := by
    show -(R.A.a o₀.k₀) = -1
    rw [o₀.A_deg.1]
  have hd : ∀ k, k ≠ Sum.inl o.k₀ → k ≠ Sum.inr o₀.k₀ → Ht.joinDeg M R none k = 0 := by
    rintro (k | k) h₁ h₂
    · exact o.A_deg.2 k fun e => h₁ (congrArg _ e)
    · show -(R.A.a k) = 0
      rw [o₀.A_deg.2 k fun e => h₂ (congrArg _ e), neg_zero]
  have hval : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L) (a : Fin (Fx.m + 1)),
      z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) ≠ 0 →
      Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R none) 1 z
        (z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) / z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩)) :=
    fun L _ z a hz => hasVal_one M.y (fun p => i (R.y p)) (o.ix a) (o₀.ix a) (hy a) _ hd₁ hd₂ hd z hz
  have hcr : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) → ∀ a b : Fin (Fx.m + 1),
      z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) * z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b⟩) =
        z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b⟩) * z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) :=
    fun L _ z hz a b => cross_eq M.y (fun p => i (R.y p)) (o.ix a) (o.ix b) (o₀.ix a) (o₀.ix b) (by
      show M.y _ * i (R.y _) = M.y _ * i (R.y _)
      rw [hy a, hy b, mul_comm]) hz
  have hexR : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) →
      ∃ a : Fin (Fx.m + 1), z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) ≠ 0 := by
    intro L _ z hz
    obtain ⟨p, hp⟩ := hz.1 (Sum.inr o₀.k₀)
    have e : o₀.ix (o₀.ix.symm p) = p := o₀.ix.apply_symm_apply p
    exact ⟨o₀.ix.symm p, fun h0 =>
      hp ((congrArg (fun x : R.ι o₀.k₀ => z ⟨Sum.inr o₀.k₀, x⟩) e.symm).trans h0)⟩
  have hexM : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) →
      ∃ a : Fin (Fx.m + 1), z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) ≠ 0 := by
    intro L _ z hz
    obtain ⟨p, hp⟩ := hz.1 (Sum.inl o.k₀)
    have e : o.ix (o.ix.symm p) = p := o.ix.apply_symm_apply p
    exact ⟨o.ix.symm p, fun h0 =>
      hp ((congrArg (fun x : M.ι o.k₀ => z ⟨Sum.inl o.k₀, x⟩) e.symm).trans h0)⟩
  have hne : ∀ (L : Type) [Field L] (z : (Σ k, Cmp.joinIdx M.ι R.ι k) → L),
      z ∈ Small.ptsOver L (mCoordIdeal (Ht.joinOf M R i)) → ∀ a : Fin (Fx.m + 1),
      z (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) ≠ 0 → z (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) ≠ 0 := by
    intro L _ z hz a ha h0
    obtain ⟨b, hb⟩ := hexM L z hz
    have h1 := hcr L z hz b a
    rw [h0, zero_mul] at h1
    exact mul_ne_zero hb ha h1
  refine ⟨fun L _ _ z hz => ?_, fun w hw v hv => ?_⟩
  · obtain ⟨a, ha⟩ := hexR L z hz
    exact ⟨_, div_ne_zero (hne L z hz a ha) ha, hval L z a ha⟩
  · obtain ⟨a, ha⟩ := hexR ℂ w hw
    have hv' := Small.LineModel.hasVal_unique _ _ _ hw hv (hval ℂ w a ha)
    have hvne : v ≠ 0 := hv' ▸ div_ne_zero (hne ℂ w hw a ha) ha
    have hblock : ∀ b : Fin (Fx.m + 1), w (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b⟩) =
        v * w (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b⟩) := by
      intro b
      rw [hv', div_mul_eq_mul_div, eq_div_iff ha]
      exact hcr ℂ w hw b a
    obtain ⟨h1, h2⟩ := (GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts.main (CMType H) (D.p + D.q) M R i).2.2.1 ℂ w hw
    rw [Small.LineModel.ptsOver_complex] at h1 h2
    let c : R.K → ℂ := fun k => if k = o₀.k₀ then v else 1
    have hc : ∀ k, c k ≠ 0 := by
      intro k
      by_cases hk : k = o₀.k₀
      · simpa [c, hk] using hvne
      · simp [c, hk]
    have e1 := o.A_h _ h1
    have e2 := o₀.A_h _ (mcPts_smul R.arith.2.1.2.1 c hc h2)
    have e3 := R.A.smul c (fun p => w (Cmp.joinInr M.ι R.ι p)) hc
    have e4 : (∏ k, ‖c k‖ ^ R.A.a k) = ‖v‖ := by
      rw [Finset.prod_eq_single o₀.k₀]
      · simp [c, o₀.A_deg.1]
      · intro k _ hk
        simp [c, hk, o₀.A_deg.2 k hk]
      · simp
    rw [e1, ← e4, ← e3, e2]
    congr 1
    funext b
    simpa [c] using hblock b

end GlobalTheory.CompanionTheory.Ar.Ht.ALine
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht

theorem lineHt_map_scale : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (L : Type) [Field L] [NumberField L] (L' : Type) [Field L'] [NumberField L'] (e : L →+* L') (w : (Σ k, ι k) → L) (c : K → L'), (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ k, c k ≠ 0) → lineHt A L' (fun p => c p.1 * e (w p)) = lineHt A L w :=
  @CoverDenseAlt.lineHt_invariant_base_change_scaling

end GlobalTheory.CompanionTheory.Ar.Ht
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem _root_.GlobalTheory.T.period_eigen_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σK : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σK ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.X) (χ : 𝓞 E →+* ℂ) (τ : E →+* ℂ) (n : ℕ) (v : Fin n → (epsAt x ⟶ Xo.univ.t.G)), IsPeriod (FU.Di i) ty P → x = FU.u i P → (∀ a : 𝓞 E, χ a = τ (a : E)) → IsEigFrame Xo.univ.t.act x χ v → ∃ V : Fin n → Fin g → ℂ, (∀ a u, IsDerivAt0 (fun z => (FU.ex i P z).left) u (v a).left ↔ u = V a) ∧ LinearIndependent ℂ V ∧ ∀ z, tyPart ty τ z ∈ Submodule.span ℂ (Set.range V) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_directions_of_isEigFrame <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SabModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isPrincipal_dim {K : Type} [Field K] {t : SAB H (Sp K)} (_h : IsPrincipal t) :
    ∃ d, SmoothOfRelativeDimension d t.G.hom := by
  letI := t.grp
  haveI hs : IsSemiAbelian t.G := t.semi
  haveI : Smooth t.G.hom := hs.smooth
  haveI : GeometricallyConnected t.G.hom := hs.geomConnected
  have hc := t.G.hom.isConnected_preimage_singleton (IsLocalRing.closedPoint K)
  have hu : t.G.hom ⁻¹' {IsLocalRing.closedPoint K} = Set.univ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  haveI : PreconnectedSpace t.G.left := ⟨by rw [← hu]; exact hc.isPreconnected⟩
  exact exists_dim_of_preconnected t.G.hom hc.nonempty.some

def pol {K : Type} [Field K] (t : SAB H (Sp K)) (h : IsPrincipal t) : Out.PolAV (Sp K) where
  A := t.G
  isAb := ⟨inferInstance, t.semi.smooth, h.1, t.semi.geomConnected⟩
  g := (isPrincipal_dim h).choose
  smoothDim := (isPrincipal_dim h).choose_spec
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := fun _ => by
    obtain ⟨-, ws, gs', -⟩ := t.sym
    exact ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
  ample := h.2.1
  ktriv := h.2.2

end GlobalTheory.CompanionTheory.Ar.SabModel
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.AbMult

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem lieMult_iff_family {S : Scheme.{0}} {k : Type} [Field k] {G : Over S} [GrpObj G] {O : Type} [CommRing O]
    {V : Type} [AddCommGroup V] [Module k V] {x : Sp k ⟶ S} (M : LieModel G x V) (act : OAct O G)
    (ρ : O →+* Module.End k V) (h : M.IsActOf act.act ρ) (τ : O →+* k) (n : ℕ) :
    LieMult act x τ n ↔ ∃ b : Fin n → V, LinearIndependent k b ∧ Submodule.span k (Set.range b) = eigSp ρ τ := by
  rw [Fl.Test.lieMult_iff_exists_frame]
  constructor
  · rintro ⟨v, hv⟩
    choose e he using fun i => M.onto (v i) (hv.1 i).1
    obtain rfl : v = fun i => M.pt (e i) := funext fun i => (he i).symm
    exact ⟨e, (Fl.Test.isEigFrame_iff M act ρ h τ e).1 hv⟩
  · rintro ⟨b, hb⟩
    exact ⟨fun i => M.pt (b i), (Fl.Test.isEigFrame_iff M act ρ h τ b).2 hb⟩

theorem lieMult_abPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ S) (P : AbPart t z), ∃ r : ℕ, ∀ (k : Type) [Field k] [IsAlgClosed k] (g : L →+* k) (τ : 𝓞 E →+* k) (n : ℕ), LieMult P.tK.act (spMap g) τ n → r ≤ n ∧ LieMult P.tB.act (spMap g) τ (n - r) := by
  intro E _ _ _ H S t L _ _ z P
  letI := P.τ.addCommGroup
  letI := P.τ.grpB
  haveI := P.τ.free
  haveI := P.τ.finite
  haveI := P.τ.q_hom
  haveI := P.τ.i_hom
  haveI := P.e_hom
  haveI heinv : IsMonHom P.e.inv := inferInstance
  obtain ⟨m, hm⟩ := GlobalTheory.T.torus_extension_module_structure L P.tK.G P.τ (𝓞 E) P.tK.act (fun a => by
    haveI := P.tB.act.hom a
    refine ⟨P.e.hom ≫ P.tB.act.act a ≫ P.e.inv, inferInstance, ?_⟩
    refine (cancel_mono P.e.hom).1 ?_
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using P.act a)
  letI := m
  refine ⟨Module.finrank ℤ P.τ.X / Module.finrank ℚ E, ?_⟩
  intro k _ _ g τ n hn
  haveI : CharZero k := charZero_of_injective_ringHom g.injective
  obtain ⟨V₂, _, _, ⟨M₂⟩⟩ := lieModel_exists (Sp L) P.tK.G k (spMap g)
  obtain ⟨V₃, _, _, ⟨M₃⟩⟩ := lieModel_exists (Sp L) P.tB.G k (spMap g)
  let D := GlobalTheory.Diag.diagAct (Sp L) (𝓞 E) P.τ.X
  let M₁ := Fl.Test.torusModel (spMap g) P.τ.X
  obtain ⟨ρ₁, hρ₁, -⟩ := lieModel_exists_unique_act _ _ k (spMap g) _ M₁ (𝓞 E) D.act D.hom D.one D.mul D.add
  obtain ⟨ρ₂, hρ₂, -⟩ := lieModel_exists_unique_act _ _ k (spMap g) _ M₂ (𝓞 E) P.tK.act.act P.tK.act.hom
    P.tK.act.one P.tK.act.mul P.tK.act.add
  obtain ⟨ρ₃, hρ₃, -⟩ := lieModel_exists_unique_act _ _ k (spMap g) _ M₃ (𝓞 E) P.tB.act.act P.tB.act.hom
    P.tB.act.one P.tB.act.mul P.tB.act.add
  obtain ⟨f, hf, -⟩ := lieModel_exists_unique_diff _ _ _ k (spMap g) _ _ M₁ M₂ P.τ.i
  obtain ⟨h, hh, -⟩ := lieModel_exists_unique_diff _ _ _ k (spMap g) _ _ M₂ M₃ (P.τ.q ≫ P.e.hom)
  obtain ⟨hker, hsurj⟩ := GlobalTheory.T.torus_extension_tangent_exact L P.tK.G P.τ k g
  haveI hmono : Mono P.τ.i := ⟨fun a b hab => P.τ.isKernel.hom_ext hab (toUnit_unique _ _)⟩
  have finj : Function.Injective f := fun a b hab => M₁.inj ((cancel_mono P.τ.i).1 (by
    rw [← hf, ← hf, hab]))
  have hsur : Function.Surjective h := fun y => by
    obtain ⟨v, hv, hvq⟩ := hsurj (M₃.pt y ≫ P.e.inv) ((M₃.tan y).comp_monHom P.e.inv)
    obtain ⟨a, rfl⟩ := M₂.onto v hv
    refine ⟨a, M₃.inj ?_⟩
    rw [hh, ← Category.assoc, hvq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hex : LinearMap.range f = LinearMap.ker h := by
    ext a
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    have h1 : h a = 0 ↔ M₂.pt a ≫ P.τ.q = 1 := by
      constructor
      · intro h0
        have := hh a
        rw [h0, Fl.Test.pt_zero, ← Category.assoc] at this
        refine (cancel_mono P.e.hom).1 ?_
        rw [← this, MonObj.one_comp]
      · intro h0
        refine M₃.inj ?_
        rw [hh, ← Category.assoc, h0, MonObj.one_comp, Fl.Test.pt_zero]
    rw [h1, hker _ (M₂.tan a)]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨M₁.pt c, M₁.tan c, (hf c).symm⟩
    · rintro ⟨w, hw, hwa⟩
      obtain ⟨c, rfl⟩ := M₁.onto w hw
      exact ⟨c, M₂.inj ((hf c).trans hwa)⟩
  have eqf : ∀ a c, f (ρ₁ a c) = ρ₂ a (f c) := fun a c => M₂.inj (by
    rw [hf, hρ₂ a (f c), hρ₁ a c, hf, Category.assoc, Category.assoc]
    exact congrArg (M₁.pt c ≫ ·) (hm a))
  have eqh : ∀ a c, h (ρ₂ a c) = ρ₃ a (h c) := fun a c => M₃.inj (by
    rw [hh, hρ₃ a (h c), hρ₂ a c, hh, Category.assoc, Category.assoc, Category.assoc]
    exact congrArg (M₂.pt c ≫ ·) (P.act a))
  obtain ⟨bas⟩ := GlobalTheory.T.eigenspace_basis_exists E P.τ.X k τ
  obtain ⟨b₁, hb₁, hb₁'⟩ := (lieMult_iff_family M₁ D ρ₁ hρ₁ τ _).1
    ((GlobalTheory.Diag.lieMult_iff (spMap g) τ _).2 ⟨bas⟩)
  obtain ⟨b₂, hb₂, hb₂'⟩ := (lieMult_iff_family M₂ P.tK.act ρ₂ hρ₂ τ n).1 hn
  obtain ⟨hle, b₃, hb₃⟩ := GlobalTheory.T.eigen_decomposition_exact_sequence E k _ _ _ ρ₁ ρ₂ ρ₃ f h finj hsur hex eqf eqh τ _ n b₁ b₂ hb₁ hb₁' hb₂ hb₂'
  exact ⟨hle, (lieMult_iff_family M₃ P.tB.act ρ₃ hρ₃ τ _).2 ⟨b₃, hb₃⟩⟩

end GlobalTheory.CompanionTheory.Ar.AbMult
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem not_inFibre_centre {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z)
    (r : ℕ) (hr : r.Prime) : ¬ InFibre ξ r ⟨centre z, h⟩ := by
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
  have hu : IsUnit ((r : X.presheaf.stalk (centre z))) := by
    have h1 : IsUnit ((Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z))) := by
      have e : (Scheme.stalkClosedPointTo z).hom (r : X.presheaf.stalk (centre z)) = (r : ℂ) := map_natCast _ r
      exact e ▸ hr0.isUnit
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo z).hom _ h1
  obtain ⟨u, hu⟩ := hu
  have hg : genMap ξ ⟨centre z, h⟩ (u : X.presheaf.stalk (centre z)) = (r : Ω) := by
    rw [hu, map_natCast]
  refine not_not.2 ⟨Nat.cast_ne_zero.2 hr.ne_zero, ⟨_, hg⟩, ⟨((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)), ?_⟩⟩
  rw [← hg]
  exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

theorem frame_valAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X) (lab : CMType H ⊕ CMType H) (r : ℕ) (s : Fin r → 𝔐.Li) (h : genPt 𝔐.ξ ⤳ centre z), (𝔐.V lab).IsFrameAt s ⟨centre z, h⟩ → ∀ i, ∃ v : epsAt z ⟶ 𝔐.t.G, 𝔐.M.ValAt z (s i) v := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z lab r s h hs i
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y S Ω K J y 𝔐 hinj
    ⟨centre z, h⟩ (fun r hr => not_inFibre_centre 𝔐.ξ z h r hr)
  have hmem : s i ∈ 𝔐.V lab ⟨centre z, h⟩ := by
    rw [hs.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [h1 lab] at hmem
  have hlat : s i ∈ 𝔐.M.lat ⟨centre z, h⟩ := by
    rw [h3]
    exact (le_iSup (fun s' => 𝔐.dR s' ⟨centre z, h⟩) lab) hmem
  exact (𝔐.M.exists_valAt_iff z (s i)).2 ⟨h, hlat⟩

end GlobalTheory.CompanionTheory.Ar.HodgeVal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.abelian_part_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange | exact GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.AbPartFieldChange.exists_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)


theorem _root_.GlobalTheory.T.hodge_flag_outside_prime_fibres : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ)
    (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y)
    (p : ℕ), p ∈ S → ∀ (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ p' : ℕ, p'.Prime → ¬ InFibre 𝔐.ξ p' q) →
      𝔐.HT p s q = 𝔐.dR s q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.HodgeModel.HtDr0.ht_eq_dR_of_not_inFibre | exact GlobalTheory.CompanionTheory.Ar.Top.HodgeModel.HtDr0.ht_eq_dR_of_not_inFibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.HodgeModel.HtDr0.ht_eq_dR_of_not_inFibre <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.ample_of_single_coord_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K) (a : K → ℤ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → a k₀ = 1 → (∀ k, k ≠ k₀ → a k = 0) → Ht.AmpleQ y a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AmpleBlock.ampleQ_of_embeds | exact GlobalTheory.CompanionTheory.Ar.AmpleBlock.ampleQ_of_embeds | (intros; apply GlobalTheory.CompanionTheory.Ar.AmpleBlock.ampleQ_of_embeds <;> assumption)
end
