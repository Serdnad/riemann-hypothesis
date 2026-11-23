module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationCoordsComplexPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle048
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle047
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsTwistedGenerators
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle020
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.snc_points_transfer_dominating : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ₁ κ₂ : Type) (x₁ : κ₁ → Ω) (x₂ : κ₂ → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (g : X₂ ⟶ X₁) (e : ℕ) (Ab : Set X₁), (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ x₁ → CoordTie ℤ ξ₂ x₂ → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SncPts ξ₁ e {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} → SncPts ξ₂ e {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt | exact GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VbPull

theorem dual_frame_ext {Ω Ω' : Type} [Field Ω] [Field Ω'] (i : Ω →+* Ω') {W W' : Type} [AddCommGroup W] [Module Ω W]
    [AddCommGroup W'] [Module Ω' W'] (j : W →+ W') (hj : ∀ (a : Ω) (e : W), j (a • e) = i a • j e)
    (hs : Submodule.span Ω' (Set.range j) = ⊤) (jW : Module.Dual Ω W →+ Module.Dual Ω' W')
    (hjW : ∀ u e, jW u (j e) = i (u e)) {r : ℕ} (b : Fin r → Module.Dual Ω W) (hli : LinearIndependent Ω b)
    (hb : Submodule.span Ω (Set.range b) = ⊤) :
    LinearIndependent Ω' (fun k => jW (b k)) ∧ Submodule.span Ω' (Set.range fun k => jW (b k)) = ⊤ := by
  classical
  let c := Module.Basis.mk hli hb.ge
  have hc : ∀ k, c k = b k := fun k => by simp [c]
  haveI : Module.Finite Ω (Module.Dual Ω W) := Module.Finite.of_basis c
  haveI : Module.Finite Ω W := (Module.finite_dual_iff Ω).1 inferInstance
  let e : Fin r → W := fun l => (Module.evalEquiv Ω W).symm (c.dualBasis l)
  have he : ∀ k l, b k (e l) = if k = l then 1 else 0 := by
    intro k l
    simp only [e]
    rw [Module.apply_evalEquiv_symm_apply, ← hc k, Module.Basis.dualBasis_apply_self]
  have hx : ∀ x : W, x = ∑ k, b k x • e k := by
    intro x
    rw [← sub_eq_zero]
    apply (Module.forall_dual_apply_eq_zero_iff Ω _).1
    intro u
    have hu : u ∈ Submodule.span Ω (Set.range b) := by rw [hb]; trivial
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy

      simp [he, map_sum]
    | zero => simp
    | add y z _ _ hy hz => simp only [LinearMap.add_apply, hy, hz, add_zero]
    | smul a y _ hy => simp only [LinearMap.smul_apply, hy, smul_zero]
  have hjx : ∀ x, j x = ∑ k, i (b k x) • j (e k) := by
    intro x
    conv_lhs => rw [hx x]

    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => hj _ _
  have hext : ∀ v v' : Module.Dual Ω' W', (∀ k, v (j (e k)) = v' (j (e k))) → v = v' := by
    intro v v' h
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨x, rfl⟩
    rw [hjx x]

    simp only [map_sum, map_smul, h]
  have hpair : ∀ k l, jW (b k) (j (e l)) = if k = l then 1 else 0 := by
    intro k l
    rw [hjW, he]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg l
    have := congrArg (fun v : Module.Dual Ω' W' => v (j (e l))) hg
    simpa [hpair] using this
  · rw [eq_top_iff]
    intro v _
    have hv : v = ∑ k, v (j (e k)) • jW (b k) := by
      apply hext
      intro l
      simp [hpair]
    rw [hv]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem isVBOn_dual_pull : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (j : V →+ V') (jd : Module.Dual Ω V →+ Module.Dual Ω' V') (W : Submodule Ω V) (W' : Submodule Ω' V') (Lo : Lat ξ (Module.Dual Ω V)) (Lo' : Lat ξ' (Module.Dual Ω' V')) (T : Set (Cpt ξ)) (T' : Set (Cpt ξ')) (r : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsCptGen ξ' → IsExtOver i j → (∀ w e, jd w (j e) = i (w e)) → W' = Submodule.span Ω' (j '' (W : Set V)) → (Lo.map W.dualRestrict).IsVBOn T r ⊤ → (∀ p' ∈ T', ∃ hq : genPt ξ ⤳ f p'.1, (⟨f p'.1, hq⟩ : Cpt ξ) ∈ T ∧ (0 < r → Lo' p' = Submodule.span (regAt ξ' p') (jd '' (Lo ⟨f p'.1, hq⟩ : Set (Module.Dual Ω V))))) → (Lo'.map W'.dualRestrict).IsVBOn T' r ⊤ := by
  intro X X' Ω Ω' _ _ ξ ξ' f i V V' _ _ _ _ j jd W W' Lo Lo' T T' r hd _ hj hjd hW hvb hT
  have hmem : ∀ e : W, j e ∈ W' := fun e => by
    rw [hW]
    exact Submodule.subset_span ⟨e, e.2, rfl⟩
  let jr : W →+ W' :=
    { toFun := fun e => ⟨j e, hmem e⟩
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun a b => Subtype.ext (map_add j _ _) }
  have hsm : ∀ (a : Ω) (e : W), jr (a • e) = i a • jr e := fun a e => Subtype.ext (hj.1 a e)
  have hext : IsExtOver i jr := ⟨hsm, fun n b hb => by
    have h1 := hj.2 n (fun k => (b k : V)) (hb.map' W.subtype W.ker_subtype)
    exact LinearIndependent.of_comp W'.subtype h1⟩
  have hs : Submodule.span Ω' (Set.range jr) = ⊤ := by
    have h1 : (Submodule.span Ω' (Set.range jr)).map W'.subtype = W' := by
      rw [Submodule.map_span]
      conv_rhs => rw [hW]
      congr 1
      ext x
      constructor
      · rintro ⟨_, ⟨e, rfl⟩, rfl⟩
        exact ⟨e, e.2, rfl⟩
      · rintro ⟨e, he, rfl⟩
        exact ⟨_, ⟨⟨e, he⟩, rfl⟩, rfl⟩
    have h2 := Submodule.comap_map_eq_of_injective W'.injective_subtype (Submodule.span Ω' (Set.range jr))
    rw [h1, Submodule.comap_subtype_self] at h2
    exact h2.symm
  obtain ⟨jW, hjW⟩ := DualExt.dual_ext Ω Ω' i W W' jr hext hs
  have hcomp : ∀ w, W'.dualRestrict (jd w) = jW (W.dualRestrict w) := by
    intro w
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨e, rfl⟩
    rw [hjW]
    exact hjd w e
  have hsemi : ∀ (a : Ω) (u : Module.Dual Ω W), jW (a • u) = i a • jW u := by
    intro a u
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨e, rfl⟩
    simp [hjW]
  intro p' hp'
  obtain ⟨hq, hpT, -⟩ := hT p' hp'
  obtain ⟨U, hU, b, hb, hfr⟩ := hvb _ hpT
  obtain ⟨hli', hspan'⟩ := dual_frame_ext i jr hsm hs jW hjW b (hfr _ hpT hU).1 hb
  refine ⟨f ⁻¹ᵁ U, hU, fun k => jW (b k), hspan', fun q' hq' hq'U => ⟨hli', ?_⟩⟩
  obtain ⟨hq2, hqT, hL⟩ := hT q' hq'
  have hfrq := (hfr _ hqT hq'U).2
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : Subsingleton (Module.Dual Ω' W') := by
      rw [← Submodule.subsingleton_iff Ω', ← subsingleton_iff_bot_eq_top]
      rw [← hspan']
      simp
    exact Subsingleton.elim _ _
  · obtain ⟨hq3, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd q'
    apply le_antisymm
    · show Submodule.map _ _ ≤ _
      rw [hL hr, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      show W'.dualRestrict (jd w) ∈ _
      rw [hcomp]
      have hin : W.dualRestrict w ∈ Submodule.span (regAt ξ ⟨f q'.1, hq2⟩) (Set.range b) := by
        rw [← hfrq]
        exact ⟨w, hw, rfl⟩
      have key : ∀ y ∈ Submodule.span (regAt ξ ⟨f q'.1, hq2⟩) (Set.range b),
          jW y ∈ Submodule.span (regAt ξ' q') (Set.range fun k => jW (b k)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨k, rfl⟩ := hy
          exact Submodule.subset_span ⟨k, rfl⟩
        | zero => simp
        | add y z _ _ hy hz =>
          rw [map_add (f := _)]
          exact Submodule.add_mem _ hy hz
        | smul a y _ hy =>
          have : jW (a • y) = (⟨i a, hreg _ a.2⟩ : regAt ξ' q') • jW y := hsemi (a : Ω) y
          rw [this]
          exact Submodule.smul_mem _ _ hy
      exact key _ hin
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have hin : b k ∈ (Lo.map W.dualRestrict) ⟨f q'.1, hq2⟩ := by
        rw [hfrq]
        exact Submodule.subset_span ⟨k, rfl⟩
      obtain ⟨w, hw, hwk⟩ := hin
      refine ⟨jd w, ?_, ?_⟩
      · rw [hL hr]
        exact Submodule.subset_span ⟨w, hw, rfl⟩
      · show W'.dualRestrict (jd w) = jW (b k)
        rw [hcomp]
        exact congrArg jW hwk

end GlobalTheory.CompanionTheory.Ar.VbPull
end
end

section

open ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.valuation_coords_complex_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (w : (Σ k, ι k) → ℂ), w ∈ Small.ptsOver ℂ (mCoordIdeal y) → ∃ (W : Subring Ω) (φ : W →+* ℂ), (∀ a : W, φ a ≠ 0 → IsUnit a) ∧ (∀ (k : K) (c e : ι k), w ⟨k, c⟩ ≠ 0 → ∃ h : y ⟨k, e⟩ / y ⟨k, c⟩ ∈ W, φ ⟨_, h⟩ * w ⟨k, c⟩ = w ⟨k, e⟩) ∧ ∀ (a : K → ℤ) (s : Ω) (v : ℂ) (C : ∀ k, ι k), Small.HasVal y a s w v → (∀ k, w ⟨k, C k⟩ ≠ 0) → ∃ h : s * ∏ k, y ⟨k, C k⟩ ^ (-a k) ∈ W, φ ⟨_, h⟩ * ∏ k, w ⟨k, C k⟩ ^ a k = v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocVal.exists_locRing_val | exact GlobalTheory.CompanionTheory.Ar.LocVal.exists_locRing_val | (intros; apply GlobalTheory.CompanionTheory.Ar.LocVal.exists_locRing_val <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

theorem lat_eq_range : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (h : IsCptGen ξ) (G : Over X) [GrpObj G] (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (Ep : Type) [AddCommGroup Ep] [Module (regAt ξ p) Ep] (Mp : LieModel G (regPt h p) Ep) (j : Ep →ₗ[regAt ξ p] E), (∀ e, (M.pt (j e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left) → (M.lat p : Set E) = Set.range j :=
  @PositivityTheory.Xgn.normal_lattice_range

end GlobalTheory.CompanionTheory.Ar.LieStalk
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.frame_coeffs_regular_in_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m n r : ℕ) (φ : Fin n → Module.Dual Ω E), IsTwistGen ξ x L m φ → ∀ (p : Cpt ξ) (c₁ : κ), InChart ξ x c₁ p → ∀ β : Fin r → E, L.IsFrameAt β p → ∃ B : Matrix (Fin r) (Fin n) Ω, (∀ a j, B a j ∈ regAt ξ p) ∧ (∀ j a, φ j (β a) / x c₁ ^ m ∈ regAt ξ p) ∧ B * Matrix.of (fun j a => φ j (β a) / x c₁ ^ m) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse | exact GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.twist_left_inverse <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.frame_via_twisted_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (c : Fin r → E), CoordTie ℤ ξ x → L.IsVB r V → IsTwistGen ξ x L m φ → LinearIndependent Ω c → Submodule.span Ω (Set.range c) = V → ∃ B : Matrix (Fin r) (Fin n) Ω, B * Matrix.of (fun j l => φ j (c l)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms | exact GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.exists_leftInverse_flagForms <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.exists_twisted_generators : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → L.IsVB r V → ∃ (m n : ℕ) (φ : Fin n → Module.Dual Ω E), IsTwistGen ξ x L m φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Twist.exists_twistGen | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Twist.exists_twistGen | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Twist.exists_twistGen <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem inv_mem_locSub_prod {K : Type} [Field K] {Q : Type} [Fintype Q] (D : Subring K) (s : Q → K)
    (h0 : ∀ q, s q ≠ 0) (hD : ∀ q, s q ∈ D) (q : Q) : (s q)⁻¹ ∈ locSub D (∏ q, s q) := by
  classical
  have hprod : s q * ∏ q' ∈ Finset.univ.erase q, s q' = ∏ q', s q' :=
    Finset.mul_prod_erase Finset.univ s (Finset.mem_univ q)
  have hne : (∏ q', s q') ≠ 0 := Finset.prod_ne_zero_iff.2 fun q' _ => h0 q'
  have e : (s q)⁻¹ = (∏ q', s q')⁻¹ * ∏ q' ∈ Finset.univ.erase q, s q' := by
    rw [← hprod] at hne ⊢
    have h1 : (∏ q' ∈ Finset.univ.erase q, s q') ≠ 0 := right_ne_zero_of_mul hne
    field_simp [h0 q, h1]
  rw [e]
  exact (locSub D (∏ q, s q)).mul_mem (inv_mem_locSub D _)
    (le_locSub D _ (D.prod_mem fun q' _ => hD q'))

theorem locSub_eq_of_inverse_family : ∀ {K : Type} [Field K] {Q : Type} [Fintype Q] (A B : Subring K) (t : Q → K),
    (∀ q, t q ≠ 0) → (∀ q, t q ∈ A) → (∀ q, (t q)⁻¹ ∈ B) →
    A ≤ Subring.closure ((B : Set K) ∪ Set.range t) →
    B ≤ Subring.closure ((A : Set K) ∪ Set.range fun q => (t q)⁻¹) →
    locSub A (∏ q, t q) = locSub B (∏ q, t q)⁻¹ := by
  intro K _ Q _ A B t h0 hA hB hAB hBA
  have hT : (∏ q, t q) ∈ A := A.prod_mem fun q _ => hA q
  have hTi : (∏ q, t q)⁻¹ ∈ B := by
    rw [← Finset.prod_inv_distrib]
    exact B.prod_mem fun q _ => hB q
  have hBle : B ≤ locSub A (∏ q, t q) := by
    refine hBA.trans ((Subring.closure_le).2 ?_)
    rintro x (hx | ⟨q, rfl⟩)
    · exact le_locSub A _ hx
    · exact inv_mem_locSub_prod A t h0 hA q
  have hAle : A ≤ locSub B (∏ q, t q)⁻¹ := by
    refine hAB.trans ((Subring.closure_le).2 ?_)
    rintro x (hx | ⟨q, rfl⟩)
    · exact le_locSub B _ hx
    · have h := inv_mem_locSub_prod B (fun q => (t q)⁻¹) (fun q => inv_ne_zero (h0 q)) hB q
      rw [Finset.prod_inv_distrib] at h
      simpa using h
  refine le_antisymm ((Subring.closure_le).2 ?_) ((Subring.closure_le).2 ?_)
  · rintro x (hx | hx)
    · exact hAle hx
    · rw [Set.mem_singleton_iff.1 hx]
      exact le_locSub B _ hTi
  · rintro x (hx | hx)
    · exact hBle hx
    · rw [Set.mem_singleton_iff.1 hx, inv_inv]
      exact le_locSub A _ hT

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem exists_basicOpen_piece (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (U : X.Opens) (R : Subring Ω) (a : Ω) (hc : IsCptGen ξ) (hP : IsPiece ξ U R) (haR : a ∈ R)
    (ha0 : a ≠ 0) :
    ∃ U' : X.Opens, IsPiece ξ U' (locSub R a) ∧ ∀ q : Cpt ξ, q.1 ∈ U' ↔ q.1 ∈ U ∧ unitAt ξ q a := by
  by_cases hη : genPt ξ ∈ U
  swap
  · have hno : ∀ q : Cpt ξ, q.1 ∉ U := fun q hq => hη (q.2.mem_open U.isOpen hq)
    refine ⟨U, ⟨hP.affine, hP.spec, fun b => ?_⟩, fun q => ?_⟩
    · refine ⟨fun _ q hq => absurd hq (hno q), fun _ => le_locSub R a ?_⟩
      exact (hP.ring b).2 fun q hq => absurd hq (hno q)
    · exact ⟨fun h => absurd h (hno q), fun h => h.1⟩
  obtain ⟨-, hrng⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hc U hη hP.spec
  obtain ⟨s, hs⟩ := (hrng a).2 ((hP.ring a).1 haR)
  have hga : ∀ (q : Cpt ξ) (hq : q.1 ∈ U), genMap ξ q (X.presheaf.germ U q.1 hq s) = a :=
    fun q hq => (genMap_germ_eq_stalk_closed ξ q U hq hη s).trans hs
  have hmem : ∀ q : Cpt ξ, q.1 ∈ X.basicOpen s ↔ q.1 ∈ U ∧ unitAt ξ q a := by
    intro q
    constructor
    · intro hq
      have hqU : q.1 ∈ U := X.basicOpen_le s hq
      have hu := (Scheme.mem_basicOpen X s q.1 hqU).1 hq
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have h1 : a * genMap ξ q v = 1 := by
        rw [← hga q hqU, ← map_mul, hv, map_one]
      exact ⟨hqU, ha0, ⟨_, hga q hqU⟩, ⟨v, (inv_eq_of_mul_eq_one_right h1).symm⟩⟩
    · rintro ⟨hqU, -, -, ⟨t, ht⟩⟩
      refine (Scheme.mem_basicOpen X s q.1 hqU).2 (isUnit_iff_exists_inv.2 ⟨t, hc.inj q ?_⟩)
      rw [map_mul, map_one, hga q hqU, ht, mul_inv_cancel₀ ha0]
  have hreg : ∀ c : Ω, c ∈ regAt ξ (Subtype.mk (genPt ξ) specializes_rfl : Cpt ξ) := by
    intro c
    obtain ⟨y, hy⟩ := hc.bij.2 c
    refine ⟨y, ?_⟩
    have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
      TopCat.Presheaf.stalkSpecializes_refl _ _
    change (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
      Scheme.stalkClosedPointTo ξ).hom y = c
    rw [e]
    exact hy
  have hη' : genPt ξ ∈ X.basicOpen s :=
    (hmem (Subtype.mk (genPt ξ) specializes_rfl : Cpt ξ)).2 ⟨hη, ha0, hreg a, hreg a⁻¹⟩
  refine ⟨X.basicOpen s, ⟨hP.affine.basicOpen s, fun q hq => hP.spec q (X.basicOpen_le s hq),
    fun b => ?_⟩, hmem⟩
  constructor
  · intro hb q hq
    obtain ⟨k, hk⟩ := (mem_locSub_iff haR ha0 b).1 hb
    obtain ⟨hqU, -, -, hinv⟩ := (hmem q).1 hq
    have h1 := (hP.ring _).1 hk q hqU
    have e : b = a⁻¹ ^ k * (a ^ k * b) := by
      rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ha0), _root_.one_mul]
    rw [e]
    exact (regAt ξ q).mul_mem ((regAt ξ q).pow_mem hinv _) h1
  · intro hb
    obtain ⟨-, hrng'⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hc (X.basicOpen s) hη'
      (fun q hq => hP.spec q (X.basicOpen_le s hq))
    obtain ⟨t, ht⟩ := (hrng' b).2 hb
    have hloc := hP.affine.isLocalization_basicOpen s
    obtain ⟨n, c, hcn⟩ := IsLocalization.Away.surj s t
    have hres : ∀ x : Γ(X, U),
        (X.presheaf.germ (X.basicOpen s) (genPt ξ) hη' ≫ Scheme.stalkClosedPointTo ξ).hom
          (algebraMap Γ(X, U) Γ(X, X.basicOpen s) x) =
        (X.presheaf.germ U (genPt ξ) hη ≫ Scheme.stalkClosedPointTo ξ).hom x := by
      intro x
      have := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (X.basicOpen_le s)) (genPt ξ) hη' x
      exact congrArg (Scheme.stalkClosedPointTo ξ).hom this
    have key : a ^ n * b = (X.presheaf.germ U (genPt ξ) hη ≫ Scheme.stalkClosedPointTo ξ).hom c := by
      have := congrArg (X.presheaf.germ (X.basicOpen s) (genPt ξ) hη' ≫
        Scheme.stalkClosedPointTo ξ).hom hcn
      rw [map_mul, map_pow, hres, hres, hs, ht] at this
      rw [← this, _root_.mul_comm]
    refine (mem_locSub_iff haR ha0 b).2 ⟨n, (hP.ring _).2 fun q hq => ?_⟩
    rw [key]
    exact (hrng _).1 ⟨c, rfl⟩ q hq

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.snc_patch_boundary_units : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ) (B : Set (Cpt ξ)) (h : Ω) (e n : ℕ) (z : Fin e → Mdl.invAdj (Mdl.chartQ x c) h) (p : Cpt ξ), IsCptGen ξ → (∀ q ∈ B, Char0 ξ q) → h ∈ Mdl.chartQ x c → h ≠ 0 → (∀ q : Cpt ξ, Char0 ξ q → InChart ξ x c q → unitAt ξ q h → (q ∈ B ↔ ∃ i : Fin e, (i : ℕ) < n ∧ ¬ unitAt ξ q (z i : Ω))) → Char0 ξ p → InChart ξ x c p → unitAt ξ p h → p ∉ B → ∃ a ∈ Mdl.chartQ x c, unitAt ξ p a ∧ ∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_chartQ_unit_sep | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_chartQ_unit_sep | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.exists_chartQ_unit_sep <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.boundary_points_coords : ∀ (Ω : Type) [Field Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (B : Set (Cpt ξ)), IsCptGen ξ → (∀ c (p : Cpt ξ), Char0 ξ p → InChart ξ x c p → p ∉ B → ∃ G ∈ Mdl.bdGens ξ x B, unitAt ξ p (Mdl.ratEval x c G)) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) z w → (w ∈ mcPts (Ideal.span (Mdl.bdGens ξ x B)) ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.mem_mcPts_span_bdGens_iff | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.mem_mcPts_span_bdGens_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.mem_mcPts_span_bdGens_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.boundary_generator_unit : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (c : Fin (N + 1)) (B : Set (Cpt ξ)) (p : Cpt ξ) (a : Ω), (∀ q ∈ B, Char0 ξ q) → Char0 ξ p → InChart ξ x c p → a ∈ Mdl.chartQ x c → unitAt ξ p a → (∀ q ∈ B, InChart ξ x c q → ¬ unitAt ξ q a) → ∃ G ∈ Mdl.bdGens ξ x B, unitAt ξ p (Mdl.ratEval x c G) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep.exists_bdGens_unitAt | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep.exists_bdGens_unitAt | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.Sep.exists_bdGens_unitAt <;> assumption)
end
