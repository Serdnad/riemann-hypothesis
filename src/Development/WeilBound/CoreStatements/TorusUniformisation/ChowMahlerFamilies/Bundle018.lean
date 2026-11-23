module

import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle045
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle033
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleHomLoc
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingDimLe
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle054
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreChartBundle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001

@[expose] public section

section

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up

namespace PositivityTheory.Xgn.A_pt_seq_lin

variable {o C : Type} [CommRing o] [Field C] [Algebra o C]

theorem mem_std (R : Subalgebra o C) {ι : Type} (v : ι → C) : v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem mem_dual (R : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C)) (v : Fin m → C) :
    v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

theorem std_le_dual (R : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C))
    (h : L ≤ stdLat R _) : stdLat R _ ≤ dotDual R L := by
  intro v hv
  rw [mem_dual]
  intro l hl
  have hl' := (mem_std R l).1 (h hl)
  have hv' := (mem_std R v).1 hv
  show ∑ i, l i * v i ∈ R
  exact R.sum_mem fun i _ => R.mul_mem (hl' i) (hv' i)

theorem smul_mem_std (R : Subalgebra o C) {m : ℕ} (L : AddSubgroup (Fin m → C)) (w : C)
    (h : mulLat w (stdLat R _) ≤ L) (v : Fin m → C) (hv : v ∈ dotDual R L) :
    w • v ∈ stdLat R (Fin m) := by
  apply GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree.smul_mem_std <;> assumption

end PositivityTheory.Xgn.A_pt_seq_lin

open PositivityTheory.Xgn.A_pt_seq_lin in
theorem PositivityTheory.Xgn.t_pt_seq_lin : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (τ : Sg), w ≠ 0 → mulLat w (stdLat RC _) ≤ D.af RC p (χ τ) → D.af RC p (χ τ) ≤ stdLat RC _ → ∀ (ht : (Fin n → C) →ₗ[C] (Fin (s τ) → C)) (hb : (Fin (r τ) → C) →ₗ[C] (Fin n → C)), Function.Injective hb → LinearMap.range hb = LinearMap.ker ht → (stdLat RC _).map ht.toAddMonoidHom = D.omHT τ → (stdLat RC _).comap hb.toAddMonoidHom = D.W τ → (D.hh RC p (χ τ)).map ht.toAddMonoidHom = D.om τ → (D.hh RC p (χ τ)).comap hb.toAddMonoidHom = divLat w (D.lie τ) → (∀ b c, (b, c) ∈ D.Del τ ↔ w • b ∈ stdLat RC _ ∧ c - ht b ∈ D.omHT τ) → (∀ a b, (a, b) ∈ D.Gam τ ↔ w • a ∈ D.W τ ∧ b - hb a ∈ stdLat RC _) → D.imH RC p τ (χ τ) = D.om τ ∧ D.kerH RC p τ (χ τ) = divLat w (D.lie τ) := by
  intro o C _ _ _ RC p F _ _ n Sg r s D w χ τ hw0 h1 h2 ht hb hinj hrng hHT hW hom hlie hDel hGam
  have hS : stdLat RC (Fin n) ≤ D.hh RC p (χ τ) := std_le_dual RC _ h2
  have hm : ∀ v ∈ D.hh RC p (χ τ), w • v ∈ stdLat RC (Fin n) :=
    fun v hv => smul_mem_std RC _ w h1 v hv
  constructor
  · ext c
    rw [← hom]
    constructor
    · rintro ⟨⟨b, c'⟩, hx, rfl⟩
      obtain ⟨hd, hp⟩ := AddSubgroup.mem_inf.1 hx
      obtain ⟨hb1, -⟩ := AddSubgroup.mem_prod.1 hp
      obtain ⟨-, hc⟩ := (hDel b c').1 hd
      rw [← hHT] at hc
      obtain ⟨y, hy, hy'⟩ := AddSubgroup.mem_map.1 hc
      refine AddSubgroup.mem_map.2 ⟨b + y, add_mem hb1 (hS hy), ?_⟩
      simp only [LinearMap.toAddMonoidHom_coe] at hy' ⊢
      simp [map_add (f := _), hy']
    · rintro ⟨b, hb1, rfl⟩
      refine AddSubgroup.mem_map.2 ⟨(b, ht b), AddSubgroup.mem_inf.2 ⟨?_, AddSubgroup.mem_prod.2 ⟨hb1, AddSubgroup.mem_top _⟩⟩, rfl⟩
      rw [hDel]
      refine ⟨hm b hb1, ?_⟩
      simp only [sub_self]
      exact zero_mem _
  · ext a
    rw [← hlie]
    constructor
    · rintro ⟨⟨a', b⟩, hx, rfl⟩
      obtain ⟨hg, hp⟩ := AddSubgroup.mem_inf.1 hx
      obtain ⟨-, hb1⟩ := AddSubgroup.mem_prod.1 hp
      obtain ⟨-, h2'⟩ := (hGam a' b).1 hg
      rw [AddSubgroup.mem_comap]
      have := sub_mem hb1 (hS h2')
      simpa using this
    · intro ha
      rw [AddSubgroup.mem_comap] at ha
      refine AddSubgroup.mem_map.2 ⟨(a, hb a), AddSubgroup.mem_inf.2 ⟨(hGam _ _).2 ⟨?_, ?_⟩, AddSubgroup.mem_prod.2 ⟨AddSubgroup.mem_top _, ha⟩⟩, rfl⟩
      · rw [← hW, AddSubgroup.mem_comap]
        simp only [LinearMap.toAddMonoidHom_coe, map_smul]
        exact hm _ ha
      · simp only [sub_self]
        exact zero_mem _
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.CoordinateMapFiniteType

theorem finiteType_of_range {A Ω R : Type} [CommRing A] [Field Ω] [CommRing R] (φ : A →+* Ω)
    (hφ : Function.Injective φ) (s : Set Ω) (hs : s.Finite)
    (h : ∀ a : Ω, a ∈ Algebra.adjoin ℤ s ↔ a ∈ φ.range) (ψ : R →+* A) : ψ.FiniteType := by
  have h1 : Algebra.FiniteType ℤ (Algebra.adjoin ℤ s) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
  have hr : φ.toIntAlgHom.range = Algebra.adjoin ℤ s := by
    ext a
    rw [h a]
    rfl
  have h2 : Algebra.FiniteType ℤ A :=
    Algebra.FiniteType.equiv h1
      ((AlgEquiv.ofInjective φ.toIntAlgHom hφ).trans (Subalgebra.equivOfEq _ _ hr)).symm
  have h3 : (ψ.comp (algebraMap ℤ R)).FiniteType := by
    rw [Subsingleton.elim (ψ.comp (algebraMap ℤ R)) (algebraMap ℤ A)]
    exact RingHom.finiteType_algebraMap.2 h2
  exact RingHom.FiniteType.of_comp_finiteType h3

theorem main {X Y : Scheme.{0}} [IsAffine Y] (f : X ⟶ Y) {Ω : Type} [Field Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hq : ∀ q : X, genPt ξ ⤳ q) (hT : CoordTie ℤ ξ x) :
    LocallyOfFiniteType f ∧ QuasiCompact f := by
  choose U h hU hUq _ hinj hran using fun c : {c // x c ≠ 0} => TieFrame.exists_chart hT c.2
  have hcov : ∀ q : X, ∃ c, q ∈ U c := fun q => by
    obtain ⟨c, hc⟩ := hT.cover ⟨q, hq q⟩
    exact ⟨⟨c, hc.1⟩, (hUq ⟨c, hc.1⟩ ⟨q, hq q⟩).2 hc⟩
  constructor
  · have htop : ⨆ c, ((⟨U c, hU c⟩ : X.affineOpens) : X.Opens) = ⊤ := by
      refine top_le_iff.1 fun q _ => ?_
      obtain ⟨c, hc⟩ := hcov q
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, hc⟩
    refine (HasRingHomProperty.iff_of_iSup_eq_top (P := @LocallyOfFiniteType)
      (fun c => (⟨U c, hU c⟩ : X.affineOpens)) htop).2 fun c => ?_
    exact finiteType_of_range _ (hinj c) _ (Set.finite_range _) (hran c) _
  · have : CompactSpace X := by
      refine ⟨?_⟩
      have e : (Set.univ : Set X) = ⋃ c, (U c : Set X) :=
        (Set.eq_univ_of_forall fun q => Set.mem_iUnion.2 (hcov q)).symm
      rw [e]
      exact isCompact_iUnion fun c => (hU c).isCompact
    exact (quasiCompact_iff_compactSpace f).2 this

end PositivityTheory.Xgn.CoordinateMapFiniteType

theorem PositivityTheory.Xgn.coordinate_map_finite_type : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X), (∀ q : X, genPt ξ ⤳ q) →
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → LocallyOfFiniteType (toZ X) ∧ QuasiCompact (toZ X) := by
  intro X Ω _ K _ J _ y ξ hq hT
  exact PositivityTheory.Xgn.CoordinateMapFiniteType.main (toZ X) hq hT
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace PositivityTheory.Xgn.A_xgz_chow_mahler_fibrefactor

theorem pair_eq {n : ℕ} (h : HermNorm n) (p : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, ((h.mat)⁻¹ *ᵥ p) j * h.pointOf y j = ∑ j, p j * y j := by
  have h1 : ((h.mat)⁻¹ *ᵥ p) ⬝ᵥ (h.matᵀ *ᵥ fun i => y i) = p ⬝ᵥ fun i => y i := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ h.isUnit_det, Matrix.one_mulVec, dotProduct_comm]
  exact h1

theorem pointOf_inj {n : ℕ} (h : HermNorm n) : Function.Injective h.pointOf := by
  intro y y' hy
  ext i
  have h1 := pair_eq h (Pi.single i 1) y
  have h2 := pair_eq h (Pi.single i 1) y'
  rw [hy, h2] at h1
  simpa [Pi.single_apply] using h1.symm

theorem row_zero {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} {π : Fin (e + 1) → Fin n → ℂ}
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ fibrePts S π) : ∑ j, π 0 j * y j = 1 := by
  have h1 : linProj π y 0 = firstCoordVec (e + 1) 0 := by rw [hy.2]
  simpa [linProj, firstCoordVec] using h1

theorem row_succ {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} {π : Fin (e + 1) → Fin n → ℂ}
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ fibrePts S π) (i : Fin e) :
    ∑ j, π i.succ j * y j = 0 := by
  have h1 : linProj π y i.succ = firstCoordVec (e + 1) i.succ := by rw [hy.2]
  simpa [linProj, firstCoordVec] using h1

end PositivityTheory.Xgn.A_xgz_chow_mahler_fibrefactor

open PositivityTheory.Xgn.A_xgz_chow_mahler_fibrefactor in
theorem PositivityTheory.Xgn.t_xgz_chow_mahler_fibrefactor : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (π : Fin (e + 1) → Fin n → ℂ) (u₀ : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g →
  (fibrePts (coneSet h W) π).encard = δ →
  eval (consGroup u₀ (nrmGroups h e (coefRows h π))) g ≠ 0 →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin n → ℂ, eval (consGroup u (nrmGroups h e (coefRows h π))) g =
      c * ∏ᶠ y ∈ fibrePts (coneSet h W) π, ∑ j, u j * h.pointOf y j := by
  classical
  intro n e δ h W g π u₀ _ hch hmh hcard hne
  have hfin : (fibrePts (coneSet h W) π).Finite := Set.finite_of_encard_eq_coe hcard
  have hc : hfin.toFinset.card = δ := by
    have h1 := hfin.encard_eq_coe_toFinset_card
    rw [hcard] at h1
    exact_mod_cast h1.symm
  have hone : ∀ y ∈ fibrePts (coneSet h W) π,
      ∑ j, ((h.mat)⁻¹ *ᵥ π 0) j * h.pointOf y j = 1 := fun y hy => by
    rw [pair_eq, row_zero hy]
  obtain ⟨c, hc0, hcu⟩ := GlobalTheory.T.chow_form_specialization_proportional n e δ W g (nrmGroups h e (coefRows h π))
    (hfin.toFinset.image h.pointOf) u₀ hch hmh
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rw [Set.Finite.mem_toFinset] at hy
      refine ⟨fun h0 => ?_, hy.1, fun i => ?_⟩
      · have h1 := hone y hy
        rw [h0] at h1
        simp at h1
      · have h1 := pair_eq h (π i.succ) y
        rw [row_succ hy] at h1
        simp only [nrmGroups, coefRows, mul_assoc]
        rw [← Finset.mul_sum, h1, mul_zero])
    (by
      intro x hx x' hx' t ht
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hx'
      rw [Set.Finite.mem_toFinset] at hy hy'
      have h1 := hone y hy
      have h2 := hone y' hy'
      rw [ht] at h2
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ t] at h2
      rw [← Finset.mul_sum, h1, mul_one] at h2
      rw [ht, h2, one_smul])
    (by rw [Finset.card_image_of_injective _ (pointOf_inj h), hc]) hne
  refine ⟨c, hc0, fun u => ?_⟩
  rw [hcu u, Finset.prod_image (fun a _ b _ hab => pointOf_inj h hab),
    finprod_mem_eq_finite_toFinset_prod _ hfin]
end

section

theorem PositivityTheory.Xgn.t_s_joinvertdiv : GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.JoinVerticalDivisor.proof
end

section

namespace PositivityTheory.Xgn.A_s_divcyclehomloc

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem homLocRingLocal : HomLocRingLocal.Statement.{0} :=
  HomLocRingLocal.proof (HomLocRingIsLocal.proof HomLocRingMem.proof)
    (HomLocRingNoetherian.proof HomLocRingMem.proof)
    (HomLocRingDimLe.proof HomLocRingMem.proof (HomLocRingIsLocal.proof HomLocRingMem.proof))

end PositivityTheory.Xgn.A_s_divcyclehomloc

theorem PositivityTheory.Xgn.t_s_divcyclehomloc : GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.Statement.{0} :=
  GroundTheory.Heights₂.Heights.NumbersDVR.DivCycleHomLoc.proof PositivityTheory.Xgn.A_s_divcyclehomloc.homLocRingLocal
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgn.FiniteSurjectivePointLift

theorem exists_ringHom (L A : Type) [Field L] [CommRing A] [Nontrivial A] (φ : L →+* A) (hφ : φ.Finite) :
    ∃ ψ : A →+* AlgebraicClosure L, ψ.comp φ = algebraMap L (AlgebraicClosure L) := by
  letI := φ.toAlgebra
  haveI : Module.Finite L A := hφ
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field m
  haveI : Module.Finite L (A ⧸ m) := inferInstance
  haveI : Algebra.IsAlgebraic L (A ⧸ m) := inferInstance
  let j : (A ⧸ m) →ₐ[L] AlgebraicClosure L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(j.comp (Ideal.Quotient.mkₐ L m)).toRingHom, ?_⟩
  ext x
  exact (j.comp (Ideal.Quotient.mkₐ L m)).commutes x

theorem exists_point (L : Type) [Field L] (P : Scheme.{0}) [Nonempty P] (g : P ⟶ Spec (CommRingCat.of L))
    [IsFinite g] : ∃ x : Spec (CommRingCat.of (AlgebraicClosure L)) ⟶ P,
      x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))) := by
  haveI hA : IsAffine P := isAffine_of_isAffineHom g
  have hfin : (g.appTop).hom.Finite := g.finite_app ⊤ (isAffineOpen_top _)
  let φ : L →+* Γ(P, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ g.appTop).hom
  have hφ : φ.Finite := by
    refine RingHom.Finite.comp hfin ?_
    exact RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of L)).inv).2
  haveI : Nonempty (⊤ : P.Opens) := ⟨⟨Classical.arbitrary P, trivial⟩⟩
  obtain ⟨ψ, hψ⟩ := exists_ringHom L Γ(P, ⊤) φ hφ
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ P.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv]
  simp only [← Spec.map_comp]
  congr 1
  ext x
  exact congrArg (fun f => f x) hψ

end PositivityTheory.Xgn.FiniteSurjectivePointLift

theorem PositivityTheory.Xgn.finite_surjective_point_lift : ∀ (Z' Z : Scheme.{0}) (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ (L : Type) [Field L] (zZ : Sp L ⟶ Z),
    ∃ x : Sp (AlgebraicClosure L) ⟶ Z', x ≫ π = spMap (algebraMap L (AlgebraicClosure L)) ≫ zZ := by
  intro Z' Z π hfin hsurj L _ zZ
  haveI : Surjective (pullback.snd π zZ) := inferInstance
  obtain ⟨p, -⟩ := (pullback.snd π zZ).surjective (IsLocalRing.closedPoint L)
  haveI : Nonempty ↥(pullback π zZ) := ⟨p⟩
  obtain ⟨x, hx⟩ := FiniteSurjectivePointLift.exists_point L (pullback π zZ) (pullback.snd π zZ)
  refine ⟨x ≫ pullback.fst π zZ, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
end
