module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle066
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle013
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle087
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle517
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle459
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle520
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanAlg
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HPInvEqForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.MoebiusJetDuality.StatementU
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.CountableCompletion

open Cardinal IsLocalRing

theorem mk_adicCompletion_le_continuum (R : Type) [CommRing R] [Countable R] (I : Ideal R) :
    #(AdicCompletion I R) ≤ 𝔠 := by
  have hinj : Function.Injective
      (fun x : AdicCompletion I R => (x.1 : ∀ n : ℕ, R ⧸ (I ^ n • ⊤ : Submodule R R))) :=
    fun x y h => Subtype.ext h
  refine (mk_le_of_injective hinj).trans ?_
  rw [mk_pi]
  refine (prod_le_prod _ (fun _ => ℵ₀) fun n =>
    (mk_le_of_surjective (Submodule.mkQ_surjective _)).trans mk_le_aleph0).trans ?_
  simp

noncomputable abbrev completionCDVR (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CharZero R] : CDVR :=
  haveI : CharZero (AdicCompletion (maximalIdeal R) R) :=
    charZero_of_injective_algebraMap (GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R)
  { V := AdicCompletion (maximalIdeal R) R }

theorem exists_cdvr_mk_le_continuum :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R], Countable R →
      ∃ (T : CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i ∧
        Cardinal.mk T.V ≤ Cardinal.continuum := by
  intro R _ _ _ _ hR
  exact ⟨completionCDVR R, algebraMap R (AdicCompletion (maximalIdeal R) R),
    GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R, inferInstance,
    mk_adicCompletion_le_continuum R (maximalIdeal R)⟩

end GlobalTheory.CountableCompletion
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePairGram.Comb

theorem sum_shift {r p m : ℕ} (hm : p + m = r) (f : Fin r → ℂ) (h : ∀ c : Fin r, (c : ℕ) < p → f c = 0) :
    ∑ c, f c = ∑ i : Fin m, f ⟨p + i, by omega⟩ := by
  subst hm
  rw [Fin.sum_univ_add, Finset.sum_eq_zero (fun c _ => h _ (by simp)), zero_add]
  rfl

theorem sum_rev {r p : ℕ} (hp : p ≤ r) (f : Fin r → ℂ) (h : ∀ c : Fin r, p ≤ (c : ℕ) → f c = 0) :
    ∑ c, f c = ∑ i : Fin p, f ⟨p - 1 - i, by omega⟩ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [Fin.sum_univ_add, Finset.sum_eq_zero (s := Finset.univ) (f := fun i : Fin m => f (Fin.natAdd p i))
    (fun c _ => h _ (by simp)), add_zero, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  apply Fin.ext
  simp [Fin.val_rev]
  omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_comb (X : Data E r) {x x' : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h1 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x τ)⁻¹ * mat x' τ) a b = 0)
    (h2 : ∀ τ (a b : Fin r), X.p0 ≤ a → (b : ℕ) < X.p0 → ((mat x' τ)⁻¹ * mat x τ) a b = 0)
    (ρ : E →+* ℂ) (m : ℕ) (hm : ρ ∈ X.Ψ → m = r - X.p0) (hm' : ρ ∉ X.Ψ → m = X.p0)
    (v : Fin r → E) (b : ℕ) (hb : b < m) :
    Formalism.L2.PjFree.perFr X x' v ρ b = ∑ i : Fin m, coef X x x' ρ b i * Formalism.L2.PjFree.perFr X x v ρ i := by
  have hp := X.p0_le
  by_cases h : ρ ∈ X.Ψ
  · have hm := hm h
    have hd : IsUnit (mat x ⟨ρ, h⟩).det := (hx _).1.isUnit
    have hb' : X.p0 + b < r := by omega
    have e1 : Formalism.L2.PjFree.perFr X x' v ρ b = ∑ c : Fin r, ((mat x' ⟨ρ, h⟩)⁻¹ * mat x ⟨ρ, h⟩) ⟨_, hb'⟩ c *
        ((mat x ⟨ρ, h⟩)⁻¹.mulVec (Data.emb ρ v)) c := by
      unfold Formalism.L2.PjFree.perFr
      rw [dif_pos h, dif_pos hb']
      conv_lhs => rw [← mul_nonsing_inv_cancel_right (mat x ⟨ρ, h⟩) (mat x' ⟨ρ, h⟩)⁻¹ hd, ← mulVec_mulVec]
      rfl
    rw [e1, sum_shift (p := X.p0) (m := m) (by omega) _
      (fun c hc => by rw [h2 _ _ _ (Nat.le_add_right _ _) hc, zero_mul])]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : X.p0 + (i : ℕ) < r := by have := i.2; omega
    congr 1
    · simp only [coef, dif_pos h, ent]
      rw [dif_pos (And.intro hb' hi)]
    · unfold Formalism.L2.PjFree.perFr
      rw [dif_pos h, dif_pos hi]
  · obtain rfl := hm' h
    have h' : conjEmb ρ ∈ X.Ψ := by_contra fun h' => h ((X.cmType ρ).2 h')
    have hd : IsUnit (mat x ⟨_, h'⟩).det := (hx _).1.isUnit
    have hb' : X.p0 - 1 - b < r := by omega
    have e1 : Formalism.L2.PjFree.perFr X x' v ρ b = ∑ c : Fin r, ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) c ⟨_, hb'⟩ *
        hermC (conjEmb ρ) X.Gm (ReciprocityTheory.ChartRestriction.G.FD.col (mat x ⟨_, h'⟩) c) (Data.emb (conjEmb ρ) v) := by
      unfold Formalism.L2.PjFree.perFr
      rw [dif_neg h, dif_pos h', dif_pos hb']
      conv_lhs => rw [← mul_nonsing_inv_cancel_left (mat x ⟨_, h'⟩) (mat x' ⟨_, h'⟩) hd]
      generalize (mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩ = n
      change Matrix (Fin r) (Fin r) ℂ at n
      simp only [hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mul_apply, Finset.sum_mul, Finset.mul_sum]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      simp only [Matrix.mul_apply, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring
    rw [e1]
    refine Eq.trans (sum_rev hp _ fun c hc => ?_) ?_
    · rw [h1 _ _ _ hc (by simp only; omega), zero_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : X.p0 - 1 - (i : ℕ) < r := by omega
    have hi2 : (i : ℕ) < X.p0 := by have := i.2; omega
    congr 1
    · simp only [coef, dif_neg h, dif_pos h', ent]
      rw [dif_pos (And.intro hi hb')]
    · unfold Formalism.L2.PjFree.perFr
      rw [dif_neg h, dif_pos h', dif_pos hi]

def hmap {T : Type} {μ : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (μ τ)) (C : T → ℕ → ℕ → ℂ) :
    (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) where
  toFun z := fun j => ∑ i : Fin (μ (e j).1), C (e j).1 (e j).2 i * z (e.symm ⟨(e j).1, i⟩)
  map_add' z w := by
    funext j
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a z := by
    funext j
    simp [Finset.mul_sum, mul_left_comm]

theorem hmap_apply {T : Type} {μ : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (μ τ)) (C : T → ℕ → ℕ → ℂ) (z : Fin g → ℂ)
    (τ : T) (b : Fin (μ τ)) : hmap e C z (e.symm ⟨τ, b⟩) = ∑ i : Fin (μ τ), C τ b i * z (e.symm ⟨τ, i⟩) := by
  have key : ∀ s : Σ τ : T, Fin (μ τ), s = ⟨τ, b⟩ →
      ∑ i : Fin (μ s.1), C s.1 s.2 i * z (e.symm ⟨s.1, i⟩) = ∑ i : Fin (μ τ), C τ b i * z (e.symm ⟨τ, i⟩) := by
    rintro _ rfl
    rfl
  exact key _ (e.apply_symm_apply _)

theorem hmap_single {T : Type} {μ : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (μ τ)) (C : T → ℕ → ℕ → ℂ) (τ : T)
    (i : Fin (μ τ)) : hmap e C (Pi.single (e.symm ⟨τ, i⟩) 1) =
      ∑ b : Fin (μ τ), C τ b i • (Pi.single (e.symm ⟨τ, b⟩) 1 : Fin g → ℂ) := by
  funext j
  obtain ⟨⟨τ', b'⟩, rfl⟩ := e.symm.surjective j
  rw [hmap_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hτ : τ' = τ
  · subst hτ
    have hs : ∀ a b : Fin (μ τ'), (Pi.single (e.symm ⟨τ', a⟩) (1 : ℂ) : Fin g → ℂ) (e.symm ⟨τ', b⟩) =
        if a = b then 1 else 0 := by
      intro a b
      by_cases hab : a = b
      · subst hab
        simp
      · rw [if_neg hab, Pi.single_eq_of_ne (fun h => hab (by simpa using h.symm))]
    simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro c _
      rw [Pi.single_eq_of_ne (fun h => hτ (by simpa using congrArg Sigma.fst (e.symm.injective h))), mul_zero]
    · intro c _
      rw [Pi.single_eq_of_ne (fun h => hτ (by simpa using congrArg Sigma.fst (e.symm.injective h))), mul_zero]

theorem isDerivAt0_comp {g : ℕ} {X : Scheme.{0}} (e e' : (Fin g → ℂ) → (Sp ℂ ⟶ X))
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (he : ∀ z, e' (h z) = e z) {w : Fin g → ℂ}
    {v : Sp (DualNumber ℂ) ⟶ X} (hd : IsDerivAt0 e w v) : IsDerivAt0 e' (h w) v := by
  refine ⟨?_, fun U hU f => ?_⟩
  · rw [hd.1, ← he 0, map_zero]
  · rw [hd.2 U hU f]
    let hc : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) := h.toContinuousLinearEquiv
    have e1 : (fun z => valAt' (e z) U f) = (fun z => valAt' (e' z) U f) ∘ hc := by
      funext z
      simp only [Function.comp, hc, LinearEquiv.coe_toContinuousLinearEquiv', he]
    rw [e1, hc.comp_right_fderiv]
    simp [hc]

end GlobalTheory.FramePairGram.Comb


open GlobalTheory.FramePairGram.Comb in
theorem GlobalTheory.FramePairGram.lie_comb_of_block : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {U : Formalism.L2.PjFree.Unf Xo c σ r}, Formalism.L2.PjFree.IsUnf U → Formalism.L2.PjFree.GoodEmb c σ → ∀ (k : U.Comp) (x x' : (U.X k).dom), (∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x.1 τ)⁻¹ * mat x'.1 τ) a b = 0) → (∀ τ (a b : Fin r), (U.X k).p0 ≤ a → (b : ℕ) < (U.X k).p0 → ((mat x'.1 τ)⁻¹ * mat x.1 τ) a b = 0) → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), Formalism.L2.Pj.IsCombAt (U.un k x').x ((U.un k x').u τ) (fun b => (coef (U.X k) x.1 x'.1 (Formalism.L2.PjFree.relab c σ τ) b i : CAt σ)) ((U.un k x).u τ i) := by
  intro E _ _ _ r H Dw l Xo c σ U hU hσ k x x' h1 h2 τ i
  obtain ⟨hr, hty, -, -, -, g, e, F, ik, φ, -, hF⟩ := hU
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hty k
  obtain ⟨P, hP, hper, hx, hu, -⟩ := hF k x
  obtain ⟨P', hP', hper', hx', hu', -⟩ := hF k x'
  obtain ⟨hEU, hEL, -, -⟩ := GlobalTheory.exp_four_clauses E H Dw l Xo c σ hσ g e F
  let C : (E →+* ℂ) → ℕ → ℕ → ℂ := fun τ b i => coef (U.X k) x.1 x'.1 (Formalism.L2.PjFree.relab c σ τ) b i
  have hL : ∀ a, P' a = hmap e C (P a) := fun a => funext fun j => by
    rw [hP', perFr_comb (U.X k) x.2 h1 h2 _ (Dw.mult (e j).1)
      (fun h => (if_pos ((hrt _).1 ((hty _).1 h))).trans (by omega))
      (fun h => (if_neg (fun h' => h ((hty _).2 ((hrt _).2 h')))).trans hp0.symm) _ _ (e j).2.2]
    simp only [hmap, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP, Equiv.apply_symm_apply]
  have hsurj : Function.Surjective (hmap e C) := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range P') := by rw [hper'.2.2.2.1]; trivial
    refine (Submodule.span_le (p := (LinearMap.range (hmap e C)).restrictScalars ℝ)).2 ?_ hy
    rintro _ ⟨a, rfl⟩
    exact ⟨P a, (hL a).symm⟩
  let hE : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    LinearEquiv.ofBijective (hmap e C) ⟨LinearMap.injective_iff_surjective.2 hsurj, hsurj⟩
  have hex : ∀ z, (F.ex (ik k) P' (hE z)).left = (F.ex (ik k) P z).left :=
    hEU (ik k) P P' hper hper' (LinearEquiv.refl _ _) hE (fun _ _ => rfl) (fun a _ => ⟨0, by simp⟩)
      (fun a => ⟨0, by simp⟩) hL
  have hd := isDerivAt0_comp (fun z => (F.ex (ik k) P z).left) (fun z => (F.ex (ik k) P' z).left) hE hex (hu τ i)
  have hs : hE (Pi.single (e.symm ⟨τ, i⟩) 1) = ∑ b : Fin (Dw.mult τ), C τ b i • (Pi.single (e.symm ⟨τ, b⟩) 1 : Fin g → ℂ) :=
    hmap_single e C τ i
  rw [hs] at hd
  rw [hx']
  exact hEL (ik k) P' hper' _ (fun b => Pi.single (e.symm ⟨τ, b⟩) 1) ((U.un k x').u τ) _ _ (fun b => hu' τ b) hd

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Resize

variable {B : Base}

@[reducible] def preX {P : Pre} (X Y : PreX P) : PreX P := { X with a := Y.a, T_gt := Y.T_gt, a_gt := Y.a_gt, spread_le := Y.spread_le }

theorem preX_eq {P : Pre} {X Y : PreX P} (h : X.piG = Y.piG) (h' : X.piT = Y.piT) : preX X Y = Y := by
  cases X; cases Y; cases h; cases h'; rfl

@[reducible] def colIn {X : PreX B.toPre} (I : ColIn B X) (Y : PreX B.toPre) : ColIn B (preX X Y) :=
  @ColIn.mk B (preX X Y) I.C I.Ch I.sel I.S I.ι I.finι I.tup I.tup_inj I.mu0 I.muStar I.muStar' I.trueColumn_tuple_trivial_eq_one I.xi I.cst I.idx I.J



theorem laws {X : PreX B.toPre} (I : ColIn B X) (Y : PreX B.toPre) (l : TC.Laws I) : TC.Laws (colIn I Y) :=
  ⟨l.pr, l.ch, l.lev, l.per, l.ovr, l.atL, l.fmL, l.xi0, l.idx0, l.bij0, l.lat⟩

variable {f : Top.Fr B.toPre} {T : TwDat B}



@[reducible] def colW (w : ColW B f T) (Y : PreX B.toPre) : ColW B f T where
  px := preX w.px Y
  I := colIn w.I Y
  ok := ⟨w.ok.spaces, w.ok.ch_ok, w.ok.ch_tied, w.ok.weil, w.ok.pibar, w.ok.sel_ok, w.ok.T_mem, w.ok.g_mem, w.ok.ram_mem, w.ok.xi_reads,
    w.ok.xi_star, w.ok.xi_star', w.ok.sharp, w.ok.idx_ok, w.ok.amb_ok, w.ok.duStar⟩
  C_eq := w.C_eq
  S_eq := w.S_eq
  xi_range := w.xi_range
  pins := ⟨w.pins.iX, w.pins.cof⟩
  l := laws w.I Y w.l
  l0 := w.l0
  δ := w.δ
  exact := w.exact
  fld := w.fld
  val := w.val



@[reducible] def dat (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt) :
    R3.Dat (w.st Z) (colIn w.I Y) hX T Wt :=
  @R3.Dat.mk (w.st Z) (preX w.px Y) (colIn w.I Y) hX T Wt z.Xg z.tr z.core z.alg z.alg_eq z.R z.cG z.geo z.pins
    ⟨z.lev.is, z.lev.C, z.lev.xiH, z.lev.Pg, z.lev.Q, z.lev.beta⟩ z.idG z.good z.mu z.fieldValues_mem_fixedField z.Ks_le



theorem pinned {K : Ctx} (w : ColW B f T) (Y : PreX B.toPre) (h : Pinned K B f T w) : Pinned K B f T (colW w Y) := by
  obtain ⟨p⟩ := h
  exact ⟨⟨p.isTw, p.jets, p.hX, p.above, p.half, p.d3b, p.selectedPlacesAgree, p.vals, p.roots⟩⟩



theorem grpAt (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (h : GrpAt (w.st Z) w.I) : GrpAt (w.st Z) (colIn w.I Y) :=
  ⟨h.pl, h.idem, h.cen⟩



theorem fine (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (h : Fine z) : Fine (w := colW w Y) (Z := Z) (dat w Y Z hX Wt z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · with_unfolding_all exact h.1
  · with_unfolding_all exact h.2.1
  · with_unfolding_all exact h.2.2.1
  · have hStd := h.2.2.2
    -- This conversion is much cheaper in the kernel than in elaborator unification.
    run_tac
      let proof ← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `hStd)
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.assign (Lean.mkFVar proof)
      Lean.Elab.Tactic.replaceMainGoal []



theorem holdsL (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (h : HoldsL z.R z.F) : HoldsL (dat w Y Z hX Wt z).R (dat w Y Z hX Wt z).F := (by with_unfolding_all exact (h :))



theorem nonzeroIndexPlaces_adelicDataResized_eq (w : ColW B f T) (Y : PreX B.toPre) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) : (dat w Y Z hX Wt z).W1 (fun _ _ => 0) = z.W1 (fun _ _ => 0) := rfl



theorem seedW {K : Ctx} {P : Pre} {f : Top.Fr P} {F F₀ : IntermediateField ℚ ℂ} {X Y : PreX P} {S : Set ℕ}
    {L : IntermediateField ℚ ℂ} (h : SeedW K P f F F₀ X S L) (hG : X.piG = Y.piG) (hT : X.piT = Y.piT) : SeedW K P f F F₀ Y S L := by
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  subst a1
  have e : w₀.px = X := eq_of_heq a5
  subst e
  refine ⟨B₀, f₀, T₀, colW w₀ Y, Z₀, hX₀, Wt₀, dat w₀ Y Z₀ hX₀ Wt₀ z₀, rfl, a2, a3, a4, heq_of_eq (preX_eq hG hT),
    pinned w₀ Y a6, a7, grpAt w₀ Y Z₀ a8, fine w₀ Y Z₀ hX₀ Wt₀ z₀ a9, holdsL w₀ Y Z₀ hX₀ Wt₀ z₀ a10, ?_, a12⟩
  intro v hv
  have hW := nonzeroIndexPlaces_adelicDataResized_eq w₀ Y Z₀ hX₀ Wt₀ z₀
  exact a11 v (Eq.mp (congrArg (fun s : Set B₀.places.Pl => v ∈ s) hW) hv)

theorem finite_norm_eq {R : Ranks} (H : Formalism.BasicNotions.Host R) (n : ℕ) :
    {x : 𝓞 H.E | (x : H.E) * H.conj (x : H.E) = (n : H.E)}.Finite := by
  have hF := NumberField.Embeddings.finite_of_norm_le H.E ℂ (n + 1 : ℝ)
  refine (hF.preimage (f := fun x : 𝓞 H.E => (x : H.E)) RingOfIntegers.coe_injective.injOn).subset ?_
  intro x hx
  refine ⟨x.isIntegral_coe, fun φ => ?_⟩
  have h1 : φ (H.conj (x : H.E)) = starRingEnd ℂ (φ (x : H.E)) := Formalism.HC.HostAx.conjE_apply _ _ _
  have h2 := congrArg φ hx
  rw [map_mul, h1, map_natCast, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖φ (x : H.E)‖ ^ 2 = (n : ℝ) := by exact_mod_cast h2
  have h4 := norm_nonneg (φ (x : H.E))
  show ‖φ (x : H.E)‖ ≤ (n + 1 : ℝ)
  nlinarith

theorem finite_gens (P : Pre) : (Set.range fun X : PreX P => (X.piG, X.piT)).Finite := by
  have h1 := Set.Finite.pi' fun i : Fin 2 => finite_norm_eq P.host (P.host.g i)
  have h2 := Set.Finite.pi' fun u : P.Word => finite_norm_eq P.host (P.T u)
  refine (h1.prod h2).subset ?_
  rintro _ ⟨X, rfl⟩
  exact ⟨fun i => X.piG_norm i, fun u => X.piT_norm u⟩

theorem exists_gens_LLC (B : Base) : ∃ S₂ : Finset ℂ, (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧
    B.LLC ≤ IntermediateField.adjoin ℚ (S₂ : Set ℂ) := by
  classical
  let b := Module.finBasis ℚ B.LL
  refine ⟨Finset.univ.image fun i => B.embLL (b i), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom B.embLL.toRatAlgHom
  · intro z hz
    obtain ⟨x, rfl⟩ := B.mem_LLC.1 hz
    have e : B.embLL x = ∑ i, (b.repr x i) • B.embLL (b i) := by
      conv_lhs => rw [← b.sum_repr x]

      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact map_rat_smul B.embLL _ _
    rw [e]
    refine sum_mem fun i _ => IntermediateField.smul_mem _ (IntermediateField.subset_adjoin _ _ ?_)
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)



theorem finite_nonzeroIndexPlaces_referenceTuple (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : R3.Dat (w.st Z) w.I hX T Wt) (hH : HoldsL z.R z.F) : (z.W1 fun _ _ => 0).Finite := by
  have hok := hH.ok.ok2
  have hIw : ∀ j, {w' | (R3.s0Of z.R z.F).Iw j (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0}.Finite :=
    fun j => GlobalTheory.Mem.NonzeroPlacesOverPrimes.idx_finite_of_fg _ _ _ (hH.mLat j).fg
      (Formalism.L2.DIV.BlockDat.Tl_lat hok.conj (hok.lifts j _) hok.irr).fg
  have hjw : ∀ j, {w' | Formalism.DivisionValues.jw (((R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0
      (R3.zsOf z.R z.F)).HT j (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.μ0) w'
      (((R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (R3.zsOf z.R z.F)).Tl j
        (R3.famR (w.st Z) w.I hX (R3.usedOf w.I T Wt) z.Xg z.tr).A.μ0) ≠ 0}.Finite :=
    fun j => GlobalTheory.Mem.NonzeroPlacesOverPrimes.jw_finite_of_lat _ (Formalism.L2.DIV.BlockDat.HZ_det hok.conj (hok.lifts j _) hok.irr) _
      (Formalism.L2.DIV.BlockDat.Tl_full hok.conj (hok.lifts j _) hok.irr)
  have hF := Set.finite_iUnion fun j => (hIw j).union (hjw j)
  refine ((hF.preimage (w.st Z).toD7.plEq.injective.injOn).union
    ((hF.preimage GlobalTheory.Mem.NonzeroPlacesOverPrimes.conjPl_injective.injOn).preimage (w.st Z).toD7.plEq.injective.injOn)).subset ?_
  rintro v ⟨j, w', hw', h | h | h⟩
  · rcases hw' with rfl | rfl
    · exact Or.inl (Set.mem_iUnion.2 ⟨j, Or.inl h⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, Or.inl h⟩)
  · rcases hw' with rfl | rfl
    · exact Or.inl (Set.mem_iUnion.2 ⟨j, Or.inr h⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨j, Or.inr h⟩)
  · exact absurd rfl h

theorem seedW_bound {K : Ctx} {P : Pre} {f : Top.Fr P} {F F₀ : IntermediateField ℚ ℂ} {X : PreX P}
    (h : SeedW K P f F F₀ X Set.univ ⊤) : ∃ (S : Finset ℕ) (S₂ : Finset ℂ), (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧
      SeedW K P f F F₀ X (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, -, -⟩ := h
  obtain ⟨S₂, hS₂, hL⟩ := exists_gens_LLC B₀
  have hfin := (finite_nonzeroIndexPlaces_referenceTuple w₀ Z₀ hX₀ Wt₀ z₀ a10).image B₀.places.resChar
  refine ⟨hfin.toFinset, S₂, hS₂, B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, fun v hv => ?_, hL⟩
  rw [Set.Finite.coe_toFinset]
  exact ⟨v, hv, rfl⟩

end GlobalTheory.Mem.R3.Rw.Resize

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lowestVector_evaluation_identifies_levelRows_conj : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ c : ℝ, 0 < c ∧ EvalOn R X h t v₀ c (MultR R F) (conjRows X) := by
  exact GlobalTheory.Mem.SRe.evalOn_all
end
