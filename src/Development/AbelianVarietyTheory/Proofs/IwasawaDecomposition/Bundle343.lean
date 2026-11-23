module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharLocalEqInvTypeCharacter
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
public import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2


open Classical GlobalTheory.TopStep in
theorem cosetIn_smul_unitary : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (j : ℕ), X.Ok → Pr.Ok → ∀ (q q' : PtAt R sel mu cst u j) (γ : UF X.E (R.N j)), q'.1.1 = ((γ, 1, 1) : UF X.E (R.N j) × GLG (E := X.E) (n := R.N j) (SG := Pr.vGs) × GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) • q.1.1 → q'.1.2 = (fun z => γ.1 z) '' q.1.2 → cosetIn q' = cosetIn q := by
  intro X Pr R sel S mu cst u j hX hPr q q' γ h1 h2
  funext P
  have key : ∀ y ∈ q.1.2, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ •
      ((frsF sel mu q'.1.1 P).symm (γ.1 y) - (frsF sel mu q.1.1 P).symm y) ∈ stdAt X.E (R.N j) P.1 := by
    intro y hy
    by_cases hP : P.1 ∈ Pr.vGs
    · rw [if_pos hP, pow_zero, inv_one, one_smul]
      by_cases hj : j + 1 = R.m
      swap
      · have h0 : q.1.2 = ∅ := by
          have := q.2
          rw [ysAt_ys_of_ne sel mu cst hj] at this
          exact this
        rw [h0] at hy
        exact absurd hy (Set.notMem_empty y)
      obtain ⟨y0, hy0, hY⟩ := PtAt.mem_ybSet q hj
      have hy' : y - y0 ∈ locLat (rowSG Pr sel mu) q.1.1.deco.1.N
          (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
        rw [hY] at hy
        exact hy
      have hA : (qOf P.1 : X.E) • y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal q.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy0 P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hB : y - y0 ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal q.1.1.deco.1.N := by
        have := Submodule.mem_iInf _ |>.1 hy' P
        rw [Submodule.mem_comap] at this
        simpa [hP] using this
      have hx : (qOf P.1 : X.E) • y ∈ q.1.1.deco.1.at P.1 := by
        have e : (qOf P.1 : X.E) • y = (qOf P.1 : X.E) • y0 + (qOf P.1 : X.E) • (y - y0) := by
          rw [← smul_add, add_sub_cancel]
        rw [e]
        exact add_mem hA (smul_mem_locP (intAt_nat _) hB)
      let w : Pr.vGs := ⟨P.1, hP⟩
      have hd : q'.1.1.deco.1 = q.1.1.deco.1.act γ.1 1 := by
        rw [h1]
        rfl
      have hf : IsLiftFr q.1.1.deco.1 w (q.1.1.deco.1.liftFr w) := liftFr_spec q.1.1.deco.2 w
      have hf' : IsLiftFr (q.1.1.deco.1.act γ.1 1) w (q'.1.1.deco.1.liftFr w) := by
        rw [← hd]
        exact liftFr_spec q'.1.1.deco.2 w
      have e1 : frsF sel mu q.1.1 P = q.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dite_eq_left hP]
      have e2 : frsF sel mu q'.1.1 P = q'.1.1.deco.1.liftFr w := by
        unfold frsF
        rw [dite_eq_left hP]
      rw [e1, e2]
      let κ := passFr γ.1 1 hf hf'
      have hκ : redGL (R.N j) P.1 κ = 1 := redGL_passFr γ.1 1 hf hf'
      set f := q.1.1.deco.1.liftFr w
      set f' := q'.1.1.deco.1.liftFr w
      have e3 : f'.symm (γ.1 y) = κ.1 (f.symm y) := by
        show _ = f'.symm (γ.1 (f (f.symm y)))
        rw [LinearEquiv.apply_symm_apply]
      rw [e3]
      have hv0 : f.symm ((qOf P.1 : X.E) • y) ∈ stdAt X.E (R.N j) P.1 := by
        rw [← hf.1, LinearEquiv.apply_symm_apply]
        exact hx
      rw [map_smul] at hv0
      have hred := redV_redGL κ hv0
      rw [hκ, Units.val_one, Matrix.one_mulVec] at hred
      have hq := (degOneUnram_of_mem_vGs hX hPr hP).2
      have hq0 : (qOf P.1 : X.E) ≠ 0 := qOf_ne_zero
      refine mem_stdAt.2 fun i => ?_
      have hi1 := mem_stdAt.1 (glint_mem κ hv0) i
      have hi2 := mem_stdAt.1 hv0 i
      have hr : redP P.1 ((κ.1 ((qOf P.1 : X.E) • f.symm y) - (qOf P.1 : X.E) • f.symm y) i) = 0 := by
        rw [Pi.sub_apply, reduction_sub hi1 hi2, sub_eq_zero]
        exact congrFun hred i
      have := intAt_div_of_redP hq (intAt_sub hi1 hi2) hr
      convert this using 1
      rw [map_smul]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    · rw [if_neg hP]
      have e : (frsF sel mu q'.1.1 P).symm (γ.1 y) = (frsF sel mu q.1.1 P).symm y := by
        rw [LinearEquiv.symm_apply_eq]
        unfold frsF
        rw [dite_eq_right hP, dite_eq_right hP, h1]
        show γ.1 y = γ.1 (q.1.1.fr _ ((((1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K))) _)⁻¹).1 ((q.1.1.fr _).symm y)))
        simp
      rw [e, sub_self, smul_zero]
      exact zero_mem _
  ext z
  simp only [cosetIn, Set.mem_setOf_eq]
  rw [h2]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
    refine ⟨y, hy, ?_⟩
    have := add_mem hz (key y hy)
    rwa [← smul_add, sub_add_sub_cancel] at this
  · rintro ⟨y, hy, hz⟩
    refine ⟨γ.1 y, ⟨y, hy, rfl⟩, ?_⟩
    have := sub_mem hz (key y hy)
    rwa [← smul_sub, sub_sub_sub_cancel_right] at this

end GlobalTheory.Mem.Col2
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem eventually_map_residue_eq {Γ O : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O]
    [TopologicalSpace O] [IsTopologicalRing O]
    (hO : IsOpen ((IsLocalRing.maximalIdeal O : Ideal O) : Set O)) {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) O) (hM : Continuous M) (g0 : Γ) :
    ∀ᶠ g in nhds g0, (M g).map (IsLocalRing.residue O) = (M g0).map (IsLocalRing.residue O) := by
  have h : ∀ a b, ∀ᶠ g in nhds g0, M g a b - M g0 a b ∈ IsLocalRing.maximalIdeal O := by
    intro a b
    have hc : Continuous fun g => M g a b - M g0 a b := (hM.matrix_elem a b).sub continuous_const
    exact hc.continuousAt.preimage_mem_nhds (hO.mem_nhds (by simp))
  have h2 : ∀ᶠ g in nhds g0, ∀ a b, M g a b - M g0 a b ∈ IsLocalRing.maximalIdeal O := by
    rw [Filter.eventually_all]; intro a; rw [Filter.eventually_all]; exact h a
  filter_upwards [h2] with g hg
  ext a b
  simp only [Matrix.map_apply]
  exact (Ideal.Quotient.eq).2 (hg a b)

theorem sub_mem_nonunits_vs {K : Type} [Field K] (A : ValuationSubring K) {x y : K}
    (hx : x ∈ A.nonunits) (hy : y ∈ A.nonunits) : x - y ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at *
  exact lt_of_le_of_lt (A.valuation.map_sub x y) (max_lt hx hy)

theorem charpoly_coeff_congr_same_place : ∀ (D : D7) (Rw : RowSide D) (Pl : PlSide D) (X : LocNd (lay0 D)) (Y : LocAut X), GlobalTheory.RowTie.ChebSplit D.nd → (∀ i σ w, Y.locW i σ w = Rw.locR σ w) → (∀ (i : X.nd.Loc) (y : X.nd.O i), ∃ h : iotaO X.nd Y.naut i y ∈ Pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (Pl.plκ (X.nd.w i) (IsLocalRing.residue (Pl.plB (X.nd.w i)) ⟨_, h⟩)) = Y.naut.kFbar i (IsLocalRing.residue (X.nd.O i) y)) → ∀ (σ : D.what₂.FT) (i i' : X.nd.Loc), X.nd.w i = X.nd.w i' → ∀ (Sig Sig' : List (Formalism.BasicNotions.Part Y.naut.CG)) (ρ : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i)) (ρ' : G D.host.E X.nd.Om →* GL (Fin D.R.r) (X.nd.O i')), HasParamW X.nd Y.naut i σ Sig → IsRepOfSig X.nd Y.naut i Sig ρ → HasParamW X.nd Y.naut i' σ Sig' → IsRepOfSig X.nd Y.naut i' Sig' ρ' → ∀ (g : G D.host.E X.nd.Om) (n : ℕ), iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) - iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈ (Pl.plB (X.nd.w i)).nonunits := by
  classical
  intro D Rw Pl X Y hCheb hRw hPl σ i i' hw Sig Sig' ρ ρ' hP hR hP' hR' g n
  have key : ∀ (j : X.nd.Loc) (y y' : X.nd.O j), IsLocalRing.residue (X.nd.O j) y = IsLocalRing.residue (X.nd.O j) y' →
      iotaO X.nd Y.naut j y - iotaO X.nd Y.naut j y' ∈ (Pl.plB (X.nd.w j)).nonunits := by
    intro j y y' hyy
    obtain ⟨h1, e1⟩ := hPl j y
    obtain ⟨h2, e2⟩ := hPl j y'
    have hres : IsLocalRing.residue (Pl.plB (X.nd.w j)) ⟨_, h1⟩ = IsLocalRing.residue (Pl.plB (X.nd.w j)) ⟨_, h2⟩ := by
      apply (Pl.plκ (X.nd.w j)).injective
      apply (fbCast (X.nd.w_l j) (D.what₂.places.resChar_prime (X.nd.w j)) (X.nd.lPrime j).out).injective
      rw [e1, e2, hyy]
    have hm := (Ideal.Quotient.eq).1 hres
    have hv := (ValuationSubring.valuation_lt_one_iff _ _).1 hm
    rw [ValuationSubring.mem_nonunits_iff]
    simpa using hv
  have key' := key i'
  rw [← hw] at key'
  have hO : ∀ j, IsOpen ((IsLocalRing.maximalIdeal (X.nd.O j) : Ideal (X.nd.O j)) : Set (X.nd.O j)) := fun j => by
    simpa using (isAdic_iff.1 (X.nd.O_adic j)).1 1
  have hclosed : IsClosed {g : G D.host.E X.nd.Om |
      iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) -
        iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈
        (Pl.plB (X.nd.w i)).nonunits} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro g0 hg0
    have e1 := eventually_map_residue_eq (hO i) (fun g => (ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i))) hR.1 g0
    have e2 := eventually_map_residue_eq (hO i') (fun g => (ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i'))) hR'.1 g0
    filter_upwards [e1, e2] with g h1 h2
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hg0 ⊢
    intro hg
    apply hg0
    have c1 : IsLocalRing.residue (X.nd.O i) ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) =
        IsLocalRing.residue (X.nd.O i) ((ρ g0 : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) := by
      rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpoly_map, ← Matrix.charpoly_map, h1]
    have c2 : IsLocalRing.residue (X.nd.O i') ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) =
        IsLocalRing.residue (X.nd.O i') ((ρ' g0 : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) := by
      rw [← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpoly_map, ← Matrix.charpoly_map, h2]
    have := sub_mem_nonunits_vs _ hg (sub_mem_nonunits_vs _ (key i _ _ c1) (key' _ _ c2))
    convert this using 1
    ring
  have hfin := Filter.eventually_cofinite.1 hR.2.2
  have hfin' := Filter.eventually_cofinite.1 hR'.2.2
  have hdense := hCheb (hfin.toFinset ∪ hfin'.toFinset)
  have hE := hdense.mono (s₂ := {g : G D.host.E X.nd.Om |
      iotaO X.nd Y.naut i ((ρ g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i)).charpoly.coeff n) -
        iotaO X.nd Y.naut i' ((ρ' g : Matrix (Fin D.R.r) (Fin D.R.r) (X.nd.O i')).charpoly.coeff n) ∈
        (Pl.plB (X.nd.w i)).nonunits}) (fun s hs => by
    obtain ⟨w, hwS, hsplit, B, hB, hF⟩ := hs
    simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_or, not_not] at hwS
    obtain ⟨q1, q2⟩ := hwS
    have r1 := q1 B s hB hF
    have r2 := q2 B s hB hF
    have eqloc : isoLoc X.nd Y.naut Sig w = isoLoc X.nd Y.naut Sig' w :=
      (hP.2.2 w hsplit).trans ((hRw i σ w).trans ((hRw i' σ w).symm.trans (hP'.2.2 w hsplit).symm))
    rw [Set.mem_setOf_eq, ← Polynomial.coeff_map, ← Polynomial.coeff_map, r1, r2, eqloc, sub_self, ValuationSubring.mem_nonunits_iff,
      map_zero]
    exact zero_lt_one)
  have hc := hE.closure_eq
  rw [hclosed.closure_eq] at hc
  exact Set.eq_univ_iff_forall.1 hc g

end GlobalTheory.HeightCounting
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.LocW

theorem pos_add {x y : WithTop ℤ} (hx : 0 ≤ x) (hy : 0 < y) : 0 < x + y := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe m =>
    induction y using WithTop.recTopCoe with
    | top => simp
    | coe k =>
      have h1 : (0:ℤ) ≤ m := by exact_mod_cast hx
      have h2 : (0:ℤ) < k := by exact_mod_cast hy
      exact_mod_cast (by omega : (0:ℤ) < m + k)

variable {K : Type} [Field K] [NumberField K] (Pl : Rows.Places K) (w : Pl.Pl)

theorem val_nonneg_int (a : 𝓞 K) : (0 : WithTop ℤ) ≤ Pl.val w (a : K) := by
  let v : Valuation K (Multiplicative (WithTop ℤ)ᵒᵈ) := Pl.val w
  have hi : IsIntegral ℤ (a : K) := RingOfIntegers.isIntegral_coe a
  have h2 : IsIntegral v.integer (a : K) := hi.tower_top
  exact (Valuation.integer.integers v).mem_of_integral h2

def primeW : Ideal (𝓞 K) where
  carrier := {a | (0 : WithTop ℤ) < Pl.val w (a : K)}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact lt_of_lt_of_le (lt_min ha hb) (AddValuation.map_add _ _ _)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at *
    exact pos_add (val_nonneg_int Pl w c) ha

theorem mem_primeW (a : 𝓞 K) : a ∈ primeW Pl w ↔ (0 : WithTop ℤ) < Pl.val w (a : K) := Iff.rfl

theorem val_eq_zero_of_not_mem (a : 𝓞 K) (ha : a ∉ primeW Pl w) : Pl.val w (a : K) = 0 := by
  rw [mem_primeW, not_lt] at ha
  exact le_antisymm ha (val_nonneg_int Pl w a)

instance primeW_isPrime : (primeW Pl w).IsPrime where
  ne_top' := by
    intro h
    have : (1 : 𝓞 K) ∈ primeW Pl w := h ▸ Submodule.mem_top
    rw [mem_primeW] at this
    simp at this
  mem_or_mem' := by
    intro a b hab
    by_contra hn
    push Not at hn
    have ha := val_eq_zero_of_not_mem Pl w a hn.1
    have hb := val_eq_zero_of_not_mem Pl w b hn.2
    rw [mem_primeW] at hab
    simp only [map_mul, AddValuation.map_mul, ha, hb, add_zero] at hab
    exact lt_irrefl _ hab

theorem primeW_ne_bot : primeW Pl w ≠ ⊥ := by
  intro h
  have hl : ((Pl.resChar w : ℕ) : 𝓞 K) ∈ primeW Pl w := by
    rw [mem_primeW]
    push_cast
    rw [Pl.val_resChar w]
    exact WithTop.coe_lt_coe.mpr (by have := Pl.ramIdx_pos w; omega)
  rw [h, Submodule.mem_bot] at hl
  have := (Pl.resChar_prime w).ne_zero
  exact this (by exact_mod_cast hl)

theorem exists_den (t : K) (ht : (0 : WithTop ℤ) ≤ Pl.val w t) :
    ∃ a s : 𝓞 K, Pl.val w (s : K) = 0 ∧ (s : K) * t = a := by
  have hS : (primeW Pl w).primeCompl ≤ nonZeroDivisors (𝓞 K) :=
    Ideal.primeCompl_le_nonZeroDivisors _
  let R := Localization.subalgebra.ofField K (primeW Pl w).primeCompl hS
  have : IsLocalization.AtPrime R (primeW Pl w) :=
    Localization.subalgebra.isLocalization_ofField K _ hS
  have : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) (primeW_ne_bot Pl w) R
  have memR : ∀ r : R, ∃ a s : 𝓞 K, s ∉ primeW Pl w ∧ (r : K) = (a : K) * (s : K)⁻¹ := by
    intro r
    obtain ⟨a, s, hs, e⟩ := r.2
    exact ⟨a, s, hs, e⟩
  rcases eq_or_ne t 0 with h0 | h0
  · exact ⟨0, 1, by simp, by simp [h0]⟩
  rcases ValuationRing.isInteger_or_isInteger R t with ⟨r, hr⟩ | ⟨r, hr⟩
  · obtain ⟨a, s, hs, e⟩ := memR r
    have hs0 : (s : K) ≠ 0 := by
      intro h; apply hs; rw [mem_primeW, h]; simp
    refine ⟨a, s, val_eq_zero_of_not_mem Pl w s hs, ?_⟩
    have : (r : K) = t := hr
    rw [← this, e]; field_simp
  · obtain ⟨a, s, hs, e⟩ := memR r
    have hs0 : (s : K) ≠ 0 := by
      intro h; apply hs; rw [mem_primeW, h]; simp
    have hrt : (r : K) = t⁻¹ := hr
    by_cases ha : a ∈ primeW Pl w
    · exfalso
      have hat : (a : K) = t⁻¹ * s := by rw [← hrt, e]; field_simp
      have h1 : Pl.val w (a : K) = Pl.val w t⁻¹ := by
        rw [hat, AddValuation.map_mul, val_eq_zero_of_not_mem Pl w s hs, add_zero]
      have h2 : Pl.val w t + Pl.val w t⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ h0, AddValuation.map_one]
      rw [mem_primeW, h1] at ha
      have := pos_add ht ha
      rw [h2] at this
      exact lt_irrefl _ this
    · have ha0 : (a : K) ≠ 0 := by
        intro h; apply ha; rw [mem_primeW, h]; simp
      refine ⟨s, a, val_eq_zero_of_not_mem Pl w a ha, ?_⟩
      have : t = (s : K) * (a : K)⁻¹ := by
        rw [← inv_inv t, ← hrt, e]; field_simp
      rw [this]; field_simp

end GlobalTheory.LocW


open GlobalTheory.LocW in
theorem GlobalTheory.Mem.Col2.GStep.locW_latOf_iff : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (Pl : Rows.Places K) (w : Pl.Pl) (p : ℕ) [Fact p.Prime] (iL : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖iL x‖ ≤ 1) → ∀ x : S.FormsK emb lam h, x ∈ locW Pl w (S.latOf emb lam h fun c => delAtr emb lam (S.Lsh c.1 (S.rep c))) ↔ ∀ c, x.1 c ∈ locW Pl w (delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
  intro E K ι _ _ _ _ _ _ _ n S emb lam h Pl w p _ iL _ x
  classical
  letI : Fintype S.Cl := h.fintypeCl
  have smulK : ∀ (b : 𝓞 K) (v : VV K lam), b • v = (b : K) • v := fun b v =>
    (algebraMap_smul K b v).symm
  constructor
  · intro hx c
    unfold locW at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (hy c)
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul t y _ hy => exact Submodule.smul_mem _ t hy
  · intro hall
    have gen : ∀ (M : Submodule (𝓞 K) (VV K lam)) (y : VV K lam),
        y ∈ Submodule.span (intW Pl w) (M : Set (VV K lam)) →
        ∃ s : 𝓞 K, Pl.val w (s : K) = 0 ∧ s • y ∈ M := by
      intro M y hy
      induction hy using Submodule.span_induction with
      | mem v hv => exact ⟨1, by simp, by rw [smulK]; push_cast; rw [one_smul]; exact hv⟩
      | zero => exact ⟨1, by simp, by rw [smulK, smul_zero]; exact Submodule.zero_mem _⟩
      | add u v _ _ hu hv =>
        obtain ⟨s1, h1, m1⟩ := hu
        obtain ⟨s2, h2, m2⟩ := hv
        refine ⟨s1 * s2, by push_cast; rw [AddValuation.map_mul, h1, h2, add_zero], ?_⟩
        have e0 : (s1 * s2) • (u + v) = (s1 * s2) • u + (s1 * s2) • v := by
          rw [smulK, smulK, smulK, smul_add]
        rw [e0]
        have e1 : (s1 * s2) • u = s2 • (s1 • u) := by
          rw [smulK, smulK, smulK, smul_smul]; push_cast; rw [mul_comm]
        have e2 : (s1 * s2) • v = s1 • (s2 • v) := by
          rw [smulK, smulK, smulK, smul_smul]; push_cast; rfl
        rw [e1, e2]
        exact Submodule.add_mem _ (Submodule.smul_mem _ s2 m1) (Submodule.smul_mem _ s1 m2)
      | smul t u _ hu =>
        obtain ⟨s, hs, m⟩ := hu
        obtain ⟨a, s', hs', e⟩ := exists_den Pl w (t : K) t.2
        refine ⟨s' * s, by push_cast; rw [AddValuation.map_mul, hs, hs', add_zero], ?_⟩
        have : (s' * s) • (t • u) = a • (s • u) := by
          rw [smulK, smulK, smulK, Subring.smul_def, smul_smul, smul_smul, ← e]
          congr 1
          push_cast
          ring
        rw [this]
        exact Submodule.smul_mem _ a m
    have key : ∀ c, ∃ s : 𝓞 K, Pl.val w (s : K) = 0 ∧
        s • x.1 c ∈ delAtr emb lam (S.Lsh c.1 (S.rep c)) := fun c => gen _ _ (hall c)
    have common : ∀ F : Finset S.Cl, ∃ s : 𝓞 K, Pl.val w (s : K) = 0 ∧
        ∀ c ∈ F, s • x.1 c ∈ delAtr emb lam (S.Lsh c.1 (S.rep c)) := by
      intro F
      induction F using Finset.induction_on with
      | empty => exact ⟨1, by simp, by simp⟩
      | insert c F _ ih =>
        obtain ⟨s1, h1, m1⟩ := ih
        obtain ⟨s2, h2, m2⟩ := key c
        refine ⟨s1 * s2, by push_cast; rw [AddValuation.map_mul, h1, h2, add_zero], ?_⟩
        intro c' hc'
        rcases Finset.mem_insert.mp hc' with rfl | hc'
        · have e : (s1 * s2) • x.1 c' = s1 • (s2 • x.1 c') := by
            rw [smulK, smulK, smulK, smul_smul]; push_cast; rfl
          rw [e]; exact Submodule.smul_mem _ s1 m2
        · have e : (s1 * s2) • x.1 c' = s2 • (s1 • x.1 c') := by
            rw [smulK, smulK, smulK, smul_smul]; push_cast; rw [mul_comm]
          rw [e]; exact Submodule.smul_mem _ s2 (m1 c' hc')
    obtain ⟨s, hs, hsm⟩ := common Finset.univ
    have hsx : s • x ∈ S.latOf emb lam h (fun c => delAtr emb lam (S.Lsh c.1 (S.rep c))) := by
      intro c
      exact hsm c (Finset.mem_univ c)
    have hs0 : (s : K) ≠ 0 := by
      intro h0; rw [h0, AddValuation.map_zero] at hs; exact WithTop.top_ne_zero hs
    have hinv : Pl.val w (s : K)⁻¹ = 0 := by
      have := AddValuation.map_mul (Pl.val w) (s : K) (s : K)⁻¹
      rw [mul_inv_cancel₀ hs0, AddValuation.map_one, hs, zero_add] at this
      exact this.symm
    let u : intW Pl w := ⟨(s : K)⁻¹, by show (0 : WithTop ℤ) ≤ _; rw [hinv]⟩
    have hx : x = u • (s • x) := by
      apply Subtype.ext
      funext c
      show x.1 c = (s : K)⁻¹ • (s • x.1 c)
      rw [smulK, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [hx]
    unfold locW
    exact Submodule.smul_mem _ u (Submodule.subset_span hsx)
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts


theorem _root_.GlobalTheory.T.analyticFibre_description_levelMove_marking_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ (gM : Dw.La →ₗ[𝓞 E] Dw.La) (y y' : FrPt Xo c ℂ), levR (gM, (LinearMap.id : Dw.La →ₗ[𝓞 E] Dw.La)) y y' → ∀ A : AnFib X bas idx e x L y, ∃ A' : AnFib X bas idx e x L y', (∀ th, A.Reads 1 y.s th → A'.Reads 1 y'.s th) ∧ ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), A.Marked mk → A'.Marked (mk ∘ₗ gM) := by
  first | exact @GlobalTheory.Dict.FibreMove.anFib_levR_id | exact GlobalTheory.Dict.FibreMove.anFib_levR_id | (intros; apply GlobalTheory.Dict.FibreMove.anFib_levR_id <;> assumption)
end
