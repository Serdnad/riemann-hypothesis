module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle013
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle284
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle282
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle271
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle029
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead.CyclotomicLifting

variable {D : D7}

theorem adj_mem {R : Type} [CommRing R] (T : Subring R) {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, A i j ∈ T) (i j : Fin n) : A.adjugate i j ∈ T := by
  let A' : Matrix (Fin n) (Fin n) T := fun a b => ⟨A a b, h a b⟩
  have e : T.subtype.mapMatrix A' = A := by ext a b; rfl
  rw [← e, ← RingHom.map_adjugate]
  exact (A'.adjugate i j).2

theorem loc_inv (Q : Pl D.host.E) {n : ℕ} (A : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E))
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hd : Valued.v A.det = 1) :
    ∃ A' : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E), (∀ i j, Valued.v (A' i j) ≤ 1) ∧ A * A' = 1 := by
  have h0 : A.det ≠ 0 := fun h => by rw [h, map_zero] at hd; exact zero_ne_one hd
  refine ⟨A⁻¹, fun i j => ?_, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 h0)⟩
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', map_mul, map_inv₀, hd, inv_one, one_mul]
  have := adj_mem (Q.adicCompletionIntegers D.host.E).toSubring A (fun a b => by
    change A a b ∈ Q.adicCompletionIntegers D.host.E
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hA a b) i j
  change A.adjugate i j ∈ Q.adicCompletionIntegers D.host.E at this
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem glob {n : ℕ} (c c' : ∀ Q : Pl D.host.E, Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E))
    (hc : ∀ Q i j, Valued.v (c Q i j) ≤ 1) (hc' : ∀ Q i j, Valued.v (c' Q i j) ≤ 1) (h1 : ∀ Q, c Q * c' Q = 1) :
    ∃ C : GL (Fin n) (EAf D), (∀ i j, C.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      (∀ i j, (C⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      ∀ Q i j, GlobalTheory.StdFrames.cpt (D := D) Q ((C⁻¹).val i j) = c' Q i j := by
  choose z hzO hz using fun p : Fin n × Fin n => GlobalTheory.AdIsom.exists_of_cpt (D := D) (fun Q => c Q p.1 p.2) (fun Q => hc Q p.1 p.2)
  choose z' hzO' hz' using fun p : Fin n × Fin n => GlobalTheory.AdIsom.exists_of_cpt (D := D) (fun Q => c' Q p.1 p.2) (fun Q => hc' Q p.1 p.2)
  let Z : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => z (i, j)
  let Z' : Matrix (Fin n) (Fin n) (EAf D) := Matrix.of fun i j => z' (i, j)
  have hmul : Z * Z' = 1 := by
    ext i j
    refine GlobalTheory.StdFrames.cpt_ext fun Q => ?_
    have e := congrArg (fun M => M i j) (h1 Q)
    simp only [Matrix.mul_apply] at e ⊢

    rw [map_sum]
    simp only [map_mul, Z, Z', Matrix.of_apply, hz, hz']
    rw [e, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨⟨Z, Z', hmul, mul_eq_one_comm.1 hmul⟩, fun i j => hzO (i, j), fun i j => hzO' (i, j),
    fun Q i j => hz' (i, j) Q⟩

theorem col_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) (EAf D)) (w : Fin n → Fin n → EAf D) (i j : Fin n) :
    (A * colMat w) i j = Matrix.mulVec A (w j) i := by
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat]

theorem res_eq (Q : Pl D.host.E) (x : EAf D) (hmem : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (δ : Formalism.L2.Herm.intAf D.host.F D.host.E) (hcpt : GlobalTheory.StdFrames.cpt Q x = GlobalTheory.StdFrames.cpt Q (δ : EAf D)) :
    Formalism.L2.DIV.resS D.host.F Q ⟨x, hmem⟩ = Formalism.L2.DIV.resS D.host.F Q δ := by
  have e0 : (⟨x, hmem⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨x - δ, sub_mem hmem δ.2⟩ + δ := Subtype.ext (by simp)
  have e1 := (GlobalTheory.AdIsom.resS_eq_zero_iff_cpt (D := D) Q ⟨x - δ, sub_mem hmem δ.2⟩).2 (by
    change Valued.v (GlobalTheory.StdFrames.cpt Q (x - δ)) < 1
    rw [map_sub, hcpt, sub_self, map_zero]
    exact zero_lt_one)
  rw [e0, (Formalism.L2.DIV.resS D.host.F Q).map_add, e1, zero_add]

end GlobalTheory.SeeConjRead.CyclotomicLifting

namespace GlobalTheory.SeeConjRead



open GlobalTheory.SeeConjRead.CyclotomicLifting in
theorem exists_lift_redIs : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (S : Finset (Pl D.host.E)) (W : Pl D.host.E → Fin n → Fin n → EAf D), (∀ Q ∈ S, ∀ i j, ((β₀⁻¹).val * colMat (W Q)) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ Q ∈ S, Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * colMat (W Q)).det) = 1) → ∃ β : GL (Fin n) (EAf D), GlobalTheory.NormSum.AdLattice.lat β = GlobalTheory.NormSum.AdLattice.lat β₀ ∧ ∀ Q ∈ S, RedIs β Q (W Q) := by
  intro D n β₀ S W hint hdet
  have hloc : ∀ Q : Pl D.host.E, ∃ c c' : Matrix (Fin n) (Fin n) (Q.adicCompletion D.host.E),
      (∀ i j, Valued.v (c i j) ≤ 1) ∧ (∀ i j, Valued.v (c' i j) ≤ 1) ∧ c * c' = 1 ∧
      (Q ∈ S → c = ((β₀⁻¹).val * colMat (W Q)).map (GlobalTheory.StdFrames.cpt Q)) := by
    intro Q
    by_cases hQ : Q ∈ S
    · have hA : ∀ i j, Valued.v ((((β₀⁻¹).val * colMat (W Q)).map (GlobalTheory.StdFrames.cpt Q)) i j) ≤ 1 :=
        fun i j => (GlobalTheory.AdIsom.mem_OA _).1 (hint Q hQ i j) Q
      have hd : Valued.v (((β₀⁻¹).val * colMat (W Q)).map (GlobalTheory.StdFrames.cpt Q)).det = 1 := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
        exact hdet Q hQ
      obtain ⟨A', hA', h1⟩ := loc_inv Q _ hA hd
      exact ⟨_, A', hA, hA', h1, fun _ => rfl⟩
    · refine ⟨1, 1, fun i j => ?_, fun i j => ?_, one_mul _, fun h => absurd h hQ⟩ <;>
      · rw [Matrix.one_apply]; split_ifs <;> simp
  choose c c' hc hc' h1 hS using hloc
  obtain ⟨C, hCi, hCi', hCc⟩ := glob c c' hc hc' h1
  refine ⟨β₀ * C, le_antisymm (GlobalTheory.NormSum.AdLattice.lat_le_of_int fun i j => ?_)
    (GlobalTheory.NormSum.AdLattice.lat_le_of_int fun i j => ?_), fun Q hQ i j => ?_⟩
  · rw [inv_mul_cancel_left]; exact hCi i j
  · rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]; exact hCi' i j
  have key : Matrix.mulVec ((β₀ * C)⁻¹).val (W Q j) i = ((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j := by
    rw [← Matrix.mul_assoc, col_apply, mul_inv_rev, Units.val_mul]
  rw [key]
  have hmem : ((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hCi' i k) (hint Q hQ k j)
  refine ⟨hmem, ?_⟩
  have hcpt : GlobalTheory.StdFrames.cpt Q (((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    have e : c' Q * c Q = 1 := mul_eq_one_comm.1 (h1 Q)
    rw [hS Q hQ] at e

    rw [← e, Matrix.mul_apply, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, hCc]
    rfl
  split_ifs with hij
  · have h1' : GlobalTheory.StdFrames.cpt Q (((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j) =
        GlobalTheory.StdFrames.cpt Q ((1 : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      rw [hcpt, Matrix.one_apply, if_pos hij]
      exact (map_one _).symm
    exact (res_eq Q _ hmem 1 h1').trans (map_one _)
  · have h0' : GlobalTheory.StdFrames.cpt Q (((C⁻¹).val * ((β₀⁻¹).val * colMat (W Q))) i j) =
        GlobalTheory.StdFrames.cpt Q ((0 : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := by
      rw [hcpt, Matrix.one_apply, if_neg hij]
      exact (map_zero _).symm
    exact (res_eq Q _ hmem 0 h0').trans (map_zero _)

end GlobalTheory.SeeConjRead
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjRead

theorem smallAt_natCast_mul {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal) {t : EAf D}
    (ht : t ∈ GlobalTheory.StdFrames.OA D) : SmallAt PP ((N : EAf D) * t) := by
  unfold SmallAt
  rw [map_mul, map_natCast, Valuation.map_mul]
  have hv : Valued.v (N : PP.adicCompletion D.host.E) < 1 := by
    have := (PP.valuation_lt_one_iff_mem (K := D.host.E) (N : 𝓞 D.host.E)).2 hN
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at this
    simpa using this
  have ht' := (GlobalTheory.AdIsom.mem_OA t).1 ht PP
  exact lt_of_le_of_lt (mul_le_of_le_one_right' ht') hv

theorem sg_hY {D : D7} (x y : Fin (Yc D 0).rank → EAf D) : GlobalTheory.StdFrames.sg D (hY D x y) = hY D y x := by
  have := GlobalTheory.AdIsom.cjA_hA (Yc D 0) y x
  rw [GlobalTheory.AdIsom.hA_eq, GlobalTheory.AdIsom.hA_eq] at this
  exact this

theorem smallAt_of_mul {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal) {c : EAf D}
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, c = (N : EAf D) * t) : SmallAt PP c := by
  obtain ⟨t, ht, rfl⟩ := h
  exact smallAt_natCast_mul hN ht

theorem smallAt_hY_of_swap {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {x y : Fin (Yc D 0).rank → EAf D} {d : EAf D} (hd : GlobalTheory.StdFrames.sg D d = d)
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x - d = (N : EAf D) * t) : SmallAt PP (hY D x y - d) := by
  obtain ⟨t, ht, e⟩ := h
  have e' := congrArg (GlobalTheory.StdFrames.sg D) e
  rw [map_sub, sg_hY, hd, map_mul, map_natCast] at e'
  rw [e']
  exact smallAt_natCast_mul hN (GlobalTheory.AdIsom.cjA_mem ht)

theorem smallAt_hY_of_swap0 {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {x y : Fin (Yc D 0).rank → EAf D} (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x = (N : EAf D) * t) :
    SmallAt PP (hY D x y) := by
  have := smallAt_hY_of_swap hN (x := x) (y := y) (d := 0) (map_zero _) (by simpa using h)
  simpa using this

theorem smallAt_hY_of_swap_delta {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {ι : Type} [DecidableEq ι] {a c : ι} {x y : Fin (Yc D 0).rank → EAf D}
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, hY D y x - (if c = a then 1 else 0) = (N : EAf D) * t) :
    SmallAt PP (hY D x y - if a = c then 1 else 0) := by
  refine smallAt_hY_of_swap hN (by split_ifs <;> simp) ?_
  simpa only [eq_comm (a := a)] using h

theorem smallAt_sub_of_cpt {D : D7} {PP : Pl D.host.E} {N : ℕ} (hN : (N : 𝓞 D.host.E) ∈ PP.asIdeal)
    {ι : Type} [DecidableEq ι] {i j : ι} {c e : EAf D} (he : GlobalTheory.StdFrames.cpt PP e = 1)
    (h : ∃ t ∈ GlobalTheory.StdFrames.OA D, c - (if i = j then e else 0) = (N : EAf D) * t) :
    SmallAt PP (c - if i = j then 1 else 0) := by
  obtain ⟨t, ht, e'⟩ := h
  have h1 : GlobalTheory.StdFrames.cpt PP (c - if i = j then 1 else 0) = GlobalTheory.StdFrames.cpt PP ((N : EAf D) * t) := by
    rw [← e']
    split_ifs <;> simp [he]
  have h2 := smallAt_natCast_mul hN ht
  unfold SmallAt at h2 ⊢
  rwa [h1]

theorem pairTable_of_cpt_one : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 → PairTable (hY D) (SmallAt PP) (e0T X h) (f0T X h) (bwT X h) (bwdT X h) (z0T X h) := by
  intro D X h PP hg hew
  have F0g := X.gramIntegral
  have F0z := X.formsAtZero
  have F0W := X.weightVectorsIntegral
  have bd := X.bw_dual
  have ge := X.g_eq
  rcases X with ⟨⟨I⟩⟩
  dsimp only at h F0g F0z F0W bd ge hew ⊢
  subst h
  subst ge
  refine ⟨fun a c => smallAt_hY_of_swap_delta hg (F0g c a).2.2, fun a j => smallAt_of_mul hg ((F0W j).2.2 a).2.1,
    fun a => smallAt_of_mul hg (F0z.2 a).2, fun a c => smallAt_of_mul hg (F0g a c).2.1,
    fun i a => smallAt_hY_of_swap0 hg ((F0W i).2.2 a).2.2.1, fun i j => smallAt_sub_of_cpt hg hew (bd i j),
    fun i => smallAt_hY_of_swap0 hg (F0W i).2.1, fun i a => smallAt_hY_of_swap0 hg ((F0W i).2.2 a).2.2.2,
    fun a => smallAt_hY_of_swap0 hg (F0z.2 a).1, fun j => smallAt_of_mul hg (F0W j).1, smallAt_of_mul hg F0z.1,
    fun a => smallAt_hY_of_swap0 hg (F0z.2 a).2, fun a c => smallAt_of_mul hg (F0g a c).1,
    fun a j => smallAt_of_mul hg ((F0W j).2.2 a).1, fun a => smallAt_of_mul hg (F0z.2 a).1,
    fun a c => smallAt_of_mul hg (F0g a c).2.2⟩

end GlobalTheory.SeeConjRead
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjAdj
open GlobalTheory.SeeConjChar Matrix
variable {D : D7}

theorem hform_unitary {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J : Matrix n n A) {M : GL n A} (hM : M ∈ Formalism.UG.UJ σ J) (u v : n → A) :
    Formalism.UG.hform σ J (M.val *ᵥ u) (M.val *ᵥ v) = Formalism.UG.hform σ J u v := by
  have e2 : ∀ a b, Formalism.UG.hform σ J a b = (σ ∘ a) ⬝ᵥ J *ᵥ b := by
    intro a b
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : σ ∘ (M.val *ᵥ u) = (σ ∘ u) ᵥ* Formalism.UG.cT σ M.val := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  have hM' : Formalism.UG.cT σ M.val * J * M.val = J := hM
  rw [e2, e2, e3, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM']

theorem eq_of_kill {R : Type} [CommRing R] (PP : Pl D.host.E) (f : Formalism.L2.Herm.intAf D.host.F D.host.E →+* R)
    (hf : ∀ p ∈ PP.asIdeal, f (oToS D.host.F D.host.E p) = 0) (s : Formalism.L2.Herm.intAf D.host.F D.host.E)
    (b : 𝓞 D.host.E) (hb : s - oToS D.host.F D.host.E b ∈ idS D.host.F PP.asIdeal) :
    f s = f (oToS D.host.F D.host.E b) := by
  have hle : idS D.host.F PP.asIdeal ≤ RingHom.ker f := by
    unfold idS
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    exact hf p hp
  have := hle hb
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
  exact this

theorem ext_oToS {R : Type} [CommRing R] (PP : Pl D.host.E) (f g : Formalism.L2.Herm.intAf D.host.F D.host.E →+* R)
    (hfg : ∀ a, f (oToS D.host.F D.host.E a) = g (oToS D.host.F D.host.E a))
    (hg : ∀ p ∈ PP.asIdeal, g (oToS D.host.F D.host.E p) = 0) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    f s = g s := by
  obtain ⟨bq, hb⟩ := cmpS_surj (F := D.host.F) PP.asIdeal PP.ne_bot (Ideal.Quotient.mk _ s)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bq
  change Ideal.Quotient.mk _ (oToS D.host.F D.host.E b) = _ at hb
  have hb' : s - oToS D.host.F D.host.E b ∈ idS D.host.F PP.asIdeal := by
    rw [← Ideal.Quotient.eq]
    exact hb.symm
  have h1 := eq_of_kill PP f (fun p hp => (hfg p).trans (hg p hp)) s b hb'
  have h2 := eq_of_kill PP g hg s b hb'
  rw [h1, h2, hfg]

noncomputable def cjS (D : D7) : Formalism.L2.Herm.intAf D.host.F D.host.E →+* Formalism.L2.Herm.intAf D.host.F D.host.E :=
  (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D).restrict (Formalism.L2.Herm.intAf D.host.F D.host.E) (Formalism.L2.Herm.intAf D.host.F D.host.E)
    (fun _ h => GlobalTheory.AdIsom.cjA_mem h)

theorem cjS_oToS (a : 𝓞 D.host.E) :
    cjS D (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (GlobalTheory.IdemSupport.cO D a) := Subtype.ext rfl

theorem resT_cjA (PP : Pl D.host.E) (z : EAf D) :
    resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z) = conjRes PP (resT PP z) := by
  by_cases hz : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E
  · have hz' : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := GlobalTheory.AdIsom.cjA_mem hz
    rw [resT, dite_eq_left hz', resT, dite_eq_left hz]
    let f1 : Formalism.L2.Herm.intAf D.host.F D.host.E →+* kP (GlobalTheory.IdemSupport.cP PP) :=
      (resS D.host.F (GlobalTheory.IdemSupport.cP PP)).comp (cjS D)
    let f2 : Formalism.L2.Herm.intAf D.host.F D.host.E →+* kP (GlobalTheory.IdemSupport.cP PP) :=
      (conjRes PP).toRingHom.comp (resS D.host.F PP)
    have hO : ∀ a : 𝓞 D.host.E, f1 (oToS D.host.F D.host.E a) = f2 (oToS D.host.F D.host.E a) := by
      intro a
      show resS D.host.F (GlobalTheory.IdemSupport.cP PP) (cjS D (oToS D.host.F D.host.E a)) =
        conjRes PP (resS D.host.F PP (oToS D.host.F D.host.E a))
      rw [cjS_oToS, resS_oToS, resS_oToS]
      exact (Ideal.quotientEquiv_mk _ _ _ _ _).symm
    have hg : ∀ p ∈ PP.asIdeal, f2 (oToS D.host.F D.host.E p) = 0 := by
      intro p hp
      show conjRes PP (resS D.host.F PP (oToS D.host.F D.host.E p)) = 0
      rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    have hfin := ext_oToS PP f1 f2 hO hg ⟨z, hz⟩
    have e : (⟨GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z, hz'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = cjS D ⟨z, hz⟩ := Subtype.ext rfl
    rw [e]
    exact hfin
  · have hz' : GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D z ∉ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun h => hz (GlobalTheory.AdIsom.cjA_mem_iff.1 h)
    rw [resT, dite_eq_right hz', resT, dite_eq_right hz, map_zero]

theorem resCP_adjoint : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (PP : Pl D.host.E) (κ : GA D (Yc D 0)) (x y : Fin (Yc D 0).rank → EAf D), (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧ GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.hT X h x (Matrix.mulVec (finE (Yc D 0) κ).val y)) = GlobalTheory.SeeConjChar.conjRes PP (GlobalTheory.SeeConjChar.resT PP (GlobalTheory.SeeConjChar.hT X h y (Matrix.mulVec ((finE (Yc D 0) κ)⁻¹).val x))) := by
  intro D X h PP κ x y
  have hH : ∀ u v, GlobalTheory.SeeConjChar.hT X h u v =
      Formalism.UG.hform (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D) ((Yc D 0).gram.map (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D)) u v := by
    intro u v
    obtain ⟨⟨I⟩⟩ := X
    dsimp only at h
    subst h
    rfl
  have hU : finE (Yc D 0) κ ∈
      Formalism.UG.UJ (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D) ((Yc D 0).gram.map (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D)) := by
    have hf := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
    rw [(Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ] at hf
    have := ((Formalism.IndefR.RationalEmbedding.iota D κ).2).2
    exact hf ▸ this
  have key : GlobalTheory.SeeConjChar.hT X h x ((finE (Yc D 0) κ).val *ᵥ y) =
      GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D (GlobalTheory.SeeConjChar.hT X h y (((finE (Yc D 0) κ)⁻¹).val *ᵥ x)) := by
    rw [hH, hH]
    have e1 : x = (finE (Yc D 0) κ).val *ᵥ (((finE (Yc D 0) κ)⁻¹).val *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have e2 := GlobalTheory.AdIsom.cjA_hA (Yc D 0) (((finE (Yc D 0) κ)⁻¹).val *ᵥ x) y
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.hA] at e2
    rw [e2]
    conv_lhs => rw [e1]
    exact hform_unitary _ _ hU _ _
  rw [key]
  exact ⟨GlobalTheory.AdIsom.cjA_mem_iff, resT_cjA PP _⟩

end GlobalTheory.SeeConjAdj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CocompactIntegrable

theorem integrableOn_of_cocompact {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : G, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (F : G → ℂ) (hF : Continuous F)
    (hinv : ∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) : IntegrableOn F 𝓕 μ := by
  have hle : μ 𝓕 ≤ μ C := by
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro h hh
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hh⟩
  have hfin : μ 𝓕 ≠ ⊤ := (hle.trans_lt hC.measure_lt_top).ne
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  refine Measure.integrableOn_of_bounded (M := M) hfin hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
  rw [hinv γ hγ]
  exact hM c hc

theorem integrableOn_fundamentalDomain : ∀ {D : D7} (V : HSp D) (μ : Measure (GA D V)) (𝓕 C : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → IsCompact C → (∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c) → ∀ F : GA D V → ℂ, Continuous F → (∀ γ ∈ GQ V, ∀ h, F (γ * h) = F h) → IntegrableOn F 𝓕 μ := by
  intro D V μ 𝓕 C hμ h𝓕 hC hcov F hF hinv
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  exact integrableOn_of_cocompact (GQ V) μ 𝓕 C h𝓕 hC hcov F hF hinv

end GlobalTheory.CocompactIntegrable
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie


theorem _root_.GlobalTheory.T.isIdemAt_conj_of_other_prime_over_split : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w w' : HeightOneSpectrum (𝓞 D.host.E)), w ≠ w' → w.under (𝓞 D.host.F) = v → w'.under (𝓞 D.host.F) = v → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → Formalism.L2.NTheta.IsIdemAt (cA D ε) w' := by
  first | exact @GlobalTheory.ConjSplitIdem.isIdemAt_cA_of_ne | exact GlobalTheory.ConjSplitIdem.isIdemAt_cA_of_ne | (intros; apply GlobalTheory.ConjSplitIdem.isIdemAt_cA_of_ne <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem coefA_dual_coef_continuousOn :
    ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ (τ : D.what₂.Tau) (f : Module.Dual ℂ c.W) (v : c.W), ContinuousOn (fun g => f (c.ρ (atTau θ V τ g)⁻¹ v)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  intro D V θ c hθ hc τ f v
  letI := c.nW
  letI := c.iW
  haveI := c.fW
  have h1 : Continuous fun h : GA D V => c.ρ h v := hc.2.2.1 v
  have hinv : Continuous (fun h : GA D V => h⁻¹) := continuous_inv
  have hf : Continuous f := LinearMap.continuous_of_finiteDimensional f
  exact (hf.comp (h1.comp hinv)).comp_continuousOn (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ)

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.mem_symmetricPositionLevel_firstSpace_iff : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (β : GL (Fin (Yc D 0).rank) (EAf D)) (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (κ : GA D (Yc D 0)), (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) ↔ κ ∈ GfC (Yc D 0) ∧ finE (Yc D 0) κ ∈ UA D.sp.cm (Yc D 0).gram ∧ finE (Yc D 0) κ ∈ St β ∧ ∀ PP ∈ Lc.Pg, upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unipSym (kP PP) D.R.r D.R.rS D.R.k) ∧ (κ ∈ levS (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) → levChi (Yc D 0) β (Lc.dat0 (PsharpSym Lc.Pg D.R.r D.R.rS D.R.k ψ0)) κ = ∏ PP ∈ Lc.Pg, ψ0 PP (edgeSum (symEdge D.R.rS D.R.k) (upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ))))) := by
  first | exact @GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff | exact GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff | (intros; apply GlobalTheory.SeeConjRead.mem_levS_dat0_PsharpSym_iff <;> assumption)
end
