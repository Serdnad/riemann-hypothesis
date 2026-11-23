module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle155
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle157
public import Mathlib.RepresentationTheory.Intertwining
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle154
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
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle136

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistDecomp

variable {D : D7}

theorem adj_eq' {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) : adj D A = Aᴴ := rfl

theorem frame_relations {V V' : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    (h1 : adj D C * V.gram * C' = 1) (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) :
    adj D C' * V.gram * C = 1 ∧ (V'.gram⁻¹ * adj D B * V.gram) * C = 0 ∧
    (V'.gram⁻¹ * adj D B * V.gram) * C' = 0 ∧ (V'.gram⁻¹ * adj D B * V.gram) * B = 1 ∧
    adj D C * V.gram * C = 0 ∧
    C * (adj D C' * V.gram) + (B * (V'.gram⁻¹ * adj D B * V.gram) + C' * (adj D C * V.gram)) = 1 := by
  have hG : V.gramᴴ = V.gram := GlobalTheory.MixModel.gram_conjTranspose V
  have hC : Cᴴ * V.gram * C = 0 := by
    have e : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C = Cᴴ := adj_eq' C
    have := hs.frame.2.2
    rwa [e] at this
  have hB := hs.isom
  have hCB := hs.orth
  simp only [adj_eq'] at hB hCB h1 h2 h3 ⊢

  have hC'C : C'ᴴ * V.gram * C = 1 := by
    have := congrArg Matrix.conjTranspose h1
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hBC : Bᴴ * V.gram * C = 0 := by
    have := congrArg Matrix.conjTranspose hCB
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hBC' : Bᴴ * V.gram * C' = 0 := by
    have := congrArg Matrix.conjTranspose h3
    simpa [Matrix.conjTranspose_mul, hG, Matrix.mul_assoc] using this
  have hG' : V'.gram⁻¹ * V'.gram = 1 := Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V')
  have hPC : V'.gram⁻¹ * Bᴴ * V.gram * C = 0 := by
    simp only [Matrix.mul_assoc] at hBC ⊢; rw [hBC, Matrix.mul_zero]
  have hPC' : V'.gram⁻¹ * Bᴴ * V.gram * C' = 0 := by
    simp only [Matrix.mul_assoc] at hBC' ⊢; rw [hBC', Matrix.mul_zero]
  have hPB : V'.gram⁻¹ * Bᴴ * V.gram * B = 1 := by
    simp only [Matrix.mul_assoc] at hB ⊢; rw [hB, hG']
  refine ⟨hC'C, hPC, hPC', hPB, hC, ?_⟩

  set P := V'.gram⁻¹ * Bᴴ * V.gram with hP
  let M : Matrix (Fin V.rank) (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) D.host.E := Matrix.fromCols C (Matrix.fromCols B C')
  let N : Matrix (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) (Fin V.rank) D.host.E :=
    Matrix.fromRows (C'ᴴ * V.gram) (Matrix.fromRows P (Cᴴ * V.gram))
  have hNM : N * M = 1 := by
    simp only [N, M, Matrix.fromRows_mul, Matrix.mul_fromCols]
    ext (i | i | i) (j | j | j) <;>
      simp [hC'C, hPC, hPC', hPB, hC, h1, h2, h3, hCB, Matrix.one_apply]
  have hcard : Fintype.card (Fin r ⊕ (Fin V'.rank ⊕ Fin r)) = Fintype.card (Fin V.rank) := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    have := hs.rank
    omega
  have hMN : M * N = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).mp hNM
  simpa [M, N, Matrix.fromCols_mul_fromRows] using hMN



theorem decomp_exists : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∃ e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W, (∀ t y x, e (t, y, x) = isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∧ ∀ t y x, e (t, y, x) ∈ ratL W V ↔ t ∈ ratMx D W.rank r ∧ y ∈ ratMx D W.rank r ∧ x ∈ ratL W V' := by
  intro D V V' W r C B hs C' h1 h2 h3
  obtain ⟨hC'C, hPC, hPC', hPB, hCC, hid⟩ := frame_relations hs h1 h2 h3
  have hV'r := GlobalTheory.MixModel.ratL_eq W V'
  have hVr := GlobalTheory.MixModel.ratL_eq W V

  set f := incA D with hf
  set a := (adj D C' * V.gram).map f with ha
  set c := (adj D C * V.gram).map f with hc
  set p := (V'.gram⁻¹ * adj D B * V.gram).map f with hp
  set u := C.map f with hu
  set u' := C'.map f with hu'
  set b := B.map f with hb
  have m1 : ∀ {k l m : ℕ} (X : Matrix (Fin k) (Fin l) D.host.E) (Y : Matrix (Fin l) (Fin m) D.host.E),
      X.map f * Y.map f = (X * Y).map f := fun X Y => (Matrix.map_mul).symm
  have z0 : ∀ {k l : ℕ}, (0 : Matrix (Fin k) (Fin l) D.host.E).map f = 0 := Matrix.map_zero _ (map_zero f)
  have o1 : ∀ {k : ℕ}, (1 : Matrix (Fin k) (Fin k) D.host.E).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)
  have au : a * u = 1 := by rw [ha, hu, m1, hC'C, o1]
  have cu : c * u = 0 := by rw [hc, hu, m1, hCC, z0]
  have pu : p * u = 0 := by rw [hp, hu, m1, hPC, z0]
  have au' : a * u' = 0 := by rw [ha, hu', m1, h2, z0]
  have cu' : c * u' = 1 := by rw [hc, hu', m1, h1, o1]
  have pu' : p * u' = 0 := by rw [hp, hu', m1, hPC', z0]
  have ab : a * b = 0 := by rw [ha, hb, m1, h3, z0]
  have cb : c * b = 0 := by rw [hc, hb, m1, hs.orth, z0]
  have pb : p * b = 1 := by rw [hp, hb, m1, hPB, o1]
  have key : u * a + (b * p + u' * c) = 1 := by
    rw [ha, hc, hp, hu, hu', hb, m1, m1, m1, ← Matrix.map_add f (map_add f), ← Matrix.map_add f (map_add f), hid, o1]

  have fwd : ∀ (t : Mx D W.rank r) (y : Mx D W.rank r) (x : WO V' W),
      isoPart V W C' t + isoPart V W C y + midPart V V' W B x = t * a + y * c + x * p := fun _ _ _ => rfl
  have back : ∀ (t : Mx D W.rank r) (y : Mx D W.rank r) (x : WO V' W),
      (t * a + y * c + x * p) * u = t ∧ (t * a + y * c + x * p) * u' = y ∧
        (t * a + y * c + x * p) * b = x := by
    intro t y x
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Matrix.add_mul, Matrix.mul_assoc, au, cu, pu, au', cu', pu', ab, cb, pb, Matrix.mul_one,
        Matrix.mul_zero, add_zero, zero_add]
  have cont : ∀ {k l m : ℕ} (Q : Mx D l m), Continuous fun z : Mx D k l => z * Q := by
    intro k l m Q
    exact continuous_id.matrix_mul continuous_const
  haveI := (GlobalTheory.MixModel.lattice_Mx D W.rank V.rank).1
  let e : (Mx D W.rank r × Mx D W.rank r × WO V' W) ≃ₜ+ WO V W :=
    { toFun := fun q => isoPart V W C' q.1 + isoPart V W C q.2.1 + midPart V V' W B q.2.2
      invFun := fun w => (w * u, w * u', w * b)
      left_inv := by
        rintro ⟨t, y, x⟩
        simp only [fwd]
        rw [(back t y x).1, (back t y x).2.1, (back t y x).2.2]
      right_inv := by
        intro w
        simp only [fwd]
        calc w * u * a + w * u' * c + w * b * p = w * (u * a + (b * p + u' * c)) := by
              simp only [Matrix.mul_add, Matrix.mul_assoc]; abel
          _ = w := by rw [key, Matrix.mul_one]
      map_add' := by
        rintro ⟨t, y, x⟩ ⟨t', y', x'⟩
        simp only [fwd, Prod.mk_add_mk, Matrix.add_mul]
        abel
      continuous_toFun := by
        simp only [fwd]
        exact (((cont a).comp continuous_fst).add ((cont c).comp (continuous_fst.comp continuous_snd))).add
          ((cont p).comp (continuous_snd.comp continuous_snd))
      continuous_invFun := ((cont u).prodMk ((cont u').prodMk (cont b))) }
  refine ⟨e, fun t y x => rfl, fun t y x => ?_⟩
  change isoPart V W C' t + isoPart V W C y + midPart V V' W B x ∈ ratL W V ↔ _
  rw [fwd, hVr, hV'r]
  have hr : ∀ {k l : ℕ} (X : Matrix (Fin k) (Fin l) D.host.E), X.map f ∈ GlobalTheory.MixModel.ratMx D k l :=
    fun X => GlobalTheory.MixModel.rat_mem X
  have hmul : ∀ {k l m : ℕ} {X : Mx D k l} {Y : Mx D l m},
      X ∈ GlobalTheory.MixModel.ratMx D k l → Y ∈ GlobalTheory.MixModel.ratMx D l m →
      X * Y ∈ GlobalTheory.MixModel.ratMx D k m := by
    intro k l m X Y hX hY
    obtain ⟨A, rfl⟩ := hX
    obtain ⟨B, rfl⟩ := hY
    change A.map f * B.map f ∈ GlobalTheory.MixModel.ratMx D k m
    rw [m1]
    exact hr (A * B)
  constructor
  · intro h
    obtain ⟨b1, b2, b3⟩ := back t y x
    refine ⟨?_, ?_, ?_⟩
    · rw [← b1]; exact hmul h (hr C)
    · rw [← b2]; exact hmul h (hr C')
    · rw [← b3]; exact hmul h (hr B)
  · rintro ⟨ht, hy, hx⟩
    exact add_mem (add_mem (hmul ht (hr _)) (hmul hy (hr _)))
      (hmul hx (hr _))

end GlobalTheory.TwistDecomp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix

noncomputable section

namespace GlobalTheory.LeviNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def phase (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y u : Mx D W.rank r) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D)
    (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace))

def resNorm (ψ : AddChar (AF D.host.F) ℂ) (V V' W : HSp D) {r : ℕ} (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)) (f : WO V W → ℂ) (u : Mx D W.rank r) : ℂ :=
  ∫ x in 𝓕', GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x *
    starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x) ∂μ'

theorem phase_apply (ψ : AddChar (AF D.host.F) ℂ) (W : HSp D) {r : ℕ} (y u : Mx D W.rank r) :
    phase ψ W y u = ψ (Algebra.trace (AF D.host.F) (AE D)
      (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace)) := rfl

end GlobalTheory.LeviNorm

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistFormsOrth

variable {D : D7}

theorem hO_mul_rat_eq_zero (V W : HSp D) {r s : ℕ} (a : Mx D W.rank r) (b : Mx D W.rank s)
    (R : Matrix (Fin r) (Fin V.rank) D.host.E) (Q : Matrix (Fin s) (Fin V.rank) D.host.E)
    (h : R * V.gram⁻¹ * Qᴴ = 0) :
    hO V W (a * GlobalTheory.MixModel.rat R) (b * GlobalTheory.MixModel.rat Q) = 0 := by
  rw [GlobalTheory.MixModel.hO_eq_trace, GlobalTheory.MixModel.adj_mul, ← GlobalTheory.MixModel.rat_conjTranspose]
  have hz : GlobalTheory.MixModel.rat R * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Qᴴ) = 0 := by
    rw [GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, ← Matrix.mul_assoc, h,
      GlobalTheory.MixModel.rat_zero]
  have e : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.rat Qᴴ * GlobalTheory.MixModel.adj b * (GlobalTheory.MixModel.gA W * (a * GlobalTheory.MixModel.rat R)))
      = GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Qᴴ * (GlobalTheory.MixModel.adj b * (GlobalTheory.MixModel.gA W * a)) * GlobalTheory.MixModel.rat R := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.trace_zero]

theorem symplO_mul_rat_eq_zero (V W : HSp D) {r s : ℕ} (a : Mx D W.rank r) (b : Mx D W.rank s)
    (R : Matrix (Fin r) (Fin V.rank) D.host.E) (Q : Matrix (Fin s) (Fin V.rank) D.host.E)
    (h : R * V.gram⁻¹ * Qᴴ = 0) :
    symplO V W (a * GlobalTheory.MixModel.rat R) (b * GlobalTheory.MixModel.rat Q) = 0 := by
  rw [GlobalTheory.MixModel.symplO_eq, hO_mul_rat_eq_zero V W a b R Q h, mul_zero, map_zero]

theorem frame_pair (V : HSp D) {r s : ℕ} (C₁ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (C₂ : Matrix (Fin V.rank) (Fin s) D.host.E) :
    adj D C₁ * V.gram * V.gram⁻¹ * (adj D C₂ * V.gram)ᴴ = adj D C₁ * V.gram * C₂ := by
  have hG := GlobalTheory.MixModel.gram_isUnit_det V
  simp only [adj, GlobalTheory.MixModel.cT_sig, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hG]

theorem frame_mid (V V' : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (h : adj D C * V.gram * B = 0) :
    adj D C * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
  have hG := GlobalTheory.MixModel.gram_isUnit_det V
  simp only [adj, GlobalTheory.MixModel.cT_sig] at h ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    GlobalTheory.MixModel.gramInv_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hG]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.zero_mul]

theorem orthogonal : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → (∀ a b, symplO V W (isoPart V W C a) (isoPart V W C b) = 0) ∧ (∀ a x, symplO V W (isoPart V W C a) (midPart V V' W B x) = 0) ∧ (∀ a x, symplO V W (isoPart V W C' a) (midPart V V' W B x) = 0) ∧ (∀ a b, symplO V W (isoPart V W C' a) (isoPart V W C' b) = 0) := by
  intro D V V' W r C B hs C' _ hC' hC'B
  have hC : adj D C * V.gram * C = 0 := hs.frame.2.2
  refine ⟨fun a b => ?_, fun a x => ?_, fun a x => ?_, fun a b => ?_⟩
  · exact symplO_mul_rat_eq_zero V W a b (adj D C * V.gram) (adj D C * V.gram) ((frame_pair V C C).trans hC)
  · exact symplO_mul_rat_eq_zero V W a x (adj D C * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (frame_mid V V' C B hs.orth)
  · exact symplO_mul_rat_eq_zero V W a x (adj D C' * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (frame_mid V V' C' B hC'B)
  · exact symplO_mul_rat_eq_zero V W a b (adj D C' * V.gram) (adj D C' * V.gram) ((frame_pair V C' C').trans hC')

end GlobalTheory.TwistFormsOrth

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.ResCont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem continuous_bounded_setIntegral {X Y : Type} [TopologicalSpace X] [FirstCountableTopology X] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure Y) (s : Set Y) (hs : μ s < ⊤) (F : X → Y → ℂ)
    (hc : Continuous fun q : X × Y => F q.1 q.2) (K : ℝ) (hb : ∀ x y, ‖F x y‖ ≤ K) :
    Continuous (fun x => ∫ y in s, F x y ∂μ) ∧ ∀ x, ‖∫ y in s, F x y ∂μ‖ ≤ K * (μ.restrict s).real Set.univ := by
  haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs.ne
  refine ⟨?_, fun x => norm_integral_le_of_norm_le_const (.of_forall fun y => hb x y)⟩
  refine continuous_of_dominated (bound := fun _ => K) (fun x => ?_) (fun x => .of_forall fun y => hb x y)
    (integrable_const K) (.of_forall fun y => ?_)
  · exact (hc.comp (continuous_const.prodMk continuous_id) : Continuous fun y => F x y).aestronglyMeasurable
  · exact (hc.comp (continuous_id.prodMk continuous_const) : Continuous fun x => F x y)

theorem res_heisO_continuous_bounded : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 →
    ∀ f, IsThetaFunO ψ V W f →
    Continuous (fun p : WO V' W × Mx D W.rank r =>
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' p.2) f) p.1) ∧
    ∃ M : ℝ, ∀ x u, ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) f) x‖ ≤ M := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 h𝓨 f hf
  obtain ⟨K, hK⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
  have hn : ∀ z, ‖ψ z‖ = 1 := hψ.1.2.1
  have hfin : μ 𝓨 < ⊤ := by rw [h𝓨.2.2]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (μ.restrict 𝓨) := isFiniteMeasure_restrict.2 hfin.ne
  obtain ⟨-, -, i3, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  obtain ⟨-, -, j3, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank V'.rank
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : OpensMeasurableSpace (Mx D W.rank r) := BorelSpace.opensMeasurable
  haveI : SecondCountableTopology (WO V' W × Mx D W.rank r) := @TopologicalSpace.instSecondCountableTopologyProd _ _ _ _ j3 i3
  haveI : FirstCountableTopology (WO V' W × Mx D W.rank r) :=
    TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _
  have hiso : ∀ (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E),
      Continuous (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C₀) := fun C₀ =>
    Continuous.matrix_mul continuous_id continuous_const
  have hmid : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B) :=
    Continuous.matrix_mul continuous_id continuous_const
  have hFb : ∀ (p : WO V' W × Mx D W.rank r) (y : Mx D W.rank r),
      ‖heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' p.2) f
        (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B p.1)‖ ≤ K := fun p y => by
    simp only [heisO, norm_mul, hn, one_mul]
    exact hK _
  have ha : Continuous fun q : (WO V' W × Mx D W.rank r) × Mx D W.rank r =>
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C q.2 + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B q.1.1 :=
    ((hiso C).comp continuous_snd).add (hmid.comp (continuous_fst.comp continuous_fst))
  have hb : Continuous fun q : (WO V' W × Mx D W.rank r) × Mx D W.rank r =>
      GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' q.1.2 := (hiso C').comp (continuous_snd.comp continuous_fst)
  have hFc : Continuous fun q : (WO V' W × Mx D W.rank r) × Mx D W.rank r =>
      heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' q.1.2) f
        (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C q.2 + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B q.1.1) :=
    (hψ.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH ha hb)).mul (hf.cont.comp (ha.add hb))
  have h := continuous_bounded_setIntegral μ 𝓨 hfin _ hFc K hFb
  exact ⟨h.1, _, fun x u => h.2 (x, u)⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ResCont

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.normLineDecompositionsOfBaseSpace_proof : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RecordDecSt D := by
  first | exact @GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec | exact GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec | (intros; apply GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  first | exact @GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal | exact GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal | (intros; apply GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.hermitianStdIsometry_of_rationalIsometry : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D → GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.StdIsomSt D := by
  first | exact @GlobalTheory.StdIsom.stdIsomSt_of_rationalSt | exact GlobalTheory.StdIsom.stdIsomSt_of_rationalSt | (intros; apply GlobalTheory.StdIsom.stdIsomSt_of_rationalSt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isSelfDualC_hyperbolicExtensionLattice_conjStable : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (ρ : ℕ) (e f : Fin ρ → Y.V), GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsDec Y X ι (fun _ : Fin 1 => z) (-GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.Tu D u) e f → ∀ L, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsSDIn Y (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.flatSp Y X ι z) L → ∀ nn, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable nn → Formalism.IndefR.Datum.IsSelfDualC Y (Formalism.L2.Herm.crdLat Y (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.lamN Y e f L nn)) := by
  first | exact @GlobalTheory.HypLattice.isSelfDualC_lamN | exact GlobalTheory.HypLattice.isSelfDualC_lamN | (intros; apply GlobalTheory.HypLattice.isSelfDualC_lamN <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ w : WO S T, ∃ P₀ : Finset (Place D), ∀ P : Finset (Place D), P₀ ⊆ P → ∃ u ∈ (latO S T ΛS ΛT fun _ => True), w = ∑ p ∈ P, wAt p w + 2 • u := by
  first | exact @GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul | exact GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul | (intros; apply GlobalTheory.PlaceTensor.CompDecomp.exists_eq_sum_wAt_add_two_smul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.splitIdempotent_prime_projection_correspondence : ∀ (D : D7), (∀ (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (v : FinPl D) (φ : SplitProj D v), IsIdemOf φ e ∧ IsProjAt φ PP) ∧ ∀ (v : FinPl D) (φ : SplitProj D v) (PP : Formalism.L2.DIV.Pl D.host.E), IsProjAt φ PP → PP.asIdeal.under (𝓞 D.host.F) = v.asIdeal ∧ (∀ PP', IsProjAt φ PP' → PP' = PP) ∧ ∀ e, IsIdemOf φ e → Formalism.L2.NTheta.IsIdemAt e PP ∧ (∀ e', Formalism.L2.NTheta.IsIdemAt e' PP → e' = e) ∧ ∀ φ' : SplitProj D v, IsIdemOf φ' e → φ' = φ := by
  first | exact @GlobalTheory.SplitIdemDict.idem_dictionary | exact GlobalTheory.SplitIdemDict.idem_dictionary | (intros; apply GlobalTheory.SplitIdemDict.idem_dictionary <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.tensor_representation_intertwiner_compat : ∀ (Γ A B C D X Y : Type) [Monoid Γ] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (a : Representation ℂ Γ A) (b : Representation ℂ Γ B) (c : Representation ℂ Γ C) (d : Representation ℂ Γ D) (x : Representation ℂ Γ X) (y : Representation ℂ Γ Y) (p : A ⊗[ℂ] C →ₗ[ℂ] X) (q : B ⊗[ℂ] D →ₗ[ℂ] Y), Function.Surjective p → Function.Surjective q → (∀ g u w, p (a g u ⊗ₜ[ℂ] c g w) = x g (p (u ⊗ₜ[ℂ] w))) → (∀ g u w, q (b g u ⊗ₜ[ℂ] d g w) = y g (q (u ⊗ₜ[ℂ] w))) → (∀ l : Module.Dual ℂ (A ⊗[ℂ] C), (∀ g, b g = 1 → d g = 1 → ∀ u w, l (a g u ⊗ₜ[ℂ] c g w) = l (u ⊗ₜ[ℂ] w)) → ∀ z, p z = 0 → l z = 0) → (∀ l : Module.Dual ℂ (B ⊗[ℂ] D), (∀ g, a g = 1 → c g = 1 → ∀ u w, l (b g u ⊗ₜ[ℂ] d g w) = l (u ⊗ₜ[ℂ] w)) → ∀ z, q z = 0 → l z = 0) → Module.finrank ℂ (invFun (a.tprod (b.tprod (c.tprod d)))) = Module.finrank ℂ (invFun (x.tprod y)) := by
  first | exact @GlobalTheory.OneFunctional.finrank_invFun_two_contractions | exact GlobalTheory.OneFunctional.finrank_invFun_two_contractions | (intros; apply GlobalTheory.OneFunctional.finrank_invFun_two_contractions <;> assumption)
end

section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

theorem _root_.GlobalTheory.T.nonempty_invFun_dual_tprod_equiv_intertwiningMap : ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (σ : Representation ℂ G W), Nonempty (invFun (ρ.dual.tprod σ) ≃ₗ[ℂ] σ.IntertwiningMap ρ) := by
  first | exact @GlobalTheory.OneFunctional.nonempty_invFun_dual_tprod_equiv | exact GlobalTheory.OneFunctional.nonempty_invFun_dual_tprod_equiv | (intros; apply GlobalTheory.OneFunctional.nonempty_invFun_dual_tprod_equiv <;> assumption)
end
