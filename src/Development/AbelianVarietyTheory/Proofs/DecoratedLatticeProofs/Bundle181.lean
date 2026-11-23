module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle161
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LFun

open NumberField IsDedekindDomain

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_lt_re_dv_arg {a i : ℕ} (hi : i ∈ Finset.range a) {s : ℂ} (hs : 0 < s.re) :
    1 < (2 * s + a - i : ℂ).re := by
  have : (i : ℝ) + 1 ≤ a := by exact_mod_cast Finset.mem_range.1 hi
  simp
  linarith

theorem dv_ne_zero_of_re_pos (a b : ℕ) (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 0 < s.re) :
    dv E a b v s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i hi =>
    inv_ne_zero ((converges_etaFam (E := E) ∅ (b + i) (one_lt_re_dv_arg hi hs)).1 v (Set.notMem_empty v))

theorem dSfun_ne_zero_of_re_pos (S : Set (HeightOneSpectrum (𝓞 F))) (a b : ℕ) {s : ℂ} (hs : 0 < s.re) :
    dSfun E S a b s ≠ 0 := by
  rw [dSfun_eq S a b hs]
  exact Finset.prod_ne_zero_iff.2 fun i hi => (converges_etaFam S (b + i) (one_lt_re_dv_arg hi hs)).ne_zero

theorem differentiableOn_dSfun (S : Set (HeightOneSpectrum (𝓞 F))) (a b : ℕ) :
    DifferentiableOn ℂ (dSfun E S a b) {s | 0 < s.re} := by
  have h : DifferentiableOn ℂ (fun s : ℂ => ∏ i ∈ Finset.range a, etaL E S (b + i) (2 * s + a - i))
      {s | 0 < s.re} := by
    refine DifferentiableOn.fun_finsetProd fun i hi => ?_
    refine (bounded_etaFam (E := E) S (b + i)).differentiableOn.comp
      (f := fun s : ℂ => 2 * s + a - i) (by fun_prop) fun s hs => ?_
    simpa only [zero_add, Set.mem_ofPred_eq] using one_lt_re_dv_arg hi hs
  exact h.congr fun s hs => dSfun_eq S a b hs

end Ext

end GlobalTheory.LFun

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem dSfun_analytic_ne_zero : ∀ (D : D7) (S : Set (FinPl D)) (a b : ℕ), AnalyticOnNhd ℂ (GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b) (rightOf 0) ∧ ∀ s : ℂ, 0 < s.re → GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b s ≠ 0 ∧ (∀ v : FinPl D, GlobalTheory.LFun.dv D.host.E a b v s ≠ 0) ∧ HasProd (fun v : {v : FinPl D // v ∉ S} => GlobalTheory.LFun.dv D.host.E a b v.1 s) (GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b s) := fun _ S a b =>
  ⟨(GlobalTheory.LFun.differentiableOn_dSfun S a b).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re),
    fun _ hs => ⟨GlobalTheory.LFun.dSfun_ne_zero_of_re_pos S a b hs, fun v => GlobalTheory.LFun.dv_ne_zero_of_re_pos a b v hs,
      (GlobalTheory.LFun.hasProd_dv S a b hs).multipliable.hasProd⟩⟩

end GlobalTheory.Core.Rk.IP

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatMoveStd

variable {D : D7}

theorem mt_mul'' (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := by
  show (matHom V (g * g')).1 = (matHom V g).1 * (matHom V g').1
  rw [map_mul, Units.val_mul]

theorem mt_one'' (V : HSp D) : mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  rw [map_one, Units.val_one]

theorem cA_cA'' (x : AE D) : cA D (cA D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a e =>
    show (a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig e)) = _
    rw [show D.sp.cm.sig (D.sp.cm.sig e) = e from star_star e]

theorem unitary (V : HSp D) (hg : V.gram = 1) (g : GA D V) :
    ((mt V g).map (cA D))ᵀ * mt V g = 1 := by
  have h : ((mt V g).map (cA D))ᵀ * V.gram.map (incA D) * mt V g = V.gram.map (incA D) :=
    (g : HR (AF D.host.F) D.sp.cm.sig V.gram).2
  rw [hg, Matrix.map_one (incA D) (map_zero _) (map_one _), Matrix.mul_one] at h
  exact h

theorem mt_inv_eq (V : HSp D) (hg : V.gram = 1) (g : GA D V) : mt V g⁻¹ = ((mt V g).map (cA D))ᵀ := by
  have h1 := unitary V hg g
  have h2 : mt V g * mt V g⁻¹ = 1 := by rw [← mt_mul'', mul_inv_cancel, mt_one'']
  calc mt V g⁻¹ = (((mt V g).map (cA D))ᵀ * mt V g) * mt V g⁻¹ := by rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]



theorem int_of_moves (V : HSp D) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hM : Moves V rfl g N) (x : Fin V.rank → D.host.E) (hx : x ∈ N) (i : Fin V.rank) :
    finPart D ((mt V g⁻¹ *ᵥ fun k => incA D (x k)) i) ∈ intAE D := by
  rw [GlobalTheory.SplitDec.int_iff]
  have := (hM x).1 hx i
  have e : toEAf D ((mt V g⁻¹ *ᵥ fun k => incA D (x k)) i) = (finM V rfl g⁻¹ *ᵥ fun j => eToEAf D (x j)) i := by
    simp only [Matrix.mulVec, dotProduct]

    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]
    rfl
  rw [e]; exact this

theorem gen_eq (α : Af D.host.F) (c x y : D.host.E) :
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * x * y) = (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) * incA D x * incA D y := by
  simp [incA, inclR, Algebra.TensorProduct.tmul_mul_tmul]

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

variable {D : D7}



theorem int_conj (V : HSp D) (hg : V.gram = 1) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hM : Moves V rfl g N) (s : Fin V.rank → D.host.E) (hs : s ∈ N) (j : Fin V.rank) :
    finPart D (∑ l, cA D (incA D (s l)) * mt V g l j) ∈ intAE D := by
  rw [← GlobalTheory.FinPl.FrameLat.cA_int_iff]
  have e : cA D (∑ l, cA D (incA D (s l)) * mt V g l j) = (mt V g⁻¹ *ᵥ fun k => incA D (s k)) j := by

    rw [mt_inv_eq V hg g, map_sum]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, cA_cA'', mul_comm]
  rw [e]; exact int_of_moves V g N hM s hs j

theorem single_mem (S T : HSp D) (hgS : S.gram = 1) (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (c : D.host.E)
    (hc : c ∈ D.host.AA) (i0 : Fin T.rank) (j0 : Fin S.rank) :
    (Matrix.single i0 j0 (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) : WO S T) ∈
      latO S T (intVec D _) (intVec D _) (fun _ => True) := by
  have hint : ∀ {n : ℕ} (k : Fin n), Pi.single k (1 : D.host.E) ∈ intVec D n := by
    intro n k l
    by_cases h : l = k
    · subst h; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne h]; exact isIntegral_zero
  refine AddSubgroup.subset_closure ⟨α, hα, fun _ h => absurd trivial h, c, hc, Pi.single j0 1, hint j0,
    Pi.single i0 1, hint i0, ?_⟩
  ext i j
  rw [Matrix.of_apply, hgS]
  have hsum : ∑ k, star ((Pi.single j0 (1 : D.host.E) : Fin S.rank → D.host.E) k) *
      (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E) k j =
      star ((Pi.single j0 (1 : D.host.E) : Fin S.rank → D.host.E) j) := by
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Matrix.one_apply_eq, mul_one]
  rw [hsum]
  by_cases hi : i = i0
  · subst hi
    by_cases hj : j = j0
    · subst hj
      rw [Matrix.single_apply_same, Pi.single_eq_same, Pi.single_eq_same, star_one, mul_one, mul_one]
    · rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hj), Pi.single_eq_of_ne hj, star_zero, mul_zero,
        TensorProduct.tmul_zero]
  · rw [Matrix.single_apply_of_row_ne (Ne.symm hi), Pi.single_eq_of_ne hi, mul_zero, zero_mul,
      TensorProduct.tmul_zero]

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

variable {D : D7}

theorem row_one {n : ℕ} (s : Fin n → D.host.E) (l : Fin n) :
    ∑ m, star (s m) * (1 : Matrix (Fin n) (Fin n) D.host.E) m l = star (s l) := by
  rw [Finset.sum_eq_single l (fun k _ hk => by rw [Matrix.one_apply_ne hk, mul_zero])
    (fun h => absurd (Finset.mem_univ l) h), Matrix.one_apply_eq, mul_one]



theorem gen_mem (S T : HSp D) (hgS : S.gram = 1) (hgT : T.gram = 1) (g : GA D S) (h : GA D T)
    (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (hN : Moves S rfl g N) (hN' : Moves T rfl h N') (α : Af D.host.F) (hα : α ∈ intAf D.host.F) (c : D.host.E)
    (hc : c ∈ D.host.AA) (s : Fin S.rank → D.host.E) (hs : s ∈ N) (t : Fin T.rank → D.host.E) (ht : t ∈ N') :
    actO S T g⁻¹ h⁻¹ (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j))
      ∈ latO S T (intVec D _) (intVec D _) (fun _ => True) := by
  have e1 : actO S T g⁻¹ h⁻¹
      (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j)) =
      Matrix.of fun i j => ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i * ∑ l, cA D (incA D (s l)) * mt S g l j) *
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] c) := by
    ext i j
    simp only [actO, inv_inv, Matrix.mul_apply, Matrix.of_apply, hgS, row_one, gen_eq,
      ← GlobalTheory.FinPl.FrameLat.cA_incA, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring
  rw [e1, Matrix.matrix_eq_sum_single ((Matrix.of fun i j =>
    ((mt T h⁻¹ *ᵥ fun k => incA D (t k)) i * ∑ l, cA D (incA D (s l)) * mt S g l j) *
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] c)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))]
  refine sum_mem fun i0 _ => sum_mem fun j0 _ => ?_
  rw [Matrix.of_apply, ← smul_eq_mul, ← Matrix.smul_single]
  refine GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ?_ _ (single_mem S T hgS α hα c hc i0 j0)
  rw [map_mul]
  exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE (int_of_moves T h N' hN' t ht i0) (int_conj S hgS g N hN s hs j0)

end GlobalTheory.LatMoveStd

namespace GlobalTheory.LatMoveStd

theorem latO_moved_onto : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True), ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := by
  intro D S T a b hS hT hgS hgT g _ h _ N N' hN hN' u' hu'
  subst hS; subst hT
  refine ⟨actO S T g⁻¹ h⁻¹ u', ?_, ?_⟩
  · let Ψ : WO S T →+ WO S T :=
      { toFun := actO S T g⁻¹ h⁻¹
        map_zero' := by simp only [actO, Matrix.mul_zero, Matrix.zero_mul]
        map_add' := fun x y => by simp only [actO, Matrix.mul_add, Matrix.add_mul] }
    have key : latO S T (latFr S rfl N) (latFr T rfl N') (fun _ => True) ≤
        (latO S T (intVec D _) (intVec D _) (fun _ => True)).comap Ψ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩
      exact gen_mem S T hgS hgT g h N N' hN hN' α hα c hc s hs t ht
    exact key hu'
  · simp only [actO]
    rw [inv_inv, Matrix.mul_assoc (mt T h), Matrix.mul_assoc (mt T h⁻¹ * u'), ← mt_mul'', mul_inv_cancel, mt_one'', Matrix.mul_one,
      ← Matrix.mul_assoc, ← mt_mul'', mul_inv_cancel, mt_one'', Matrix.one_mul]

end GlobalTheory.LatMoveStd
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Core.Mi.ConjEquiv

open GlobalTheory.ConjRowMult Formalism.L2.SG.EvalTOntoRep

theorem conjMap_equiv : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) = rTr (D.sp.Y 0) (atTau θ (D.sp.Y 0) τ g) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t v) := by
  intro _hcl D X h θ S M J χ t c _hS hθ _hgap hιE hM hc Φ hΦ hrep τ g hg v w hw
  obtain ⟨hfin, -, hreal, -⟩ := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h θ hθ hιE
  obtain ⟨ha2, ha1, -⟩ := hreal τ g hg
  set a := iotaX X h (atTau θ (D.sp.Y 0) τ g) with ha
  have hvec : vecC X M c (Function.update v τ w) =
      fun p => X.B.σ p (uMat (a.1 p)) (vecC X M c v p) := by
    refine vecC_eq X M c _ _ fun τ' => ?_
    have e1 : vecC X M c v (X.pl.symm τ') = c τ' (v τ' : M.H τ') := by
      unfold vecC
      exact Equiv.piCongrLeft_apply_apply _ _ _ _
    rw [e1]
    by_cases ht : τ' = τ
    · subst ht
      rw [Function.update_self, hw, hc τ' g hg]
    · rw [Function.update_of_ne ht, ha1 (X.pl.symm τ') (fun e => ht (X.pl.symm.injective e))]
      have h1 : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds (X.pl.symm τ')).2.2.1.1.1
      have h2 : uMat (1 : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ'))) = 1 := rfl
      rw [h2, h1]
      rfl
  have htens : X.B.tens (vecC X M c (Function.update v τ w)) = X.B.σs a.1 (X.B.tens (vecC X M c v)) := by
    rw [hvec, X.B.tens_spec.2.1]
  have haeq : ((a.1, 1) : X.B.I.GA) = a := Prod.ext rfl ha2.symm
  obtain ⟨T, hT, hTΦ⟩ := Submodule.mem_map.1 hΦ
  have hΦx : ∀ x, Φ x = X.B.Re (T x) := fun x => by rw [← hTΦ]; rfl
  have hcomm := (GlobalTheory.IdemProj.re_orth_proj X.B).2.1 a.1
  have key : ∀ x, Φ (X.B.σs a.1 x) = X.B.R a (Φ x) := by
    intro x
    rw [hΦx, hΦx, ← haeq]
    have e1 := congrArg (fun L => L x) (hT a.1)
    simp only [ContinuousLinearMap.comp_apply] at e1
    rw [e1]
    exact congrArg (fun L => L (T x)) hcomm
  obtain ⟨ψ, hψ⟩ := hrep v
  have hψ' : IsContRep X (Φ (X.B.tens (vecC X M c (Function.update v τ w)))) (fun x => ψ (x * a)) := by
    rw [htens, key]
    exact contRep_reg X hψ a
  funext y
  rw [conjMap_apply, contRepL_spec X hψ']
  show _ = conjMap X M c Φ h t v (y * atTau θ (D.sp.Y 0) τ g)
  rw [conjMap_apply, contRepL_spec X hψ]
  congr 1
  have hti : (iotaX X h t⁻¹).1 = 1 := by rw [map_inv, Prod.fst_inv, (hfin t).1 hM.1, inv_one]
  rw [map_mul, map_mul, map_mul, ← ha, mul_assoc]
  beta_reduce
  rw [mul_assoc]
  congr 2
  exact Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, hti, one_mul, mul_one])
    (by rw [Prod.snd_mul, Prod.snd_mul, ha2, one_mul, mul_one])

end GlobalTheory.Core.Mi.ConjEquiv
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.Core.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem castGA_mem_GFset {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    Formalism.L2.SG.RowsJoinPinned.castGA e x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst e; rfl

theorem besGrp_iff_sA (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (g : GA D (D.sp.Y 0)) :
    g ∈ besGrp B.d B.o ↔ (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u := by
  have hS : besGrp B.d B.o = (Formalism.L2.SG.Pf.SAsub X u).comap (iotaX X h).toMonoidHom := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro n hn
        obtain ⟨h1, h2⟩ := (B.tieN n).1 hn
        exact ⟨fun v => (h1 v).1, Formalism.L2.SG.Pf.nfin_sfin X u h2⟩
      · intro g hg
        obtain ⟨h1, h2⟩ := (B.tieH g).1 hg
        exact ⟨hinf_le_sinf X u _ h1, Formalism.L2.SG.Pf.hfin_sfin X u ⟨_, h2⟩⟩
    · intro g hg
      have hg' : (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u := hg
      obtain ⟨hg1, hg2⟩ := hg'
      obtain ⟨hi, hhi, ni, hni, ei⟩ := Formalism.L2.SG.Pf.Sinf.levi X u hg1
      obtain ⟨hf, nf, hnf, ef⟩ := Formalism.L2.SG.Closed.FinLeviC_holds D X u _ hg2
      have hgeq : g = (iotaX X h).symm (hi, (hf : X.B.I.Gf)) * (iotaX X h).symm (ni, nf) := by
        rw [← map_mul, (iotaX X h).eq_symm_apply]
        exact Prod.ext ei ef
      rw [hgeq]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mem_sup_left ?_)
      · refine (B.tieH _).2 ?_
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact ⟨hhi, hf.2⟩
      · refine (B.tieN _).2 ?_
        rw [ContinuousMulEquiv.apply_symm_apply]
        exact ⟨hni, hnf⟩
  rw [hS]; rfl

theorem besGrp_eq_sGroup : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A),
    (∀ g, g ∈ besGrp B.d B.o ↔ (iotaX X h g).1 ∈ X.SinfU u ∧ (iotaX X h g).2 ∈ SfinU X u) ∧
      ∀ g, g ∈ GQ (D.sp.Y 0) ⊓ besGrp B.d B.o ↔ iotaX X h g ∈ Srat X u := by
  intro D X h u ψ A B
  refine ⟨besGrp_iff_sA D X h u ψ A B, fun g => ?_⟩
  rw [Subgroup.mem_inf, besGrp_iff_sA D X h u ψ A B, Formalism.L2.SG.Pf.srat_eq, Subgroup.mem_inf,
    Formalism.MainNotions.LeviCoordinates.rr_mem_GF, Formalism.IndefR.RationalEmbedding.iota_rat]
  have e : iotaX X h g = Formalism.L2.SG.RowsJoinPinned.castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D g) := rfl
  rw [e, castGA_mem_GFset]
  rfl

end GlobalTheory.Core.Mi

end
end

section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem stepLoc1_of_fam (hQ5 : ∀ D : D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39) (hF : StepFam1) : StepLoc1 := by
  intro Cg cb Cw cT CT C0
  obtain ⟨C0n, CSt, hCSt, a₀, b₀, h2⟩ := hF Cg cb Cw cT CT C0
  refine ⟨39, C0n, CSt, hCSt, a₀, b₀, fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq
    Irat Ire hBk ν hν => ?_⟩
  obtain ⟨s, hs1, hs0, hsb, hL⟩ := h2 C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat
    Ire hBk ν hν
  have hk4 : 4 * D.R.rS + 7 ≤ D.R.k := by
    obtain ⟨⟨hH, _, _⟩, _, _⟩ := hc
    unfold Formalism.MainNotions.S.StandingHypotheses at hH
    dsimp only at hH
    obtain ⟨-, -, h3, h4, -⟩ := hH
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    have hmr : 2 * D.R.rS + 2 = D.R.m := by simp only [Formalism.BasicNotions.Ranks.rS]; omega
    have : 2 * D.R.m + 3 ≤ D.R.m ^ 4 := by nlinarith [Nat.pow_le_pow_left hm2 3]
    omega
  have hQ : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound D.R.k D.R.rS ((39 : ℕ) : ℝ) := by
    have := hQ5 D hk4
    exact_mod_cast this
  exact ⟨s, hs1, hs0, hsb, localLeG_of_fam _ _ 39 C0n _ (by omega) hQ hL⟩

end GlobalTheory.Core.One
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem val_eq_zero_imp (D : D7) : MetEx D → ForStage D fun c _ s => ∀ (x : s.CC c) w, w ≠ 0 → PiLocalization₂.val x w = 0 → x = 0 := by
  intro hM c hc j hj s hs x w hw hx
  obtain ⟨ipD, ip, hm⟩ := hM c hc j hj s hs
  have h1 := hm.schur x x w w
  have h0 : Lift.pet s.ν s.fd ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) ((x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w) = 0 := by
    have hx' : (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) w = 0 := hx
    rw [hx']
    simp [Lift.pet]
  rw [h0] at h1
  have hD : ipD w w ≠ 0 := by
    intro h
    have := hm.posD w hw
    rw [h] at this
    simp at this
  have hip : ip x x = 0 := by
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact h
    · exact absurd h hD
  by_contra hne
  have := hm.pos x hne
  rw [hip] at this
  simp at this

end GlobalTheory.ChainOnto
end
