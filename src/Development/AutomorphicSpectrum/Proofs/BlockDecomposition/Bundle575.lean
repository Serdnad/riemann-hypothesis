module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1441
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle208
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle008
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle566
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDiagonalDoubleCosets
public import Mathlib.Topology.Algebra.Group.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle567
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle492
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CompanionTheory.EulerV

open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finite_above (v : PlF E) : Finite (Above v) := by
  by_cases h : Nonempty (Above v)
  · obtain ⟨u⟩ := h
    refine Finite.of_injective (β := (GlobalTheory.EulerTw.orb E u.1 : Finset (Pl E)))
      (fun w => ⟨w.1, (GlobalTheory.EulerTwRestr.mem_orb_iff u.1 w.1).2 (w.2.trans u.2.symm)⟩) ?_
    intro x y hxy
    exact Subtype.ext (congrArg (fun z => z.1) hxy)
  · haveI := not_nonempty_iff.1 h
    infer_instance

def pn (n : ℕ) (v : PlF E) : GL (Fin n) (Af E) →* GL (Fin n) (Av v) := GeneralLinearGroup.map (projv v)

def ev {v : PlF E} (w : Above v) : GL (Fin n) (Av v) →* GLw n w.1 :=
  GeneralLinearGroup.map (Pi.evalRingHom (fun w : Above v => w.1.adicCompletion E) w)

def Kn (n : ℕ) (v : PlF E) : Subgroup (GL (Fin n) (Av v)) :=
  ⨅ w : Above v, (GlobalTheory.LFun.KGL w.1 (n := n)).comap (ev w)

theorem mem_Kn {v : PlF E} {y : GL (Fin n) (Av v)} : y ∈ Kn n v ↔ ∀ w : Above v, ev w y ∈ GlobalTheory.LFun.KGL w.1 (n := n) := by
  simp only [Kn, Subgroup.mem_iInf, Subgroup.mem_comap]

theorem ev_pn {v : PlF E} (w : Above v) (g : GL (Fin n) (Af E)) :
    ev w (pn n v g) = GeneralLinearGroup.map (pLoc E w.1) g := rfl

theorem mem_Kv {a b : ℕ} {v : PlF E} {y : Yv a b v} : y ∈ Kv a b v ↔ y.1 ∈ Kn a v ∧ y.2 ∈ Kn b v := by
  simp only [Kv, Subgroup.mem_iInf, Subgroup.mem_comap, mem_Kn, Subgroup.mem_prod, forall_and]
  rfl

theorem mem_Kf_iff {g : GL (Fin n) (Af E)} : g ∈ Kf E n ↔ ∀ v : PlF E, pn n v g ∈ Kn n v := by
  have h : g ∈ Kf E n ↔ ∀ w : Pl E, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
    simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap]
  rw [h]
  refine ⟨fun H v => mem_Kn.2 fun w => H w.1, fun H w => ?_⟩
  exact mem_Kn.1 (H (w.under (𝓞 (maximalRealSubfield E)))) ⟨w, rfl⟩

theorem continuous_projv (v : PlF E) : Continuous (projv v) :=
  continuous_pi fun w => RestrictedProduct.continuous_eval w.1

theorem continuous_pn (v : PlF E) : Continuous (pn n v) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_projv v))

theorem continuous_ev {v : PlF E} (w : Above v) : Continuous (ev (n := n) w) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id (continuous_apply w))

theorem isOpen_Kn (v : PlF E) : IsOpen (Kn n v : Set (GL (Fin n) (Av v))) := by
  haveI := finite_above v
  rw [Kn, Subgroup.coe_iInf]
  exact isOpen_iInter_of_finite fun w =>
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w.1 n).1.preimage (continuous_ev w)

theorem pn_ext {g h : GL (Fin n) (Af E)} (H : ∀ v : PlF E, pn n v g = pn n v h) : g = h :=
  GlobalTheory.EulerTwRestr.gl_ext fun w => by
    exact congrArg (ev ⟨w, rfl⟩) (H (w.under (𝓞 (maximalRealSubfield E))))

theorem eventually_mem_Kn (g : GL (Fin n) (Af E)) : ∀ᶠ v : PlF E in cofinite, pn n v g ∈ Kn n v := by
  have h1 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w (g.1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => (g.1 i j).2
  have h2 : ∀ᶠ w : Pl E in cofinite, ∀ i j, pLoc E w ((g⁻¹).1 i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j => ((g⁻¹).1 i j).2
  have hx : ∀ᶠ w : Pl E in cofinite, GeneralLinearGroup.map (pLoc E w) g ∈ GlobalTheory.LFun.KGL w (n := n) := by
    filter_upwards [h1, h2] with w h1 h2
    exact GlobalTheory.EulerTwRestr.mem_KGL_iff.2 ⟨fun i j => by rw [GlobalTheory.EulerTwRestr.loc_val]; exact h1 i j,
      fun i j => by rw [GlobalTheory.EulerTwRestr.loc_inv_val]; exact h2 i j⟩
  refine eventually_cofinite.2 (((eventually_cofinite.1 hx).image
    fun w : Pl E => w.under (𝓞 (maximalRealSubfield E))).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq, mem_Kn, not_forall, ev_pn] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, w.2⟩

theorem exists_lift (y : ∀ v : PlF E, GL (Fin n) (Av v)) (hy : ∀ᶠ v : PlF E in cofinite, y v ∈ Kn n v) :
    ∃ x : GL (Fin n) (Af E), ∀ v, pn n v x = y v := by
  let un : Pl E → PlF E := fun w => w.under (𝓞 (maximalRealSubfield E))
  let Y : ∀ w : Pl E, GLw n w := fun w => ev (⟨w, rfl⟩ : Above (un w)) (y (un w))
  have hc : ∀ᶠ w : Pl E in cofinite, Y w ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have hB := eventually_cofinite.1 hy
    refine eventually_cofinite.2 ((hB.biUnion fun v _ => (Set.finite_coe_iff (s := {w : Pl E | un w = v})).1 (finite_above v)).subset ?_)
    intro w hw
    refine Set.mem_iUnion₂.2 ⟨un w, fun h => hw (mem_Kn.1 h ⟨w, rfl⟩), rfl⟩
  let M : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => (Y w).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).1 i j⟩
  let M' : Matrix (Fin n) (Fin n) (Af E) := Matrix.of fun i j =>
    ⟨fun w => ((Y w)⁻¹).1 i j, hc.mono fun w h => (GlobalTheory.EulerTwRestr.mem_KGL_iff.1 h).2 i j⟩
  have hloc : ∀ P Q : Matrix (Fin n) (Fin n) (Af E), (∀ w : Pl E, P.map (pLoc E w) = Q.map (pLoc E w)) → P = Q :=
    fun P Q h => Matrix.ext fun i j => Subtype.ext (funext fun w => congrFun (congrFun (h w) i) j)
  have hMM' : M * M' = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).mul_inv
  have hM'M : M' * M = 1 := hloc _ _ fun w => by
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact (Y w).inv_mul
  refine ⟨⟨M, M', hMM', hM'M⟩, fun v => Units.ext (Matrix.ext fun i j => funext ?_)⟩
  rintro ⟨w, rfl⟩
  rfl

theorem exists_Kf_lift {v : PlF E} {k : GL (Fin n) (Av v)} (hk : k ∈ Kn n v) :
    ∃ x ∈ Kf E n, pn n v x = k := by
  have hm : ∀ u : PlF E, (Function.update (fun u : PlF E => (1 : GL (Fin n) (Av u))) v k) u ∈ Kn n u := by
    intro u
    by_cases h : u = v
    · subst h
      simpa using hk
    · simp [Function.update_of_ne h, one_mem]
  obtain ⟨x, hx⟩ := exists_lift _ (Eventually.of_forall hm)
  exact ⟨x, mem_Kf_iff.2 fun u => by rw [hx]; exact hm u, by rw [hx]; simp⟩

theorem isCompact_Kn (v : PlF E) : IsCompact (Kn n v : Set (GL (Fin n) (Av v))) := by
  have e : (Kn n v : Set (GL (Fin n) (Av v))) = pn n v '' (Kf E n : Set (GL (Fin n) (Af E))) := by
    ext k
    refine ⟨fun hk => ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := exists_Kf_lift hk
      exact ⟨x, hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact mem_Kf_iff.1 hg v
  rw [e]
  exact (GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)).image (continuous_pn v)

theorem coe_Kv (a b : ℕ) (v : PlF E) : (Kv a b v : Set (Yv a b v)) =
    (Kn a v : Set (GL (Fin a) (Av v))) ×ˢ (Kn b v : Set (GL (Fin b) (Av v))) :=
  Set.ext fun _ => mem_Kv

theorem mem_prod_iff (a b : ℕ) (x : Gf E a b) :
    x ∈ (Kf E a).prod (Kf E b) ↔ ∀ v, pv a b v x ∈ Kv a b v := by
  rw [Subgroup.mem_prod, mem_Kf_iff, mem_Kf_iff]
  simp only [mem_Kv, forall_and]
  rfl

theorem isOpen_Kf : IsOpen (Kf E n : Set (GL (Fin n) (Af E))) := GlobalTheory.EulerTwRestr.isOpen_Kglob

theorem isCompact_Kf : IsCompact (Kf E n : Set (GL (Fin n) (Af E))) := GlobalTheory.EulerTwRestr.isCompact_Kglob

theorem coe_level (a b : ℕ) : {x : Gf E a b | ∀ v, pv a b v x ∈ Kv a b v} =
    (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) :=
  Set.ext fun x => (mem_prod_iff a b x).symm

theorem isRestrGroup (a b : ℕ) :
    GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch (Gf E a b)) (pv (E := E) a b) (Kv a b) := by
  refine ⟨fun w => w.elim, fun v => ?_, fun v => ?_, fun v => ?_, fun x y _ H => ?_, fun x => ?_, fun c y hy => ?_, ?_, fun C _ => ?_⟩
  · exact ((continuous_pn v).comp continuous_fst).prodMk ((continuous_pn v).comp continuous_snd)
  · rw [coe_Kv]
    exact (isOpen_Kn v).prod (isOpen_Kn v)
  · rw [coe_Kv]
    exact (isCompact_Kn v).prod (isCompact_Kn v)
  · exact Prod.ext (pn_ext fun v => congrArg Prod.fst (H v)) (pn_ext fun v => congrArg Prod.snd (H v))
  · filter_upwards [eventually_mem_Kn x.1, eventually_mem_Kn x.2] with v h1 h2
    exact mem_Kv.2 ⟨h1, h2⟩
  · obtain ⟨x₁, h₁⟩ := exists_lift (fun v => (y v).1) (hy.mono fun v h => (mem_Kv.1 h).1)
    obtain ⟨x₂, h₂⟩ := exists_lift (fun v => (y v).2) (hy.mono fun v h => (mem_Kv.1 h).2)
    exact ⟨(x₁, x₂), fun w => w.elim, fun v => Prod.ext (h₁ v) (h₂ v)⟩
  · rw [coe_level]
    exact isOpen_Kf.prod isOpen_Kf
  · have e : {x : Gf E a b | (∀ w, GlobalTheory.RestrMeas.noArch (Gf E a b) w x ∈ C w) ∧ ∀ v, pv a b v x ∈ Kv a b v} =
        (Kf E a : Set (GL (Fin a) (Af E))) ×ˢ (Kf E b : Set (GL (Fin b) (Af E))) := by
      rw [← coe_level]
      exact Set.ext fun x => ⟨fun h => h.2, fun h => ⟨fun w => w.elim, h⟩⟩
    rw [e]
    exact isCompact_Kf.prod isCompact_Kf

theorem cjv_spec (hC : CjEx) (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cjv v (projv v x) := by
  have h := hC E v
  rw [cjv, dite_eq_left h]
  exact h.choose_spec.2 x

theorem pn_thF (hC : CjEx) (n : ℕ) (v : PlF E) (x : GL (Fin n) (Af E)) :
    pn n v (thF E n x) = thetaGL n (cjv v) (pn n v x) :=
  GlobalTheory.ThetaPull.map_thetaGL _ _ _ (cjv_spec hC v) x

theorem pv_thP (hC : CjEx) (a b : ℕ) (v : PlF E) (x : Gf E a b) :
    pv a b v (thP E a b x) = thv a b v (pv a b v x) :=
  Prod.ext (pn_thF hC a v x.1) (pn_thF hC b v x.2)

theorem theta_mem_Kn (hC : CjEx) {v : PlF E} {k : GL (Fin n) (Av v)} (hk : k ∈ Kn n v) :
    thetaGL n (cjv v) k ∈ Kn n v := by
  obtain ⟨x, hx, rfl⟩ := exists_Kf_lift hk
  rw [← pn_thF hC]
  exact mem_Kf_iff.1 (GlobalTheory.EulerTwKU.thF_mem_Kglob x hx) v

theorem main : RestrV := fun hC E _ _ _ a b =>
  ⟨isRestrGroup a b, fun v x => pv_thP hC a b v x,
    fun v k hk => mem_Kv.2 ⟨theta_mem_Kn hC (mem_Kv.1 hk).1, theta_mem_Kn hC (mem_Kv.1 hk).2⟩,
    mem_prod_iff a b⟩

end GlobalTheory.CompanionTheory.EulerV

end
end

section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.TorusDeriv

noncomputable def blockL (E : Type) [Field E] (r s : ℕ) : Lie E (r + s) :=
  ∑ i : Fin r, toL (Matrix.single (Fin.castAdd s i) (Fin.castAdd s i) (1 : Cinf E))

theorem blockL_apply (E : Type) [Field E] (r s : ℕ) (i j : Fin (r + s)) (w : InfinitePlace E) :
    blockL E r s i j w = if i = j then (if (i : ℕ) < r then (1 : ℂ) else 0) else 0 := by
  have e : blockL E r s i j w =
      ∑ k : Fin r, ((Matrix.single (Fin.castAdd s k) (Fin.castAdd s k) (1 : Cinf E)) i j) w := by
    simp only [blockL, Finset.sum_apply]
    rfl
  rw [e]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases hi : (i : ℕ) < r
    · rw [if_pos hi, Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · have : Fin.castAdd s (⟨i, hi⟩ : Fin r) = i := Fin.ext rfl
        simp [this]
      · intro b _ hb
        have : Fin.castAdd s b ≠ i := fun h => hb (Fin.ext (show (b : ℕ) = i from congrArg Fin.val h))
        simp [Matrix.single_apply, this]
      · simp
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun k _ => ?_
      have : Fin.castAdd s k ≠ i := fun h => hi (by rw [← h]; exact k.2)
      simp [Matrix.single_apply, this]
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ¬ (Fin.castAdd s k = i ∧ Fin.castAdd s k = j) := fun h => hij (h.1.symm.trans h.2)
    simp [Matrix.single_apply, this]

theorem hasDerivAt_entries {ι : Type} [Fintype ι] {a : ℕ} (f : ℝ → Fin a → Fin a → ι → ℂ) (X : Fin a → Fin a → ι → ℂ)
    (h : ∀ i j w, HasDerivAt (fun t => f t i j w) (X i j w) 0) : HasDerivAt f X 0 :=
  hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w => h i j w

theorem hasDerivAt_aInf (E : Type) [Field E] [NumberField E] (r s : ℕ) :
    HasDerivAt (fun t : ℝ => toL (aInf E (r + s) r t).val) (blockL E r s) 0 := by
  refine hasDerivAt_entries _ _ fun i j w => ?_
  rw [blockL_apply]
  have e : (fun t : ℝ => (toL (aInf E (r + s) r t).val) i j w) = fun t : ℝ =>
      if i = j then Complex.exp (if (i : ℕ) < r then (t : ℂ) else 0) else 0 := by
    funext t
    by_cases hij : i = j
    · subst hij
      simp [aInf]
    · simp [aInf, hij]
  rw [e]
  by_cases hij : i = j
  · simp only [if_pos hij]
    by_cases hi : (i : ℕ) < r
    · simp only [if_pos hi]
      simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).cexp
    · simp only [if_neg hi]
      simpa using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  · simp only [if_neg hij]
    exact hasDerivAt_const _ _

theorem lie_blockL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) :
    lie E (r + s) (blockL E r s) =
      ∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i) := by

  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => GlobalTheory.CompanionTheory.CapelliTrace.sum_Eop _ _, blockL, map_sum]
  rfl

theorem hasDerivAt_aT_right : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (F : Sm E (r + s)) (g : GA E (r + s)) (t : ℝ),
  HasDerivAt (fun t : ℝ => F.1 (g * aT E (r + s) r t))
    (((∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) F).1 (g * aT E (r + s) r t)) t := by
  intro E _ _ _ r s F g t
  have h0 : aInf E (r + s) r 0 = 1 := Units.ext (by
    change Matrix.diagonal _ = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i w
    simp)
  have h1 := hasDerivAt_curve F (g * aT E (r + s) r t) (aInf E (r + s) r) (blockL E r s) h0
    (hasDerivAt_aInf E r s)
  have h2 : HasDerivAt (fun u : ℝ => F.1 ((g * aT E (r + s) r t) * infGL E (r + s) (aInf E (r + s) r (u - t))))
      (lieD (blockL E r s) F.1 (g * aT E (r + s) r t)) t :=
    HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h1)
  rw [← lie_blockL]
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  have e : aT E (r + s) r u = aT E (r + s) r t * infGL E (r + s) (aInf E (r + s) r (u - t)) := by
    rw [← aT, ← PExpFin.aT_add]
    congr 1
    ring
  simp only []
  rw [e, mul_assoc]

end GlobalTheory.CompanionTheory.Conc.TorusDeriv
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.eisenstein_series_continuation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ Ê : ℂ → G2 σ Y → ℂ, ∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧ ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re} := by
  first | exact @GlobalTheory.CompanionTheory.SiegelEis.eis_half_plane | exact GlobalTheory.CompanionTheory.SiegelEis.eis_half_plane | (intros; apply GlobalTheory.CompanionTheory.SiegelEis.eis_half_plane <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.eisenstein_vertical_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ t₀ : ℝ, ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), t₀ ≤ t → (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → (∀ s : ℂ, t < s.re → (fun x => Ê s x) ∈ modFun σ Y) ∧ ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) ∧ ∀ c c' : ℝ, t < c → ∃ (C : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  first | exact @GlobalTheory.CompanionTheory.EisHalf.eis_half_plane | exact GlobalTheory.CompanionTheory.EisHalf.eis_half_plane | (intros; apply GlobalTheory.CompanionTheory.EisHalf.eis_half_plane <;> assumption)
end

section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

theorem _root_.GlobalTheory.T.intertwiner_eq_zero_of_vanish_on_highest : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [AddCommGroup V] [Module ℂ V] (G : Fin n → Fin n → Module.End ℂ H) (D : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel G → (∀ a b (x y : H), ⟪G a b x, y⟫_ℂ = ⟪x, G b a y⟫_ℂ) → ∀ R : H →ₗ[ℂ] V, (∀ a b w, R (G a b w) = D a b (R w)) → (∀ (μ : Fin n → ℝ) (v : H), Formalism.REAL.KHighest (fun _ => true) G μ v → R v = 0) → R = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.intertwiner_eq_zero_of_highest | exact GlobalTheory.CompanionTheory.RealCountG.intertwiner_eq_zero_of_highest | (intros; apply GlobalTheory.CompanionTheory.RealCountG.intertwiner_eq_zero_of_highest <;> assumption)
end

section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

theorem _root_.GlobalTheory.T.finite_diagonal_double_cosets : ∀ (H : Type) [Group H] (Z L C : Subgroup H) (F : H × H → ℂ),
  (∀ x : H, Z ⊓ L.map (MulAut.conj x).toMonoidHom ≤ C ∧ (Z ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0) →
  (∀ t ∈ Z, ∀ c ∈ C, t * c * t⁻¹ ∈ C) →
  (∀ t ∈ Z, ∀ x h, F (t * x, t * h) = F (x, h)) →
  (∀ l ∈ L, ∀ l' ∈ L, ∀ x h, F (x * l, h * l') = F (x, h)) →
  {Q : DoubleCoset.Quotient ((Z.map ((MonoidHom.id H).prod (MonoidHom.id H)) : Subgroup (H × H)) : Set (H × H)) ((L.prod L : Subgroup (H × H)) : Set (H × H)) | F (Quotient.out Q) ≠ 0}.Finite →
  ∑ᶠ Q : DoubleCoset.Quotient ((Z.map ((MonoidHom.id H).prod (MonoidHom.id H)) : Subgroup (H × H)) : Set (H × H)) ((L.prod L : Subgroup (H × H)) : Set (H × H)),
      (((Z.map ((MonoidHom.id H).prod (MonoidHom.id H)) ⊓ (L.prod L).map (MulAut.conj (Quotient.out Q)).toMonoidHom).relIndex (C.map ((MonoidHom.id H).prod (MonoidHom.id H))) : ℕ) : ℂ) * F (Quotient.out Q) =
    ∑ᶠ q : DoubleCoset.Quotient (Z : Set H) (L : Set H),
      (((Z ⊓ L.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex C : ℕ) : ℂ) * ∑ᶠ p : H ⧸ L, F (Quotient.out q, p.out) := by
  first | exact @GlobalTheory.CompanionTheory.OrbitCount.orbit_count | exact GlobalTheory.CompanionTheory.OrbitCount.orbit_count | (intros; apply GlobalTheory.CompanionTheory.OrbitCount.orbit_count <;> assumption)
end

section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

theorem _root_.GlobalTheory.T.rel_index_ne_zero_of_open_le : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K L : Subgroup H), IsOpen (L : Set H) → IsCompact (K : Set H) → L ≤ K → L.relIndex K ≠ 0 ∧ ∀ (T C : Subgroup H) (x : H), (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 → (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted | exact GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted | (intros; apply GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted <;> assumption)
end
