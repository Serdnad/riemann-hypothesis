module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Bundle001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFunctionsPeriodRingSeparation
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
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
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
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SphOff
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CutOff

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {k : ℕ}

theorem contDiff_lastEnt : ContDiff ℝ ∞ (lastEnt : (Fin k → Cinf E) → Cinf E) := by
  unfold lastEnt
  refine ContDiff.sum fun c _ => ?_
  by_cases h : (c : ℕ) + 1 = k
  · simp only [if_pos h]
    exact contDiff_apply ℝ (fun _ : Fin k => Cinf E) c
  · simp only [if_neg h]
    exact contDiff_const

theorem isOpen_lastEnt_unit : IsOpen {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
  (Units.isOpen (R := Cinf E)).preimage (contDiff_lastEnt (E := E)).continuous

theorem contDiffOn_inverse_lastEnt :
    ContDiffOn ℝ ∞ (fun x : Fin k → Cinf E => Ring.inverse (lastEnt x))
      {x | IsUnit (lastEnt x)} := by
  intro x hx
  obtain ⟨u, hu⟩ := hx
  have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Cinf E → Cinf E) (lastEnt x) := by
    rw [← hu]; exact contDiffAt_ringInverse ℝ u
  exact (h1.comp x (contDiff_lastEnt (E := E)).contDiffAt).contDiffWithinAt

def tauM (x : Fin k → Cinf E) : LieI (InfinitePlace E) k := Matrix.of.symm (rowM (rowI x))

theorem contDiffOn_tauM :
    ContDiffOn ℝ ∞ (tauM : (Fin k → Cinf E) → LieI (InfinitePlace E) k)
      {x | IsUnit (lastEnt x)} := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun c => ?_
  have hinv := contDiffOn_inverse_lastEnt (E := E) (k := k)
  by_cases hi : (i : ℕ) + 1 = k
  · have e : ∀ x : Fin k → Cinf E, tauM x i c = rowI x c := fun x => rowM_apply_last _ i c hi
    simp only [e]
    by_cases hc : (c : ℕ) + 1 = k
    · simp only [rowI, if_pos hc]
      exact hinv
    · simp only [rowI, if_neg hc]
      exact ((contDiff_apply ℝ (fun _ : Fin k => Cinf E) c).contDiffOn.mul hinv).neg
  · have e : ∀ x : Fin k → Cinf E, tauM x i c = (1 : Matrix (Fin k) (Fin k) (Cinf E)) i c :=
      fun x => rowM_apply_ne _ i c hi
    simp only [e]
    exact contDiffOn_const

theorem tauM_isUnit {x : Fin k → Cinf E} (h : IsUnit (lastEnt x)) :
    IsUnit (Matrix.of (tauM x)) := by
  have e : Matrix.of (tauM x) = (((rowGL x)⁻¹ : GL (Fin k) (Cinf E)) : Matrix (Fin k) (Fin k) (Cinf E)) :=
    (rowGL_inv_val h).symm
  rw [e]
  exact Units.isUnit _

theorem rt_inv_eq_orb (φ : XB E k) {x : Fin k → Cinf E} (h : IsUnit (lastEnt x)) :
    Rt E k (infGL E k (rowGL x))⁻¹ φ = orb (repI E k) φ (tauM x) := by
  have hu := tauM_isUnit h
  have e : hu.unit = (rowGL x)⁻¹ := Units.ext (by
    rw [IsUnit.unit_spec]; exact (rowGL_inv_val h).symm)
  rw [orb, dite_eq_left hu, e]
  change _ = Rt E k (infGL E k (rowGL x)⁻¹) φ
  rw [map_inv (infGL E k)]

theorem contDiff_cut_orbit {φ : XB E k} (hφ : SmV (repI E k) φ) {b : (Fin k → Cinf E) → ℝ}
    (hb : ContDiff ℝ ∞ b) (hs : ∀ x ∈ tsupport b, IsUnit (lastEnt x)) :
    ContDiff ℝ ∞ fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ := by
  have hO := isOpen_lastEnt_unit (E := E) (k := k)
  have hbc : ContDiff ℝ ∞ fun x => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp hb
  have horb : ContDiffOn ℝ ∞ (fun x => orb (repI E k) φ (tauM x)) {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
    ContDiffOn.comp hφ contDiffOn_tauM fun x hx => tauM_isUnit hx
  have hF : ContDiffOn ℝ ∞ (fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ)
      {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
    (hbc.contDiffOn.smul horb).congr fun x hx => by
      rw [rt_inv_eq_orb φ hx]
      rfl
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ tsupport b
  · exact hF.contDiffAt (hO.mem_nhds (hs x hx))
  · have e : (fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq e

end GlobalTheory.CompanionTheory.CutOff

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4
  GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.SgRing

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conj_conj (x : E) : conjE E (conjE E x) = x :=
  IsCMField.complexConj_apply_apply E x

def bar (X : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E := (X.map (conjE E))ᵀ

theorem bar_mul (X Y : Matrix (Fin n) (Fin n) E) : bar (X * Y) = bar Y * bar X := by
  rw [bar, bar, bar, Matrix.map_mul, Matrix.transpose_mul]

theorem bar_add (X Y : Matrix (Fin n) (Fin n) E) : bar (X + Y) = bar X + bar Y := by
  ext i j; simp [bar]

theorem bar_bar (X : Matrix (Fin n) (Fin n) E) : bar (bar X) = X := by
  ext i j; simp [bar, conj_conj]

theorem bar_algebraMap (r : E) :
    bar (algebraMap E (Matrix (Fin n) (Fin n) E) r) = algebraMap E (Matrix (Fin n) (Fin n) E) (conjE E r) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [bar, Matrix.algebraMap_matrix_apply]
  · simp [bar, Matrix.algebraMap_matrix_apply, h, Ne.symm h]

theorem sg_eq (d : GL (Fin n) E) (X : Matrix (Fin n) (Fin n) E) : sg d X = d.val * bar X * (d⁻¹ : GL (Fin n) E).val := rfl

theorem nrm_val (d : GL (Fin n) E) : (nrm d).val = d.val * bar (d⁻¹ : GL (Fin n) E).val := rfl

theorem nrm_inv_val (d : GL (Fin n) E) :
    ((nrm d)⁻¹ : GL (Fin n) E).val = bar d.val * (d⁻¹ : GL (Fin n) E).val := rfl

theorem sg_add (d : GL (Fin n) E) (X Y : Matrix (Fin n) (Fin n) E) : sg d (X + Y) = sg d X + sg d Y := by
  rw [sg_eq, sg_eq, sg_eq, bar_add, Matrix.mul_add, Matrix.add_mul]

theorem sg_mul (d : GL (Fin n) E) (X Y : Matrix (Fin n) (Fin n) E) : sg d (X * Y) = sg d Y * sg d X := by
  have h : (d⁻¹ : GL (Fin n) E).val * d.val = 1 := Units.inv_mul d
  calc sg d (X * Y) = d.val * bar Y * 1 * bar X * (d⁻¹ : GL (Fin n) E).val := by
        rw [sg_eq, bar_mul]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    _ = sg d Y * sg d X := by
        rw [← h, sg_eq, sg_eq]; simp only [Matrix.mul_assoc]

theorem sg_algebraMap (d : GL (Fin n) E) (r : E) :
    sg d (algebraMap E (Matrix (Fin n) (Fin n) E) r) = algebraMap E (Matrix (Fin n) (Fin n) E) (conjE E r) := by
  have h : d.val * (d⁻¹ : GL (Fin n) E).val = 1 := Units.mul_inv d
  rw [sg_eq, bar_algebraMap, ← Algebra.commutes, Matrix.mul_assoc, h, Matrix.mul_one]

theorem sg_one (d : GL (Fin n) E) : sg d 1 = 1 := by
  have h := sg_algebraMap d 1
  simpa using h

theorem sg_zero (d : GL (Fin n) E) : sg d 0 = 0 := by
  have h := sg_algebraMap d 0
  simpa using h

theorem sg_nrm (d : GL (Fin n) E) : sg d (nrm d).val = ((nrm d)⁻¹ : GL (Fin n) E).val := by
  have h : d.val * (d⁻¹ : GL (Fin n) E).val = 1 := Units.mul_inv d
  rw [nrm_inv_val, sg_eq, nrm_val, bar_mul, bar_bar, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem sg_sg (d : GL (Fin n) E) (X : Matrix (Fin n) (Fin n) E) :
    sg d (sg d X) = (nrm d).val * X * ((nrm d)⁻¹ : GL (Fin n) E).val := by
  rw [nrm_inv_val, nrm_val, sg_eq, sg_eq, bar_mul, bar_mul, bar_bar]
  simp only [Matrix.mul_assoc]


omit [NumberField E] [IsCMField E] in
theorem inv_mem (g : GL (Fin n) E) : (g⁻¹ : GL (Fin n) E).val ∈ Algebra.adjoin E {g.val} := by
  have hdet : g.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  have hc : g.val.charpoly.coeff 0 ≠ 0 := by
    intro h0
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  have hp : aeval g.val g.val.charpoly = 0 := Matrix.aeval_self_charpoly _
  set q : Matrix (Fin n) (Fin n) E := aeval g.val (divX g.val.charpoly) with hq
  have hd : q * g.val + algebraMap E _ (g.val.charpoly.coeff 0) = 0 := by
    have h := congrArg (aeval g.val) (divX_mul_X_add g.val.charpoly)
    rwa [hp, map_add, map_mul, aeval_X, aeval_C] at h
  have hmem : q ∈ Algebra.adjoin E {g.val} := aeval_mem_adjoin_singleton E g.val
  have h1 : (-(g.val.charpoly.coeff 0)⁻¹ • q) * g.val = 1 := by
    rw [Matrix.smul_mul, eq_neg_of_add_eq_zero_left hd, Algebra.algebraMap_eq_smul_one, smul_neg, neg_smul, neg_neg,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h2 : (g⁻¹ : GL (Fin n) E).val = -(g.val.charpoly.coeff 0)⁻¹ • q := by
    calc (g⁻¹ : GL (Fin n) E).val = ((-(g.val.charpoly.coeff 0)⁻¹ • q) * g.val) * (g⁻¹ : GL (Fin n) E).val := by
          rw [h1, Matrix.one_mul]
      _ = -(g.val.charpoly.coeff 0)⁻¹ • q := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h2]
  exact Subalgebra.smul_mem _ hmem _

theorem sg_mem (d : GL (Fin n) E) {x : Matrix (Fin n) (Fin n) E} (hx : x ∈ Algebra.adjoin E {(nrm d).val}) :
    sg d x ∈ Algebra.adjoin E {(nrm d).val} := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.1 hx
    rw [sg_nrm]
    exact inv_mem (nrm d)
  | algebraMap r =>
    rw [sg_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [sg_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [sg_mul]
    exact mul_mem hy hx

omit [NumberField E] [IsCMField E] in
theorem adjoin_comm (γ : Matrix (Fin n) (Fin n) E) {x y : Matrix (Fin n) (Fin n) E}
    (hx : x ∈ Algebra.adjoin E {γ}) (hy : y ∈ Algebra.adjoin E {γ}) : x * y = y * x :=
  pol_comm γ x y ((isPol_iff γ x).2 hx) ((isPol_iff γ y).2 hy)

theorem exists_sgRing (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E) :
    ∃ σ : Algebra.adjoin E {(nrm d).val} →+* Algebra.adjoin E {(nrm d).val},
      (∀ x, ((σ x : Algebra.adjoin E {(nrm d).val}) : Matrix (Fin n) (Fin n) E) = sg d x) ∧ ∀ x, σ (σ x) = x := by
  refine ⟨{ toFun := fun x => ⟨sg d x, sg_mem d x.2⟩
            map_one' := Subtype.ext (sg_one d)
            map_zero' := Subtype.ext (sg_zero d)
            map_add' := fun x y => Subtype.ext (sg_add d x y)
            map_mul' := fun x y => Subtype.ext ?_ }, fun x => rfl, fun x => Subtype.ext ?_⟩
  · change sg d (x.val * y.val) = sg d x.val * sg d y.val
    rw [sg_mul]
    exact adjoin_comm _ (sg_mem d y.2) (sg_mem d x.2)
  · change sg d (sg d x.val) = x.val
    have hγ : (nrm d).val ∈ Algebra.adjoin E {(nrm d).val} := Algebra.self_mem_adjoin_singleton E _
    rw [sg_sg, adjoin_comm _ hγ x.2, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

end GlobalTheory.CompanionTheory.TorusCh.SgRing

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem aeval_mulVec_mem_of_stable {K : Type} [Field K] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)) (hW : W.map (Matrix.toLin' γ) ≤ W) (g : K[X]) :
    ∀ y ∈ W, aeval γ g *ᵥ y ∈ W := by
  have hγ : ∀ y ∈ W, γ *ᵥ y ∈ W := fun y hy =>
    hW ⟨y, hy, by rw [Matrix.toLin'_apply]⟩
  induction g using Polynomial.induction_on with
  | C a =>
    intro y hy
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem a hy
  | add p q hp hq =>
    intro y hy
    rw [map_add (f := _), Matrix.add_mulVec]
    exact W.add_mem (hp y hy) (hq y hy)
  | monomial k a ih =>
    intro y hy
    have : aeval γ (C a * X ^ (k + 1)) = aeval γ (C a * X ^ k) * γ := by
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    rw [this, ← Matrix.mulVec_mulVec]
    exact ih _ (hγ y hy)

def stableIdeal {K : Type} [Field K] {n : ℕ} (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K)
    (W : Submodule K (Fin n → K)) (hW : W.map (Matrix.toLin' γ) ≤ W) : Ideal K[X] where
  carrier := {h | aeval γ h *ᵥ v ∈ W}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add (f := _), Matrix.add_mulVec]
    exact W.add_mem ha hb
  zero_mem' := by
    simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul] at hx ⊢
    rw [map_mul, ← Matrix.mulVec_mulVec]
    exact aeval_mulVec_mem_of_stable γ W hW c _ hx

theorem exists_idem_pol_range_eq : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K),
    γ.charpoly.Separable → (∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v) →
    ∀ W : Submodule K (Fin n → K), W.map (Matrix.toLin' γ) ≤ W →
    ∃ π, IsPol γ π ∧ π * π = π ∧ LinearMap.range (Matrix.toLin' π) = W := by
  intro K _ n γ v hsep hcyc W hW
  set I := stableIdeal γ v W hW with hI
  have hmemI : ∀ h : K[X], h ∈ I ↔ aeval γ h *ᵥ v ∈ W := fun h => Iff.rfl
  obtain ⟨w, hw⟩ : ∃ w, I = Ideal.span {w} :=
    ⟨Submodule.IsPrincipal.generator I, (Ideal.span_singleton_generator I).symm⟩
  have hdvd : ∀ h : K[X], aeval γ h *ᵥ v ∈ W ↔ w ∣ h := fun h => by
    rw [← hmemI, hw, Ideal.mem_span_singleton]
  have hχ : aeval γ γ.charpoly = 0 := Matrix.aeval_self_charpoly γ
  obtain ⟨c, hc⟩ : w ∣ γ.charpoly := by
    rw [← hdvd, hχ, Matrix.zero_mulVec]
    exact W.zero_mem
  have hco : IsCoprime w c := Polynomial.Separable.isCoprime (hc ▸ hsep)
  obtain ⟨u, b, hub⟩ := hco
  refine ⟨aeval γ (u * w), ⟨u * w, rfl⟩, ?_, ?_⟩
  · have key : u * w * (u * w) = u * w - u * b * γ.charpoly := by
      linear_combination (u * w) * hub + (u * b) * hc
    rw [← map_mul, key, map_sub, map_mul (aeval γ) (u * b), hχ, mul_zero, sub_zero]
  · apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      obtain ⟨h, rfl⟩ := hcyc y
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← map_mul, hdvd]
      exact ⟨u * h, by ring⟩
    · intro y hy
      obtain ⟨h, rfl⟩ := hcyc y
      obtain ⟨g, rfl⟩ := (hdvd h).1 hy
      refine ⟨aeval γ (w * g) *ᵥ v, ?_⟩
      have key : u * w * (w * g) = w * g - g * b * γ.charpoly := by
        linear_combination (w * g) * hub + (g * b) * hc
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← map_mul, key, map_sub,
        map_mul (aeval γ) (g * b), hχ, mul_zero, sub_zero]

end GlobalTheory.CompanionTheory.TorusCh
end
end

section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem dvd_of_aeval_eq_zero_of_dvd_charpoly {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) {p g : K[X]} (hp : Irreducible p) (hpc : p ∣ γ.charpoly)
    (hg : aeval γ g = 0) : p ∣ g := by
  classical
  by_contra hn
  obtain ⟨a, b, hab⟩ := (hp.coprime_iff_not_dvd).2 hn
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) p (ne_of_gt (degree_pos_of_irreducible hp))
  have hroot : (γ.map (algebraMap K (AlgebraicClosure K))).charpoly.IsRoot α := by
    obtain ⟨c, hc⟩ := hpc
    rw [Matrix.charpoly_map, hc, IsRoot, eval_map_algebraMap, map_mul, hα, zero_mul]
  have hs : α ∈ spectrum (AlgebraicClosure K) (γ.map (algebraMap K (AlgebraicClosure K))) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h2 := spectrum.subset_polynomial_aeval (γ.map (algebraMap K (AlgebraicClosure K)))
    (g.map (algebraMap K (AlgebraicClosure K))) ⟨α, hs, rfl⟩
  have h3 : aeval (γ.map (algebraMap K (AlgebraicClosure K))) (g.map (algebraMap K (AlgebraicClosure K))) = 0 := by
    have := aeval_algHom_apply ((Algebra.ofId K (AlgebraicClosure K)).mapMatrix (m := Fin n)) γ g
    rw [hg, map_zero] at this
    rw [aeval_map_algebraMap]
    exact this
  rw [h3] at h2
  have h4 : aeval α g = 0 := by
    by_contra hne
    apply h2
    simp only [eval_map_algebraMap]
    rw [spectrum.mem_resolventSet_iff, sub_zero]
    exact (Ne.isUnit hne).map (algebraMap (AlgebraicClosure K) (Matrix (Fin n) (Fin n) (AlgebraicClosure K)))
  have h5 := congrArg (aeval α) hab
  simp [hα, h4] at h5

theorem exists_prim_of_irreducible {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) {p : K[X]} (hp : Irreducible p)
    (hpc : p ∣ γ.charpoly) :
    ∃ e, IsPrim γ e ∧ ∃ f : K[X], e = aeval γ f ∧ p ∣ 1 - f := by
  obtain ⟨q, hq⟩ := hpc
  have hχ : aeval γ (p * q) = 0 := by rw [← hq]; exact Matrix.aeval_self_charpoly γ
  obtain ⟨b, u, hbu⟩ : IsCoprime p q := (hq ▸ hs : (p * q).Separable).isCoprime
  have hnd : ∀ c : K[X], aeval γ (c * (p * q)) = 0 := fun c => by rw [map_mul, hχ, mul_zero]
  have hsub : (1 : K[X]) - u * q = b * p := by rw [← hbu]; ring
  have hdvd : p ∣ 1 - u * q := ⟨b, by rw [hsub]; ring⟩
  refine ⟨aeval γ (u * q), ⟨⟨_, rfl⟩, ?_, ?_, ?_⟩, _, rfl, hdvd⟩
  · rw [← map_mul]
    have : u * q * (u * q) = u * q - (u * b) * (p * q) := by linear_combination (-(u * q)) * hsub
    rw [this, map_sub, hnd, sub_zero]
  · intro h0
    have h1 := dvd_of_aeval_eq_zero_of_dvd_charpoly γ hp ⟨q, hq⟩ h0
    exact hp.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_add hdvd h1))
  · intro h hne
    have hnp : ¬ p ∣ h := by
      rintro ⟨c, rfl⟩
      apply hne
      rw [← map_mul]
      have : p * c * (u * q) = (c * u) * (p * q) := by ring
      rw [this, hnd]
    obtain ⟨a', a, haa⟩ := (hp.coprime_iff_not_dvd).2 hnp
    refine ⟨a, ?_⟩
    rw [← map_mul, ← map_mul]
    have : a * (h * (u * q)) = u * q - (a' * u) * (p * q) := by linear_combination (u * q) * haa
    rw [this, map_sub, hnd, sub_zero]

theorem exists_prim_cover (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K)
    (hs : γ.charpoly.Separable) :
    ∃ S : Finset (Matrix (Fin n) (Fin n) K), (∀ e ∈ S, IsPrim γ e) ∧
      ∀ x : Fin n → K, x ≠ 0 → ∃ e ∈ S, x ᵥ* e ≠ 0 := by
  classical
  have key : ∀ p : K[X], p ∈ UniqueFactorizationMonoid.normalizedFactors γ.charpoly →
      ∃ e, IsPrim γ e ∧ ∃ f : K[X], e = aeval γ f ∧ p ∣ 1 - f := fun p hp =>
    exists_prim_of_irreducible γ hs (UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp)
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)
  choose! E hE using key
  have hχ0 : γ.charpoly ≠ 0 := (Matrix.charpoly_monic γ).ne_zero
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors γ.charpoly).toFinset.image E, ?_, ?_⟩
  · intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he
    exact (hE p (Multiset.mem_toFinset.1 hp)).1
  · intro x hx
    let I : Ideal K[X] :=
      { carrier := {f | x ᵥ* aeval γ f = 0}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_add (f := _), Matrix.vecMul_add, ha, hb, add_zero]
        zero_mem' := by simp
        smul_mem' := fun c f hf => by
          simp only [Set.mem_setOf_eq] at hf ⊢
          rw [smul_eq_mul, mul_comm, map_mul, ← Matrix.vecMul_vecMul, hf, Matrix.zero_vecMul] }
    have hmem : ∀ f, f ∈ I ↔ x ᵥ* aeval γ f = 0 := fun f => Iff.rfl
    set a := Submodule.IsPrincipal.generator I with ha
    have hdiv : ∀ f, f ∈ I ↔ a ∣ f := fun f => Submodule.IsPrincipal.mem_iff_generator_dvd I
    have haχ : a ∣ γ.charpoly := (hdiv _).1 (by
      rw [hmem, Matrix.aeval_self_charpoly, Matrix.vecMul_zero])
    have ha0 : a ≠ 0 := fun h => hχ0 (by simpa [h] using haχ)
    have hau : ¬ IsUnit a := fun h => hx (by
      have h1 : (1 : K[X]) ∈ I := (hdiv 1).2 h.dvd
      rw [hmem, map_one, Matrix.vecMul_one] at h1
      exact h1)
    obtain ⟨i, hi, hia⟩ := WfDvdMonoid.exists_irreducible_factor hau ha0
    obtain ⟨p, hp, hip⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hχ0 hi (hia.trans haχ)
    obtain ⟨hprim, f, hf, hpf⟩ := hE p hp
    refine ⟨E p, Finset.mem_image.2 ⟨p, Multiset.mem_toFinset.2 hp, rfl⟩, fun h0 => ?_⟩
    rw [hf] at h0
    have h1 : a ∣ f := (hdiv f).1 h0
    have h2 : p ∣ f := hip.symm.dvd.trans (hia.trans h1)
    have hpi : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
    exact hpi.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_add hpf h2))

end GlobalTheory.CompanionTheory.TorusCh
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.continuous_functions_period_ring_separation : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∀ x : (A.cont ℤ_[l]).Acr n, IsLocallyConstant fun z => mapAcr (A.evCont z) n x) ∧ (∀ x : (A.cont ℤ_[l]).Acr n, (∀ z, mapAcr (A.evCont z) n x = 0) → x = 0) ∧ ∀ (𝔞 : Ideal ((base l).Acr n)) (f : ℤ_[l] → A.Acr n), IsLocallyConstant f → (∀ z, f z ∈ 𝔞.map (mapAcr A.fromBase n)) → ∃ x ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n), ∀ z, mapAcr (A.evCont z) n x = f z := by
  first | exact @GlobalTheory.CompanionTheory.ContAcr.acr_cont | exact GlobalTheory.CompanionTheory.ContAcr.acr_cont | (intros; apply GlobalTheory.CompanionTheory.ContAcr.acr_cont <;> assumption)
end
