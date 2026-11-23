module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle186
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle147
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.flagStabilizer_eq_unipotent_torus_levi_atPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (g : GA D S), g ∈ grpAt S (· = v) → (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S g * d.jX = d.jX * a) → ∃ n ∈ flagN d, n ∈ grpAt S (· = v) ∧ ∃ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) ∧ d.levi t ∈ grpAt S (· = v) ∧ ∃ γ ∈ grpAt S₀ (· = v), g = n * d.levi t * d.emb0 γ := by
  intro D S S₀ ρ d v g hg ⟨a, hup, hgX⟩
  have hG' : ∀ i j, (mt S g - 1) i j ∈ idAt D (· = v) := fun i j => by
    rw [Matrix.sub_apply]; exact (mem_congGrp_iff S (idAt D (· = v)) g).1 hg i j

  have hba : (adj (mt S g * d.jY) * (gA S * d.jX)) * a = 1 := by
    have h1 : adj (mt S g * d.jY) * (gA S * (mt S g * d.jX)) = 1 := by
      rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)), mt_unitary]
      exact d.gram_YX
    rw [hgX] at h1
    simpa only [Matrix.mul_assoc] using h1
  have hab : a * (adj (mt S g * d.jY) * (gA S * d.jX)) = 1 := mul_eq_one_comm.1 hba
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin ρ) (AE D), A.1 = a := ⟨⟨a, _, hab, hba⟩, rfl⟩

  have hdet : IsUnit a.det := Matrix.isUnit_det_of_left_inverse hba
  rw [Matrix.det_of_isUpperTriangular (M := a) (fun ⦃i j⦄ h => hup i j h)] at hdet
  have hu : ∀ i, IsUnit (a i i) := fun i =>
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun k => a k k) (Finset.mem_univ i)) hdet
  obtain ⟨t, ht1, htinv⟩ : ∃ t : GL (Fin ρ) (AE D), t.1 = diagonal (fun i => a i i) ∧
      (t⁻¹).1 = diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)) :=
    ⟨⟨diagonal (fun i => a i i), diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)),
      by rw [diagonal_mul_diagonal]; simp only [IsUnit.mul_val_inv, diagonal_one],
      by rw [diagonal_mul_diagonal]; simp only [IsUnit.val_inv_mul, diagonal_one]⟩, rfl, rfl⟩
  have ht_diag : ∀ i j, i ≠ j → t.1 i j = 0 := fun i j h => by rw [ht1]; exact diagonal_apply_ne _ h

  have hAt : (A * t⁻¹).1 =
      a * diagonal (fun i => (((hu i).unit⁻¹ : (AE D)ˣ) : AE D)) := by
    rw [Units.val_mul A t⁻¹, htinv, hA]
  have hUX : A * t⁻¹ ∈ UX D ρ := fun i j =>
    ⟨fun h => by rw [hAt, mul_diagonal, hup i j h, zero_mul],
      by rw [hAt, mul_diagonal]; exact IsUnit.mul_val_inv (hu i)⟩
  have hR' : mt S (g * (d.levi t)⁻¹) * d.jX = d.jX * (A * t⁻¹).1 := by
    rw [Units.val_mul A t⁻¹, hA, ← map_inv d.levi t, mt_mul, Matrix.mul_assoc, d.levi_jX]
    simpa only [Matrix.mul_assoc] using congrArg (fun M : Mx D S.rank ρ => M * (t⁻¹).1) hgX
  let u := A * t⁻¹
  let r := g * (d.levi t)⁻¹
  let s := d.levi u⁻¹ * r
  have hsX : mt S s * d.jX = d.jX := by
    change mt S (d.levi u⁻¹ * r) * d.jX = d.jX
    rw [mt_mul, Matrix.mul_assoc, show mt S r * d.jX = d.jX * u.1 from hR',
      ← Matrix.mul_assoc, d.levi_jX, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.mul_one]
  have hgram {k l : ℕ} (X : Mx D S.rank k) (Y : Mx D S.rank l) :
      adj (mt S s * X) * (gA S * (mt S s * Y)) = adj X * (gA S * Y) := by
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) _ Y,
      ← Matrix.mul_assoc (adj (mt S s)), mt_unitary]
  have hsY : d.pY * (mt S s * d.j0) = 0 := by
    rw [d.pY_eq, Matrix.mul_assoc, ← hsX, hgram, d.wittDecomp_gram_X_anisotropic]
  let B := d.pX * (mt S s * d.j0)
  let Q := d.p0 * (mt S s * d.j0)
  have hs0 : mt S s * d.j0 = d.jX * B + d.j0 * Q := by
    conv_lhs => rw [← Matrix.one_mul (mt S s * d.j0), ← d.sum_eq_one]
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      hsY, Matrix.mul_zero, add_zero]
  have hQ : adj Q * (gA S₀ * Q) = gA S₀ := by
    have h := hgram d.j0 d.j0
    rw [hs0, d.gram_00] at h
    simpa only [adj_add, adj_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      cancel₃ d.gram_XX, cancel₃ d.wittDecomp_gram_X_anisotropic, cancel₃ d.gram_0X,
      cancel₃ d.gram_00, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] using h
  let γ := GlobalTheory.MixModel.ofMat S₀ Q hQ
  have hγQ : mt S₀ γ = Q := by
    change mt S₀ (GlobalTheory.MixModel.ofMat S₀ Q hQ) = Q
    rw [mt_ofMat]
  have hs0' : mt S s * d.j0 = d.jX * B + d.j0 * mt S₀ γ := by rw [hγQ, hs0]
  let n₀ := s * (d.emb0 γ)⁻¹
  have hn₀X : mt S n₀ * d.jX = d.jX := by
    change mt S (s * (d.emb0 γ)⁻¹) * d.jX = d.jX
    rw [← map_inv, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, hsX]
  have hn₀0 : mt S n₀ * d.j0 = d.j0 + d.jX * (B * mt S₀ γ⁻¹) := by
    change mt S (s * (d.emb0 γ)⁻¹) * d.j0 = _
    rw [← map_inv, mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic,
      ← Matrix.mul_assoc, hs0', Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc d.j0,
      GlobalTheory.MixModel.mt_mul_inv, Matrix.mul_one, add_comm]
  have hn₀ : n₀ ∈ flagN d := by
    refine d.mem_NFlag HypDec.one_mem_upperUni ?_ hn₀0
    rw [hn₀X, Units.val_one, Matrix.mul_one]
  let n := d.levi u * n₀
  have hn : n ∈ flagN d := mul_mem (d.levi_mem_NFlag hUX) hn₀
  have hnγ : g * (d.levi t)⁻¹ = n * d.emb0 γ := by
    change r = (d.levi u * (s * (d.emb0 γ)⁻¹)) * d.emb0 γ
    rw [mul_assoc, inv_mul_cancel_right]
    change r = d.levi u * (d.levi u⁻¹ * r)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

  have hgfac : g = n * d.levi t * d.emb0 γ := by
    rw [mul_assoc, ← d.wittHyperbolic_anisotropic_commute_levi, ← mul_assoc, ← hnγ,
      inv_mul_cancel_right]

  have hmtγ : mt S₀ γ = d.p0 * (mt S g * d.j0) := by
    rw [hγQ]
    change d.p0 * (mt S (d.levi u⁻¹ * (g * (d.levi t)⁻¹)) * d.j0) = _
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← map_inv d.levi t,
      d.wittDecomp_levi_inclAnisotropic, ← Matrix.mul_assoc d.p0,
      d.wittDecomp_projAnisotropic_levi]
  have hγ : γ ∈ grpAt S₀ (· = v) := (mem_congGrp_iff S₀ _ γ).2 fun i j => by
    have e : mt S₀ γ - 1 = d.p0 * ((mt S g - 1) * d.j0) := by
      rw [hmtγ, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, d.p0_j0]
    rw [← Matrix.sub_apply, e]
    exact GlobalTheory.IwaFlag.mul_left_mem _ (GlobalTheory.IwaFlag.mul_right_mem _ hG') i j

  have haI : ∀ i j, (a - 1) i j ∈ idAt D (· = v) := by
    have e : a - 1 = d.pX * ((mt S g - 1) * d.jX) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, d.pX_jX, hgX, ← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul]
    intro i j
    rw [e]
    exact GlobalTheory.IwaFlag.mul_left_mem _ (GlobalTheory.IwaFlag.mul_right_mem _ hG') i j
  have ht1I : ∀ i j, (t.1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [ht1, Matrix.sub_apply]
    by_cases h : i = j
    · subst h
      have := haI i i
      rw [Matrix.sub_apply] at this
      rwa [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero]
      exact Ideal.zero_mem _
  have htiI : ∀ i j, ((t⁻¹).1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [htinv, Matrix.sub_apply]
    by_cases h : i = j
    · subst h
      have := haI i i
      rw [Matrix.sub_apply, Matrix.one_apply_eq] at this
      rw [diagonal_apply_eq, Matrix.one_apply_eq]
      have e : (((hu i).unit⁻¹ : (AE D)ˣ) : AE D) - 1 = -((((hu i).unit⁻¹ : (AE D)ˣ) : AE D) * (a i i - 1)) := by
        rw [mul_sub, IsUnit.val_inv_mul (hu i)]; ring
      rw [e]
      exact (idAt D (· = v)).neg_mem (Ideal.mul_mem_left _ _ this)
    · rw [diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero]
      exact Ideal.zero_mem _
  have hadjI : ∀ i j, (adj (t⁻¹).1 - 1) i j ∈ idAt D (· = v) := by
    intro i j
    rw [← adj_one, ← adj_sub]
    exact GlobalTheory.IwaFlag.cA_mem_idAt' (htiI j i)
  have hlevI : d.levi t ∈ grpAt S (· = v) := by
    have e : mt S (d.levi t) - 1 = d.jX * (t.1 - 1) * d.pX + d.jY * (adj (t⁻¹).1 - 1) * d.pY := by
      rw [d.mt_levi, ← d.sum_eq_one]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      abel
    refine (mem_congGrp_iff S _ _).2 fun i j => ?_
    rw [← Matrix.sub_apply, e, Matrix.add_apply]
    exact add_mem (GlobalTheory.IwaFlag.mul_right_mem _ (GlobalTheory.IwaFlag.mul_left_mem _ ht1I) i j) (GlobalTheory.IwaFlag.mul_right_mem _ (GlobalTheory.IwaFlag.mul_left_mem _ hadjI) i j)
  have hnI : n ∈ grpAt S (· = v) := by
    have hγI : d.emb0 γ ∈ grpAt S (· = v) := by
      have hγ' : ∀ i j, (mt S₀ γ - 1) i j ∈ idAt D (· = v) := fun i j => by
        rw [Matrix.sub_apply]
        exact (mem_congGrp_iff S₀ _ γ).1 hγ i j
      have e : mt S (d.emb0 γ) - 1 = d.j0 * (mt S₀ γ - 1) * d.p0 := by
        rw [d.unitaryMatrix_wittCoreEmbedding, ← d.sum_eq_one, Matrix.mul_sub, Matrix.sub_mul,
          Matrix.mul_one]
        abel
      refine (mem_congGrp_iff S _ _).2 fun i j => ?_
      rw [← Matrix.sub_apply, e]
      exact GlobalTheory.IwaFlag.mul_right_mem _ (GlobalTheory.IwaFlag.mul_left_mem _ hγ') i j
    have e : n = g * (d.levi t * d.emb0 γ)⁻¹ := eq_mul_inv_of_mul_eq ((mul_assoc _ _ _).symm.trans hgfac.symm)
    rw [e]
    exact mul_mem hg (inv_mem (mul_mem hlevI hγI))
  exact ⟨n, hn, hnI, t, ht_diag, hlevI, γ, hγ, hgfac⟩
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {T L : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def zcol (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (y : WO L T) : n → k :=
  β.b' *ᵥ fun i => p.pr ((y *ᵥ fun j => incA D (ζ j)) i)


open Classical in
def colFun (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (a : (n → k) → ℂ) (y : WO L T) : ℂ :=
  if IsHalf p.e y then a (zcol β ζ y) else 0

def zrow (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (x : WO T L) : n → k :=
  (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)))⁻¹ •
    ((fun i => p.pr (((fun j => incA D ((star ζ ᵥ* L.gram) j)) ᵥ* x) i)) ᵥ* β.b)


open Classical in
def rowFun (β : Frame p T n) (ζ : Fin L.rank → D.host.E) (b : (n → k) → ℂ) (x : WO T L) : ℂ :=
  if IsHalf p.e x then b (zrow β ζ x) else 0

def restrModel {m n m' n' m'' n'' : ℕ} (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (h : Mx D m'' n'' → ℂ)
    (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) (y : Mx D m'' n'') :
    (Mx D m' n' → ℂ) →ₗ[ℂ] (Mx D m' n' → ℂ) where
  toFun Φ := fun w => T' (fun t => Φ (r t).1 * h (r t).2) (r.symm (w, y))
  map_add' Φ Φ' := by
    funext w
    have : (fun t => (Φ + Φ') (r t).1 * h (r t).2) = (fun t => Φ (r t).1 * h (r t).2) + fun t => Φ' (r t).1 * h (r t).2 := by
      funext t; simp [add_mul]
    rw [this, map_add (f := _)]; rfl
  map_smul' c Φ := by
    funext w
    have : (fun t => (c • Φ) (r t).1 * h (r t).2) = c • fun t => Φ (r t).1 * h (r t).2 := by
      funext t; simp [mul_assoc]
    rw [this, map_smul]; rfl

theorem restrModel_apply {m n m' n' m'' n'' : ℕ} (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (h : Mx D m'' n'' → ℂ)
    (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)) (y : Mx D m'' n'') (Φ : Mx D m' n' → ℂ) (w : Mx D m' n') :
    restrModel r h T' y Φ w = T' (fun t => Φ (r t).1 * h (r t).2) (r.symm (w, y)) := rfl

theorem heisO_resS_symm (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (a : WO A T)
    (F : WO S T → ℂ) (w : WO A T) (y : WO L T) :
    heisO ψ S T ((o.resS T).symm (a, 0)) F ((o.resS T).symm (w, y)) =
      heisO ψ A T a (fun w' => F ((o.resS T).symm (w', y))) w := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h0 : symplOH L T y 0 = 0 := by simp [symplOH, symplO, hO]
  rw [h0, add_zero, ← map_add (f := _)]
  simp

theorem heisO_resT_symm (ψ : AddChar (AF D.host.F) ℂ) {S A L T : HSp D} (o : OrthDec S A L) (a : WO T A)
    (F : WO T S → ℂ) (w : WO T A) (y : WO T L) :
    heisO ψ T S ((o.resT T).symm (a, 0)) F ((o.resT T).symm (w, y)) =
      heisO ψ T A a (fun w' => F ((o.resT T).symm (w', y))) w := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have h0 : symplOH T L y 0 = 0 := by simp [symplOH, symplO, hO]
  rw [h0, add_zero, ← map_add (f := _)]
  simp

theorem symplO_resS_symm {S A L T : HSp D} (o : OrthDec S A L) (t : WO S T) (a : WO A T) :
    symplO S T t ((o.resS T).symm (a, 0)) = symplO A T ((o.resS T) t).1 a := by
  rw [o.symplO_resS, AddEquiv.apply_symm_apply]
  simp [symplO, hO]

theorem symplO_resT_symm {S A L T : HSp D} (o : OrthDec S A L) (t : WO T S) (a : WO T A) :
    symplO T S t ((o.resT T).symm (a, 0)) = symplO T A ((o.resT T) t).1 a := by
  rw [o.symplO_resT, AddEquiv.apply_symm_apply]
  simp [symplO, hO]

theorem half_resS_symm {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {a : WO A T} (ha : IsHalf e a) :
    IsHalf e ((o.resS T).symm (a, 0)) := by
  intro i j
  rw [OrthDec.resS_symm_apply]
  simp only [Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [← mul_assoc, ha]

theorem half_resT_symm {S A L T : HSp D} (o : OrthDec S A L) {e : AE D} {a : WO T A} (ha : IsHalf e a) :
    IsHalf e ((o.resT T).symm (a, 0)) := by
  intro i j
  rw [OrthDec.resT_symm_apply]
  simp only [Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [mul_left_comm, ha]

section Lat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [Fintype n']

theorem latInd_lastKer (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)) :
    latInd (lastKer ΛA) ΛT = tensCol (latInd ΛA ΛT) (vecInd ΛT) := by
  classical
  funext x
  have hmv : ∀ y : n' ⊕ Fin 1 → k, x *ᵥ y = x.submatrix id Sum.inl *ᵥ (y ∘ Sum.inl) +
      y (Sum.inr 0) • fun i => x i (Sum.inr 0) := by
    intro y; funext i
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]
  have key : (∀ y ∈ lastKer ΛA, x *ᵥ y ∈ ΛT) ↔
      (∀ y ∈ ΛA, x.submatrix id Sum.inl *ᵥ y ∈ ΛT) ∧ (fun i => x i (Sum.inr 0)) ∈ ΛT := by
    constructor
    · intro h
      refine ⟨fun y hy => ?_, ?_⟩
      · have hm : Sum.elim y 0 ∈ lastKer ΛA := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa using hy, by simp⟩
        have := h _ hm
        rw [hmv] at this
        simpa using this
      · have hm : (Sum.elim 0 1 : n' ⊕ Fin 1 → k) ∈ lastKer ΛA :=
          GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨by simpa using ΛA.zero_mem, by simp⟩
        have := h _ hm
        rw [hmv] at this
        simpa using this
    · rintro ⟨h1, h2⟩ y hy
      obtain ⟨hy1, hy2⟩ := GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy
      rw [hmv]
      refine ΛT.add_mem (h1 _ hy1) ?_
      have := ΛT.smul_mem (⟨y (Sum.inr 0), hy2⟩ : 𝒪[k]) h2
      exact this
  simp only [latInd, tensCol, vecInd]
  by_cases h : ∀ y ∈ lastKer ΛA, x *ᵥ y ∈ ΛT
  · rw [if_pos h, if_pos (key.1 h).1, if_pos (key.1 h).2, mul_one]
  · rw [if_neg h]
    by_cases h1 : ∀ y ∈ ΛA, x.submatrix id Sum.inl *ᵥ y ∈ ΛT
    · rw [if_pos h1, if_neg fun h2 => h (key.2 ⟨h1, h2⟩), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem latInd_lastKer_row (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)) :
    latInd ΛT (lastKer ΛA) = tensRow (latInd ΛT ΛA) (dualInd ΛT) := by
  classical
  funext x
  have key : (∀ y ∈ ΛT, x *ᵥ y ∈ lastKer ΛA) ↔
      (∀ y ∈ ΛT, x.submatrix Sum.inl id *ᵥ y ∈ ΛA) ∧ InDual ΛT (x (Sum.inr 0)) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer, InDual]
    exact ⟨fun h => ⟨fun y hy => (h y hy).1, fun y hy => (h y hy).2⟩, fun h y hy => ⟨h.1 y hy, h.2 y hy⟩⟩
  simp only [latInd, tensRow, dualInd]
  by_cases h : ∀ y ∈ ΛT, x *ᵥ y ∈ lastKer ΛA
  · rw [if_pos h, if_pos (key.1 h).1, if_pos (key.1 h).2, mul_one]
  · rw [if_neg h]
    by_cases h1 : ∀ y ∈ ΛT, x.submatrix Sum.inl id *ᵥ y ∈ ΛA
    · rw [if_pos h1, if_neg fun h2 => h (key.2 ⟨h1, h2⟩), mul_zero]
    · rw [if_neg h1, zero_mul]

end Lat

end GlobalTheory.FinPl.ExtZero

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPl

theorem matrix_mulVec_mem_adeleIdealSupportedOnPlaces {D : D7} {P : Pl D → Prop} {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D))
    (y : Fin n → AE D) (hy : ∀ i, y i ∈ idAt D P) (i : Fin m) : (A *ᵥ y) i ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem matrixColumnScaledByAdele_zero {D : D7} {m n : ℕ} (x : Mx D m n) (i : Fin n) : colMul x i 0 = 0 := by
  funext k; simp [colMul]

theorem carriesLattice_wittEmbedding_iff_core : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : GlobalTheory.FinPl.Lat S) (L₀ : GlobalTheory.FinPl.Lat S₀) (v : GlobalTheory.FinPl.Pl D) (g : GA D S₀), GlobalTheory.FinPl.MonoAt d L L₀ v → (GlobalTheory.FinPl.Moves S (d.emb0 g) L L (· = v) ↔ GlobalTheory.FinPl.Moves S₀ g L₀ L₀ (· = v)) := by
  intro D S S₀ ρ d L L₀ v g hM
  have hpX : ∀ z : Fin S₀.rank → AE D, d.pX *ᵥ (d.j0 *ᵥ z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
  have hpY : ∀ z : Fin S₀.rank → AE D, d.pY *ᵥ (d.j0 *ᵥ z) = 0 := fun z => by
    rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
  have hp0 : ∀ z : Fin S₀.rank → AE D, d.p0 *ᵥ (d.j0 *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
  have key : ∀ z : Fin S₀.rank → AE D, d.j0 *ᵥ z ∈ latV S L (· = v) ↔ z ∈ latV S₀ L₀ (· = v) := fun z => by
    rw [hM, hpX, hpY, hp0]
    simp only [Pi.zero_apply, matrixColumnScaledByAdele_zero, zero_mem, implies_true, true_and]
  have hj : ∀ z : Fin S₀.rank → AE D, mt S (d.emb0 g) *ᵥ (d.j0 *ᵥ z) = d.j0 *ᵥ (mt S₀ g *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  constructor
  · intro h z hz
    rw [← key, ← key, ← hj]
    exact h _ (matrix_mulVec_mem_adeleIdealSupportedOnPlaces _ _ hz)
  · intro h y hy
    have eX : d.pX *ᵥ (mt S (d.emb0 g) *ᵥ y) = d.pX *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
    have eY : d.pY *ᵥ (mt S (d.emb0 g) *ᵥ y) = d.pY *ᵥ y := by rw [Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
    have e0 : d.p0 *ᵥ (mt S (d.emb0 g) *ᵥ y) = mt S₀ g *ᵥ (d.p0 *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding]
    rw [hM y, hM (mt S (d.emb0 g) *ᵥ y), eX, eY, e0]
    exact and_congr Iff.rfl (and_congr Iff.rfl (h _ (matrix_mulVec_mem_adeleIdealSupportedOnPlaces _ _ hy)))

end GlobalTheory.FinPl

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl

noncomputable section
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacUnion

variable {D : D7}


open Classical in
def idemF (v : Pl D) : Af D.host.F :=
  ⟨fun w => if w = v then 1 else 0, Filter.Eventually.of_forall fun w => by
    show (if w = v then (1 : IsDedekindDomain.HeightOneSpectrum.adicCompletion D.host.F w) else 0) ∈ _
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

open Classical in
theorem evalV_idemF (v w : Pl D) : evalV D.host.F w (idemF v) = if w = v then 1 else 0 := rfl

theorem pairA_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  show ((0 : Ainf D.host.F) * 0, α * β) = ((0 : Ainf D.host.F), α * β)
  rw [mul_zero]

def idemE (v : Pl D) : AE D := algebraMap (AF D.host.F) (AE D) (pairA _ 0 (idemF v))

theorem idemE_mul_gen (v : Pl D) (α : Af D.host.F) (x : D.host.E) :
    idemE v * (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = pairA D.host.F 0 (idemF v * α) ⊗ₜ[D.host.F] x := by
  rw [idemE, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.algebraMap_self, RingHom.id_apply, pairA_mul]

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem idemE_smul_gen (v : Pl D) (α : Af D.host.F) (x : Fin T.rank → Fin S.rank → D.host.E) :
    idemE v • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] x i j : WO S T) =
      Matrix.of fun i j => pairA D.host.F 0 (idemF v * α) ⊗ₜ[D.host.F] x i j := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.of_apply, idemE_mul_gen]

theorem idemE_smul_mem (v : Pl D) {P : Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    idemE v • u ∈ latO S T LS LT (· = v) := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    have hα' : ∀ w, evalV D.host.F w α ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers D.host.F w := hα
    have hmem : idemF v * α ∈ intAf D.host.F := by
      simp only [intAf, Set.mem_setOf_eq]
      intro w
      rw [map_mul]
      refine mul_mem ?_ (hα' w)
      rw [evalV_idemF]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    refine ⟨idemF v * α, hmem, fun w hw => ?_, a, ha, s, hs, t, ht, idemE_smul_gen v α _⟩
    rw [map_mul, evalV_idemF, if_neg hw, zero_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.VacUnion
end
end
