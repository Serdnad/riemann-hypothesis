module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle093
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle111
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieListProducts
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle099
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SupportPhiZeroSubset
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankZeroApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableCoordinateMap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle105
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace CapSm

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def glW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (hπ : Qr.IsRepW k r z π) :
    Submodule ℂ (Mx k r) where
  carrier := {Z | Qr.InGlW k r z Z}
  add_mem' := fun {Z Z'} hZ hZ' => (elementary_lie_elements Wp k r z π hπ Z Z' hZ hZ').1.1
  zero_mem' := by
    have h := LieListProducts.gl_comb (LieListProducts.lie_zero (k := k) (r := r) (z := z)) (LieListProducts.lie_zero (k := k) (r := r) (z := z))
    simpa using h
  smul_mem' := fun c Z hZ => ((elementary_lie_elements Wp k r z π hπ Z Z hZ hZ).2.1 c).1

def ecL (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (hπ : Qr.IsRepW k r z π) :
    glW k r z π hπ →ₗ[ℂ] (Wp →L[ℂ] Wp) where
  toFun Z := QrD.ecOp π Z.1
  map_add' Z Z' := (elementary_lie_elements Wp k r z π hπ Z.1 Z'.1 Z.2 Z'.2).1.2
  map_smul' c Z := ((elementary_lie_elements Wp k r z π hπ Z.1 Z.1 Z.2 Z.2).2.1 c).2

theorem foldr_apply (l : List (Wp →L[ℂ] Wp)) (v : Wp) :
    List.foldr (fun (T : Wp → Wp) h => T h) v (List.map (fun T : Wp →L[ℂ] Wp => (⇑T : Wp → Wp)) l) =
      (l.foldr (fun (T acc : Wp →L[ℂ] Wp) => T.comp acc) 1) v := by
  induction l with
  | nil => simp
  | cons T l ih =>
    simp only [List.map_cons, List.foldr_cons, ContinuousLinearMap.comp_apply, ih]

theorem foldr_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (l : List (X → (Wp →L[ℂ] Wp)))
    (h : ∀ f ∈ l, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (l.map fun f => f x).foldr (fun (T acc : Wp →L[ℂ] Wp) => T.comp acc) 1) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (Wp →L[ℂ] Wp) × (Wp →L[ℂ] Wp) => p.1.comp p.2) :=
    (isBoundedBilinearMap_comp (𝕜 := ℂ) (E := Wp) (F := Wp) (G := Wp)).contDiff.restrict_scalars ℝ
  induction l with
  | nil => simpa using contDiff_const
  | cons f l ih =>
    have hf := h f (List.mem_cons_self ..)
    have hl := ih fun g hg => h g (List.mem_cons_of_mem _ hg)
    simp only [List.map_cons, List.foldr_cons]
    exact hc.comp (hf.prodMk hl)

theorem unitB_contDiff {m : ℕ} (a b : Fin m) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Bs : Fin m → Fin (2 * r + k + 1) → ℂ => unitB (Hpk k r) Bs a b) := by
  unfold unitB
  refine contDiff_pi.2 fun p => contDiff_pi.2 fun q => ?_
  simp only [Matrix.of_apply, herm, dotProduct, Pi.star_apply]
  refine ContDiff.mul (contDiff_apply_apply ℝ a p)
    (ContDiff.sum fun i _ => ?_)
  exact (Complex.conjCLE.contDiff.comp
    (contDiff_apply_apply ℝ b i)).mul contDiff_const

end CapSm

open CapSm in
theorem capacity_smoothness_holds : CapSmooth := by
  intro Wp _ _ _ k r m z π hπ w
  obtain ⟨G', hG'⟩ := Submodule.exists_isCompl (glW k r z π hπ)
  let Lext : Mx k r →ₗ[ℂ] (Wp →L[ℂ] Wp) := (ecL z π hπ).comp (Submodule.linearProjOfIsCompl _ _ hG')
  have hLext : ∀ Z (hZ : Qr.InGlW k r z Z), Lext Z = QrD.ecOp π Z := by
    intro Z hZ
    have hmem : Z ∈ glW k r z π hπ := hZ
    have e := Submodule.linearProjOfIsCompl_apply_left hG' ⟨Z, hmem⟩
    show ecL z π hπ (Submodule.linearProjOfIsCompl _ _ hG' Z) = _
    erw [e]
    rfl
  let Lc : Mx k r →L[ℂ] (Wp →L[ℂ] Wp) := LinearMap.toContinuousLinearMap Lext
  have hLc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun Z : Mx k r => Lc Z) := (Lc.restrictScalars ℝ).contDiff
  let T : Equiv.Perm (Fin m) → Fin m → (Fin m → Fin (2 * r + k + 1) → ℂ) → (Wp →L[ℂ] Wp) := fun σ t Bs =>
    (if σ t = t then (w - ((t : ℕ) : ℂ)) • (1 : Wp →L[ℂ] Wp) else 0) + Lc (unitB (Hpk k r) Bs (σ t) t)
  refine ⟨fun Bs => ∑ σ : Equiv.Perm (Fin m), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
    ((List.ofFn fun t => T σ t).map fun f => f Bs).foldr (fun (T acc : Wp →L[ℂ] Wp) => T.comp acc) 1, ?_, ?_⟩
  · refine ContDiff.sum fun σ _ => ContDiff.const_smul _ ?_
    refine foldr_contDiff _ fun f hf => ?_
    obtain ⟨t, rfl⟩ := List.mem_ofFn.1 hf
    exact contDiff_const.add (hLc.comp (unitB_contDiff _ _))
  · intro Bs hB v
    unfold capRep qmF
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [ContinuousLinearMap.smul_apply, ← foldr_apply]
    congr 2
    simp only [List.map_ofFn]
    congr 1
    funext t y
    have hl := QrD.frame_lie hB (σ t) t
    have hgl : Qr.InGlW k r z (unitB (Hpk k r) Bs (σ t) t) := hl
    simp only [Function.comp_apply, T, id]
    rw [ContinuousLinearMap.add_apply, QrD.ecRep_eq hπ.1 hπ.2 hl.1 hl.2 (k := k) (r := r), ← hLext _ hgl]
    congr 1
    split_ifs <;> simp

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
end
end

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

namespace LagrangeInterpolation

theorem aeval_eig {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (C : E →L[ℂ] E) (d : ℂ) (v : E)
    (hv : C v = d • v) (p : Polynomial ℂ) : Polynomial.aeval C p v = p.eval d • v := by
  have hpow : ∀ n : ℕ, (C ^ n) v = d ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), ContinuousLinearMap.add_apply, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, ContinuousLinearMap.mul_apply, hpow,
      Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_smul]

def lagP {ι κ : Type*} (c : ι → ℂ) (d : κ → ℂ) (bad : ι → Finset κ) (ρ : ι) : Polynomial ℂ :=
  ∏ σ ∈ bad ρ, (Polynomial.C (c ρ - d σ)⁻¹ * (Polynomial.X - Polynomial.C (d σ)))

theorem lagrangePoly_eval_eq_zero_of_mem {ι κ : Type*} (c : ι → ℂ) (d : κ → ℂ) (bad : ι → Finset κ) {ρ : ι} {σ : κ}
    (hb : σ ∈ bad ρ) : (lagP c d bad ρ).eval (d σ) = 0 := by
  rw [lagP, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hb (by simp)

theorem lagrangePoly_eval_eq_one {ι κ : Type*} (c : ι → ℂ) (d : κ → ℂ) (bad : ι → Finset κ) {ρ : ι} {σ : κ}
    (h : d σ = c ρ) (hne : ∀ τ ∈ bad ρ, d τ ≠ c ρ) : (lagP c d bad ρ).eval (d σ) = 1 := by
  rw [lagP, Polynomial.eval_prod]
  refine Finset.prod_eq_one fun τ hτ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [h]
  exact inv_mul_cancel₀ (sub_ne_zero.mpr (hne τ hτ).symm)

def qP (P : M.Par) (ρ : M.Ty P) : Polynomial ℂ :=
  ∏ i ∈ Finset.Icc 1 (P.k - 1), (Polynomial.X + Polynomial.C ((M.rho P ρ i : ℝ) : ℂ))

theorem eval_qP (P : M.Par) (ρ : M.Ty P) (Y : ℂ) : (qP P ρ).eval Y = M.xC P ρ Y := by
  rw [qP, Polynomial.eval_prod]
  simp [M.xC]

theorem generic (P : M.Par) : ∃ Y : ℂ, ∀ (ρ : M.Ty P) (σ : M.Ty (Qx8.P2 P)),
    (∃ Y', M.xC (Qx8.P2 P) σ Y' ≠ M.xC P ρ Y') → M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y := by
  classical
  let D : Polynomial ℂ := ∏ ρ : M.Ty P, ∏ σ : M.Ty (Qx8.P2 P),
    (if qP (Qx8.P2 P) σ = qP P ρ then 1 else qP (Qx8.P2 P) σ - qP P ρ)
  have hD : D ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun ρ _ => Finset.prod_ne_zero_iff.mpr fun σ _ => ?_
    split_ifs with h
    · exact one_ne_zero
    · exact sub_ne_zero.mpr h
  obtain ⟨Y, hY⟩ : ∃ Y, D.eval Y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hD (Polynomial.funext fun y => by rw [hcon y, Polynomial.eval_zero])
  refine ⟨Y, fun ρ σ hex hEq => ?_⟩
  obtain ⟨Y', hY'⟩ := hex
  have hne : qP (Qx8.P2 P) σ ≠ qP P ρ := fun h => hY' (by rw [← eval_qP, ← eval_qP, h])
  apply hY
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ ρ) ?_
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ σ) ?_
  rw [if_neg hne, Polynomial.eval_sub, eval_qP, eval_qP, hEq, sub_self]

end LagrangeInterpolation

open LagrangeInterpolation in
theorem lagrange_annihilation : Lagrange := by
  classical
  intro hE P hOK hk
  have hOK2 : (Qx8.P2 P).OK := by
    unfold Qx8.P2
    refine ⟨hOK.k_pos, hOK.T_pos, hOK.T'_pos, hOK.int_u, hOK.int_u, fun i hmem => ?_⟩
    have g := hOK.gap i hmem
    simp only [M.Par.lo, M.Par.hi, max_self, min_self] at g ⊢
    linarith [le_max_left (P.u (i + 1)) (P.u' (i + 1)), min_le_left (P.u i) (P.u' i)]
  obtain ⟨Y, hY⟩ := generic P
  refine ⟨Y + ((P.k : ℂ) - 2) / 2, fun ρ => lagP (fun ρ => M.xC P ρ Y) (fun σ => M.xC (Qx8.P2 P) σ Y)
    (fun ρ => Finset.univ.filter fun σ => M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y) ρ, ?_⟩
  intro Wp _ _ _ z e π hz hT hπ he hez hee Fr hFr C hC ρ
  obtain ⟨S, hSi, -, hSc⟩ := branching_proof Wp (Qx8.P2 P) hOK2 rfl z e π hz hT hπ he hez hee
  have hSv : ∀ σ, ∀ v ∈ S σ, ∀ Fr' : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, IsFrameOf P.k P.r [z, e] Fr' →
      ∀ w', capRep P.k P.r π Fr' w' v = M.xC (Qx8.P2 P) σ (w' - ((P.k : ℂ) - 2) / 2) • v :=
    fun σ v hv Fr' hFr' w' => hSc Fr' hFr' σ w' v hv
  have hCv : ∀ σ, ∀ v ∈ S σ, C v = M.xC (Qx8.P2 P) σ Y • v := by
    intro σ v hv
    rw [hC, hSv σ v hv Fr hFr, add_sub_cancel_right]
  have hKs : ∀ σ, ∀ v ∈ S σ,
      v ∈ Kset P.k P.r z e π (fun w' => M.xC (Qx8.P2 P) σ (w' - ((P.k : ℂ) - 2) / 2)) :=
    fun σ v hv Fr' hFr' w' => hSv σ v hv Fr' hFr' w'
  have hRep : Qr.IsRepW P.k P.r z π := ⟨hπ.2.1, hπ.2.2.1⟩
  have hOrth : ∀ σ, M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y → ∀ v ∈ S σ,
      v ∈ (K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2)))ᗮ := by
    intro σ hne v hv
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction (fun x hx => ?_) ?_ (fun x y _ _ hx hy => ?_) (fun a x _ hx => ?_) hu
    · exact hE Wp P.k P.r z e π hz hT hRep hπ.2.2.2.1 ⟨Fr, hFr⟩ _ _ x v hx (hKs σ v hv)
        ⟨Y + ((P.k : ℂ) - 2) / 2, by simpa using hne.symm⟩
    · exact inner_zero_left _
    · rw [inner_add_left, hx, hy, add_zero]
    · rw [inner_smul_left, hx, mul_zero]
  have hIn : ∀ σ, M.xC (Qx8.P2 P) σ Y = M.xC P ρ Y → ∀ v ∈ S σ,
      v ∈ K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2)) := by
    intro σ heq v hv
    have hfun : ∀ Y', M.xC (Qx8.P2 P) σ Y' = M.xC P ρ Y' := by
      by_contra hc
      push_neg at hc
      exact hY ρ σ hc heq
    refine Submodule.subset_span (fun Fr' hFr' w' => ?_)
    show capRep P.k P.r π Fr' w' v = M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2) • v
    rw [hSv σ v hv Fr' hFr' w', hfun]
  ext v
  have hv : v ∈ ⨆ σ, S σ := by
    rw [hSi.submodule_iSup_eq_top]
    exact Submodule.mem_top
  refine Submodule.iSup_induction S (motive := fun x =>
    (Polynomial.aeval C) (lagP (fun ρ => M.xC P ρ Y) (fun σ => M.xC (Qx8.P2 P) σ Y)
      (fun ρ => Finset.univ.filter fun σ => M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y) ρ) x =
    (K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2))).starProjection x) hv ?_ ?_ ?_
  · intro σ x hx
    rw [aeval_eig C _ x (hCv σ x hx)]
    by_cases hb : M.xC (Qx8.P2 P) σ Y = M.xC P ρ Y
    · rw [lagrangePoly_eval_eq_one (fun ρ => M.xC P ρ Y) (fun σ => M.xC (Qx8.P2 P) σ Y)
        (fun ρ => Finset.univ.filter fun σ => M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y) hb (fun τ hτ => (Finset.mem_filter.mp hτ).2), one_smul]
      exact ((Submodule.starProjection_eq_self_iff).mpr (hIn σ hb x hx)).symm
    · rw [lagrangePoly_eval_eq_zero_of_mem (fun ρ => M.xC P ρ Y) (fun σ => M.xC (Qx8.P2 P) σ Y)
        (fun ρ => Finset.univ.filter fun σ => M.xC (Qx8.P2 P) σ Y ≠ M.xC P ρ Y) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩), zero_smul]
      exact ((Submodule.starProjection_apply_eq_zero_iff _).mpr (hOrth σ hb x hx)).symm
  · simp only [map_zero]
  · intro x y hx hy
    rw [map_add (f := _), map_add (f := _), hx, hy]

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
end
end

section

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.OJ

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

private theorem herm_hpk_bvec_esI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (esI k r a)) = v (eI k r a) := by
  have ha := a.isLt
  have he : (eI k r a).val = a.val := rfl
  have hs : (esI k r a).val = 2 * r + k - a.val := rfl
  unfold herm bvec
  rw [← Pi.single_star, star_one, single_dotProduct, one_mul, Matrix.mulVec, dotProduct,
    Finset.sum_eq_single (eI k r a)]
  · have h1 : Hpk k r (esI k r a) (eI k r a) = 1 := by
      simp only [Hpk]
      rw [if_neg (fun h => absurd h.1 (by omega)), if_pos ⟨by omega, by omega⟩]
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ a.val := fun h => hj (Fin.ext (h.trans he.symm))
    have h0 : Hpk k r (esI k r a) j = 0 := by
      simp only [Hpk]
      rw [if_neg (fun h => absurd h.1 (by omega)), if_neg (fun h => hj' (by have := h.2; omega)),
        if_neg (fun h => absurd h.2.1 (by omega))]
    rw [h0, zero_mul]
  · simp

theorem ell_eq (z : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : ell k r z g = C2.simpleUp (C2.uMap k r z g) := by
  unfold ell C2.simpleUp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, lt_self_iff_false, dite_false, add_zero, Fin.val_castSucc]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha : a.val + 1 < r + 1 := by omega
  rw [dite_eq_left ha]
  simp only [C2.uMap, Fin.val_castSucc, a.isLt, dite_true]
  rw [herm_hpk_bvec_esI]
  simp only [fvec]
  by_cases h1 : a.val + 1 < r
  · simp [h1, bvec, Matrix.mulVec_single]
  · simp [h1]

theorem psi_prod (a b : ℂ) :
    Complex.exp (Complex.I * (((1 : ℝ) * (cStd * a).re - (1 : ℝ) * (cStd * b).re : ℝ) : ℂ)) =
      C2.psiC cStd a * star (C2.psiC cStd b) := by
  simp only [C2.psiC, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem xi_at (S : B.RealPlaceData k r Wp Wq) {v u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hv : v ∈ C2.UTset (r + 1))
    (hu' : u' ∈ C2.UTset (r + 1)) {n0 n0' : Mt k r} (hn0 : Matrix.of n0 ∈ C2.N0set k r S.z)
    (hn0' : Matrix.of n0' ∈ C2.N0set k r S.z') (h h' : Mt k r) :
    B.xiTau S (1, 1) ((h, Matrix.of.symm (C2.tauM k r S.z v * Matrix.of n0)),
      (h', Matrix.of.symm (C2.tauM k r S.z' u' * Matrix.of n0'))) =
      C2.psiC cStd (C2.simpleUp v) * star (C2.psiC cStd (C2.simpleUp u')) := by
  have key : ∀ {z : Fin (2 * r + k + 1) → ℂ}, C2.StdZ k r z → ∀ {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ},
      v ∈ C2.UTset (r + 1) → ∀ {n0 : Mt k r}, Matrix.of n0 ∈ C2.N0set k r z →
      ell k r z (C2.tauM k r z v * Matrix.of n0) = C2.simpleUp v := by
    intro z hz v hv n0 hn0
    rw [ell_eq, HC.uMap_mul hz (HC.tau_N hz hv) hn0.1, HC.tau_u hz hv, hn0.2, mul_one]
  unfold B.xiTau B.lam
  simp only [Equiv.apply_symm_apply]
  rw [key ⟨S.z_mem, S.T_pos⟩ hv hn0, key ⟨S.z'_mem, S.T'_pos⟩ hu' hn0']
  exact psi_prod _ _

theorem pt_eq (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (Y : (C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ)) (p : B.SS k r)
    (hp1 : Matrix.of p.1.2 ∈ C2.N0set k r S.z) (hp2 : Matrix.of p.2.2 ∈ C2.N0set k r S.z') :
    D.orbIntegrand S γ F (Xi0 S w ((p.1.1, (Y.1, p.1.2)), (p.2.1, (Y.2, p.2.2)))) =
      (C2.psiC cStd (C2.simpleUp (lowP w Y.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper Y.2)))) •
        B.rho S p F ((C2.tauM k r S.z (lowP w Y.1)ᴴ)⁻¹ * γ * C2.tauM k r S.z' (G.upper Y.2)) := by
  have hv := OD.lowPH_UT Y.1
  have hu := HC.upper_mem Y.2
  have hr : B.rho S ((p.1.1, Matrix.of.symm (C2.tauM k r S.z (lowP w Y.1)ᴴ * Matrix.of p.1.2)),
        (p.2.1, Matrix.of.symm (C2.tauM k r S.z' (G.upper Y.2) * Matrix.of p.2.2))) F γ =
      B.rho S p F ((C2.tauM k r S.z (lowP w Y.1)ᴴ)⁻¹ * γ * C2.tauM k r S.z' (G.upper Y.2)) := by
    unfold B.rho B.sgs
    simp only [Equiv.apply_symm_apply, Matrix.mul_inv_rev, Matrix.mul_assoc]
  unfold D.orbIntegrand
  rw [show Xi0 S w ((p.1.1, (Y.1, p.1.2)), (p.2.1, (Y.2, p.2.2))) =
      ((p.1.1, Matrix.of.symm (C2.tauM k r S.z (lowP w Y.1)ᴴ * Matrix.of p.1.2)),
        (p.2.1, Matrix.of.symm (C2.tauM k r S.z' (G.upper Y.2) * Matrix.of p.2.2))) from rfl,
    xi_at S hv hu hp1 hp2 p.1.1 p.2.1, hr]

theorem cell_int [CompleteSpace Wp] (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    {μ0 μ0' : Measure (Mt k r)} (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
    (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0') (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hI : Integrable (fun q => D.orbIntegrand S γ F (Xi0 S w q)) (nuR S w μ0 μ0')) :
    ∫ q, D.orbIntegrand S γ F (Xi0 S w q) ∂(nuR S w μ0 μ0') =
      ∫ Y : (C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ),
        (C2.psiC cStd (C2.simpleUp (lowP w Y.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper Y.2)))) •
          PBI.fibInt S μ0 μ0' F ((C2.tauM k r S.z (lowP w Y.1)ᴴ)⁻¹ * γ * C2.tauM k r S.z' (G.upper Y.2)) := by
  have := Dx2.OrbJ.sigmaF hμ0
  have := Dx2.OrbJ.sigmaF hμ0'
  have := Dx2.OrbJ.sigmaF S.haarW
  have := Dx2.OrbJ.sigmaF S.haarW'
  have hmp := RE.mp_rearr S w hμ0 hμ0'
  let Φ : ((C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ)) × B.SS k r → (Wq →L[ℂ] Wp) := fun x =>
    (C2.psiC cStd (C2.simpleUp (lowP w x.1.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper x.1.2)))) •
      B.rho S x.2 F ((C2.tauM k r S.z (lowP w x.1.1)ᴴ)⁻¹ * γ * C2.tauM k r S.z' (G.upper x.1.2))
  have hae : (fun q => D.orbIntegrand S γ F (Xi0 S w q)) =ᵐ[nuR S w μ0 μ0'] fun q => Φ (RE.rearr k r w q) := by
    filter_upwards [OG.ae_good S w hμ0 hμ0'] with q hq
    rw [RE.rearr_apply]
    exact pt_eq S γ w F (q.1.2.1, q.2.2.1) ((q.1.1, q.1.2.2), (q.2.1, q.2.2.2)) hq.2.1 hq.2.2.2
  have hIp : Integrable Φ (((volume : Measure (C2.LPidx w → ℂ)).prod (volume : Measure (G.UT (r + 1) → ℂ))).prod
      ((S.μW.prod μ0).prod (S.μW'.prod μ0'))) :=
    (hmp.integrable_comp_emb (RE.rearr k r w).measurableEmbedding).mp (hI.congr hae)
  rw [integral_congr_ae hae, hmp.integral_comp' Φ, integral_prod Φ hIp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
  simp only [Φ]
  rw [integral_smul]
  rfl

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.OJ
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem jdl_pow (d : ℕ) (ν : Fin (d + 1) → ℝ) (hν : Function.Injective ν) (k : ℕ) (hk : k ≤ d) (y : ℂ) :
    y ^ k = ∑ j, lagC ν j y * ((ν j : ℝ) : ℂ) ^ k := by
  classical
  have hinj : Set.InjOn (fun j : Fin (d + 1) => ((ν j : ℝ) : ℂ)) (Finset.univ : Finset (Fin (d + 1))) :=
    fun a _ b _ h => hν (Complex.ofReal_injective h)
  have hdeg : (Polynomial.X ^ k : Polynomial ℂ).degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin, Polynomial.degree_X_pow]
    exact_mod_cast Nat.lt_succ_of_le hk
  have hf := Lagrange.eq_interpolate hinj hdeg
  have h := congrArg (Polynomial.eval y) hf
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  congr 1
  unfold lagC Lagrange.basis
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [div_eq_inv_mul]

theorem jdl_interp {R : Type} [Ring R] [Algebra ℂ R] (f : ℂ → R) (d : ℕ)
    (hf : Formalism.FourierDecayAlt.P.MAx3.G.PolyIn (fun s => f (0 + s)) d) (ν : Fin (d + 1) → ℝ) (hν : Function.Injective ν)
    (y : ℂ) : f y = ∑ j, lagC ν j y • f ((ν j : ℝ) : ℂ) := by
  obtain ⟨a, ha⟩ := hf
  have hf' : ∀ s, f s = ∑ k ∈ Finset.range (d + 1), s ^ k • a k := fun s => by simpa using ha s
  have e1 : f y = ∑ k ∈ Finset.range (d + 1), (∑ j, lagC ν j y * ((ν j : ℝ) : ℂ) ^ k) • a k := by
    rw [hf' y]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← jdl_pow d ν hν k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) y]
  rw [e1]
  simp only [hf', Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem hat_lagrange_decay_holds : JDHatLagrange := by
  intro P L ν hν y
  exact ⟨jdl_interp (fun s => L.R0 s) (P.r + 1) (Formalism.FourierDecayAlt.P.MAx3.G.raising_operator_polynomial P L 0) ν hν y,
    jdl_interp (fun s => L.R0v s) (P.r + 1) (Formalism.FourierDecayAlt.P.MAx3.L.raising_variant_polynomial P L 0) ν hν y⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end
