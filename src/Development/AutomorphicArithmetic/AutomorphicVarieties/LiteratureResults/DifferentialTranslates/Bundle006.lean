module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.SecondFromFirstStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

theorem geo_main (h1 : AbsMain) (h2 : DEquiv) (h3 : InclFacts) (h4 : DExact) (h5 : Average) (h6 : Window) (h7 : Cutoff)
    {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {d : ℕ} (G : Geo Γ V S d)
    (hc : Convex ℝ G.Y) (hn : G.Y.Nonempty) (hp : G.Proper) (q n : ℕ) (w : Fin n → G.Om q)
    (hi : ∀ i γ, G.act q γ (w i) = w i) (hd : ∀ i, G.dOm q (w i) = 0)
    (hx : ∀ c : Fin n → ℂ, InvExact (Ω := fun q => G.Om q) G.act G.dOm (∑ i, c i • w i) → c = 0) :
    (n : Cardinal) ≤ Module.rank ℂ (groupCohomology (Rep.of G.lev) q) := by
  obtain ⟨W, hW⟩ := h6 Γ V S d G hp
  obtain ⟨u, hu⟩ := h7 Γ V S d G W hW
  obtain ⟨a1, a2, a3⟩ := h3 Γ V S d G hc hn
  exact h1 q Γ _ (fun q => G.Om q) G.lev G.act G.incl G.dOm a1 (h2 Γ V S d G) a2 a3 (h4 Γ V S d G hc) (h5 Γ V S d G u hu)
    n w hi hd hx

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
  (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) {q : ℕ}

private theorem alt_sum {V M : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup M] [Module ℝ M] {n : ℕ}
    (f : Fin n → V [⋀^Fin q]→ₗ[ℝ] M) (X : Fin q → V) : (∑ i, f i) X = ∑ i, f i X :=
  map_sum (AddMonoidHom.mk' (fun g : V [⋀^Fin q]→ₗ[ℝ] M => g X) fun _ _ => rfl) f _

theorem corr_zero : Corr (q := q) U Ξ 0 0 := fun g x X => by simp

theorem corr_sum {n : ℕ} (c : Fin n → ℂ) {α : Fin n → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))}
    {w : Fin n → (GL (Fin a) (Af E) ⧸ U) → HV E a → HV E a [⋀^Fin q]→L[ℝ] (Fin Ξ.d → ℂ)} (h : ∀ i, Corr U Ξ (α i) (w i)) :
    Corr U Ξ (∑ i, c i • α i) (∑ i, c i • w i) := fun g x X => by

  rw [alt_sum, map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, ContinuousAlternatingMap.sum_apply,
  Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlternatingMap.smul_apply, map_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Matrix.mulVec_smul, ← h i g x X]
  rfl

end

theorem deRhamInj_of (h1 : AbsMain) (h2 : DEquiv) (h3 : InclFacts) (h4 : DExact) (h5 : Average) (h6 : Window) (h7 : Cutoff)
    (h8 : Retract) (k1 : LocSec) (k2 : ConeConvex) (k3 : GeoProper) (k4 : Gauge) (k5 : LevelVal) (k6 : CentralOf)
    (k7 : CorrFwd) (k8 : CorrSmooth) (k9 : CorrBwd) (k10 : CorrCochain) (k11 : CorrUniq) (k12 : CorrInv) (k13 : CorrBasic)
    (k14 : CorrD) : DeRhamInj := by
  intro E _ _ _ a ha U _ hU Ξ q n α hα hind
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := k1 E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  have hv : ∀ i X, LeftInv (α i X) ∧ RightInv U (α i X) := fun i X => (k5 E a U Ξ _).1 ((hα i).1.val X)
  have hw : ∀ i, ∃ w : (geo ho U Ξ).Om q, Corr U Ξ (α i) w.1 := fun i => by
    obtain ⟨w, hw, h0⟩ := k7 E a U Ξ q (α i) (hα i).1.equiv fun X => (hv i X).2
    exact ⟨⟨w, fun s => ⟨k8 E a U Ξ q _ w hw s, h0 s⟩⟩, hw⟩
  choose w hw using hw
  rw [← geo_lev ho U Ξ]
  refine geo_main h1 h2 h3 h4 h5 h6 h7 (geo ho U Ξ) (k2 E a).1 ⟨_, hOne_mem_cone⟩ (k3 E a ho U Ξ hU) q n w
    (fun i => (k12 E a ho U Ξ q _ _ (hw i)).1 fun X => (hv i X).1) (fun i => ?_) fun c hc => hind c ?_
  · have h := k14 E a ho U Ξ q _ _ (hw i)
    rw [(hα i).2] at h
    exact (k11 E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)
  · have hs : Corr U Ξ (∑ i, c i • α i) (∑ i, c i • w i).1 := by
      rw [Submodule.coe_sum]
      exact corr_sum U Ξ c hw
    have hb : ∀ (X : Fin q → Herm E a) (i : Fin q), (X i).1 = 1 → (∑ i, c i • α i) X = 0 := fun X i hX => by
      rw [alt_sum]
      exact Finset.sum_eq_zero fun j _ => by rw [AlternatingMap.smul_apply, (hα j).1.basic X i hX, smul_zero]
    generalize ∑ i, c i • α i = β at hs hb
    generalize ∑ i, c i • w i = z at hs hc
    cases q with
    | zero =>
      obtain rfl : z = 0 := hc
      exact (k11 E a ho U Ξ 0).1 _ 0 _ hs (corr_zero U Ξ)
    | succ q =>
      obtain ⟨y, hy, rfl⟩ := hc
      obtain ⟨l, hl⟩ := k4 E a ha ho U Ξ hU
      obtain ⟨y', i1, i2, i3⟩ := h8 _ _ _ _ (geo ho U Ξ) (k2 E a).2 l hl q y hy ((k13 E a U Ξ _ _ _ hs).1 hb)
      obtain ⟨η, hη⟩ := k9 E a ho U Ξ q y'
      have e : dCo (smLie Ξ) η = β := (k11 E a ho U Ξ (q + 1)).1 _ _ _ (i3 ▸ k14 E a ho U Ξ q _ _ hη) hs
      have b := (k13 E a U Ξ _ _ _ hη).2 i2
      obtain ⟨c1, c2⟩ := k10 E a U Ξ q _ _ hη
      exact ⟨η, ⟨c1, b, fun X => (k5 E a U Ξ _).2 ((k12 E a ho U Ξ q _ _ hη).2 i1 X) (c2 X)
        (k6 E a _ (smLie Ξ) q η b (e ▸ hb) X)⟩, e⟩

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

namespace UpperTheory.V.Lit.Dr

private theorem entry_sq_le {ι : Type} [Fintype ι] {a : ℕ} (A : Matrix (Fin a) (Fin a) (ι → ℂ)) (i j : Fin a) :
    ‖A i j‖ ≤ Real.sqrt ‖(A * star A) i i‖ := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun w => Real.le_sqrt_of_sq_le ?_
  refine le_trans ?_ (norm_le_pi_norm ((A * star A) i i) w)
  have h : (A * star A) i i w = ((∑ k, ‖A i k w‖ ^ 2 : ℝ) : ℂ) := by
    simp [Matrix.mul_apply, Finset.sum_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  exact le_trans (Finset.single_le_sum (f := fun k => ‖A i k w‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ j)) (le_abs_self _)

theorem boundInf : BoundInf := by
  intro E _ _ a K hK hc
  obtain ⟨C₁, hC₁⟩ := hc.isBounded.exists_norm_le
  have hcont : ContinuousOn (fun p : HV E a => toL (Matrix.of p.1)⁻¹) K := by
    intro p hp
    obtain ⟨h, rfl⟩ := hK hp
    have hu : IsUnit (Matrix.of (sand h (hOne E a)).1).det := by
      rw [sand_val, hOne_val, mul_one, ← Matrix.isUnit_iff_isUnit_det]
      exact h.isUnit.mul h.isUnit.star
    have h1 : ContinuousAt (Inv.inv : Matrix (Fin a) (Fin a) (Cinf E) → _) (Matrix.of (sand h (hOne E a)).1) :=
      continuousAt_matrix_inv _ (by
        obtain ⟨u, hu⟩ := hu
        rw [← hu]
        exact NormedRing.inverse_continuousAt u)
    have h2 : Continuous (fun p : HV E a => (Matrix.of p.1 : Matrix (Fin a) (Fin a) (Cinf E))) :=
      continuous_subtype_val
    exact (ContinuousAt.comp (f := fun p : HV E a => (Matrix.of p.1 : Matrix (Fin a) (Fin a) (Cinf E))) h1
      h2.continuousAt).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := hc.exists_bound_of_continuousOn hcont
  refine ⟨a * (Real.sqrt C₁ * Real.sqrt C₂), fun g p hp hgp => ?_⟩
  obtain ⟨h, rfl⟩ := hK hp
  have hA : ∀ i j, ‖(g * h).val i j‖ ≤ Real.sqrt C₁ := fun i j => by
    refine (entry_sq_le _ i j).trans (Real.sqrt_le_sqrt (le_trans ?_ (hC₁ _ hgp)))
    have e : (g * h).val * star (g * h).val = Matrix.of (sand g (sand h (hOne E a))).1 := by
      rw [sand_val, sand_val, hOne_val]; simp only [Units.val_mul, star_mul, mul_assoc, one_mul]
    rw [e]
    exact (norm_le_pi_norm _ i).trans (norm_le_pi_norm (sand g (sand h (hOne E a))).1 i)
  have hB : ∀ i j, ‖(h⁻¹).val i j‖ ≤ Real.sqrt C₂ := fun i j => by
    have e0 : ‖(h⁻¹).val i j‖ = ‖(star (h⁻¹).val) j i‖ := by rw [Matrix.star_apply, norm_star]
    rw [e0]
    refine (entry_sq_le _ j i).trans (Real.sqrt_le_sqrt (le_trans ?_ (hC₂ _ hp)))
    have e : star (h⁻¹).val * star (star (h⁻¹).val) = (Matrix.of (sand h (hOne E a)).1)⁻¹ := by
      rw [sand_val, hOne_val, mul_one, star_star]
      refine (Matrix.inv_eq_left_inv ?_).symm
      rw [mul_assoc, ← mul_assoc (h⁻¹).val, Units.inv_mul, one_mul, ← star_mul, Units.mul_inv, star_one]
    rw [e]
    exact (norm_le_pi_norm _ j).trans (norm_le_pi_norm (toL (Matrix.of (sand h (hOne E a)).1)⁻¹) j)
  have h0 : (0 : ℝ) ≤ a * (Real.sqrt C₁ * Real.sqrt C₂) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  have e : g.val = (g * h).val * (h⁻¹).val := by rw [← Units.val_mul, mul_inv_cancel_right]
  change ‖g.val i j‖ ≤ _
  rw [e, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun k _ => (norm_mul_le _ _).trans
    (mul_le_mul (hA i k) (hB k j) (norm_nonneg _) (Real.sqrt_nonneg _))).trans ?_
  simp

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct ContDiff ComplexOrder

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem rat_mul_split (γ : GL (Fin a) E) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    infGL E a (GeneralLinearGroup.map (pInf E) (ratGL E a γ) * g) *
        finGL E a (GeneralLinearGroup.map (algebraMap E (Af E)) γ * x) =
      ratGL E a γ * (infGL E a g * finGL E a x) := by
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]
    rfl

private theorem split_ga (g : GA E a) :
    infGL E a (GeneralLinearGroup.map (pInf E) g) * finGL E a (GeneralLinearGroup.map (pFin E) g) = g := by
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]

private theorem act_corr (ho : IsOpen (cone E a)) (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ)
    (α : Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) (w : (geo ho U Ξ).Om q) (h : Corr U Ξ α w.1)
    (γ : (⊤ : Subgroup (GL (Fin a) E))) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) (X : Fin q → Herm E a) :
    ((geo ho U Ξ).act q γ w).1 (x : GL (Fin a) (Af E) ⧸ U) (sand g (hOne E a))
        (fun i => (2 : ℝ) • sand g (hv (X i))) =
      Ξ.mat g *ᵥ ev (α X) (ratGL E a (γ⁻¹).1 * (infGL E a g * finGL E a x)) := by
  have hs : ∀ p : HV E a, (geo ho U Ξ).ρ γ⁻¹ (sand g p) =
      sand (GeneralLinearGroup.map (pInf E) (ratGL E a (γ⁻¹).1) * g) p := fun p => by
    rw [geo_ρ, map_mul]; rfl
  have hσ : (geo ho U Ξ).σ γ⁻¹ (x : GL (Fin a) (Af E) ⧸ U) =
      ((GeneralLinearGroup.map (algebraMap E (Af E)) (γ⁻¹).1 * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
  rw [Geo.act_apply, hσ]
  simp only [map_smul, hs]
  rw [h, rat_mul_split, geo_ξ, Matrix.mulVec_mulVec, ← map_mul, ← mul_assoc, ← map_mul, ← map_mul]
  simp only [Subgroup.coe_inv, mul_inv_cancel, map_one, one_mul]

theorem corrInv : CorrInv := by
  intro E _ _ _ a ho U Ξ q α w h
  constructor
  · intro hL γ
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ cone E a
    · obtain ⟨g, rfl⟩ := hp
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
      ext1 v
      have hv' : v = fun i => (2 : ℝ) • sand g (hv (hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i)))) := by
        funext i
        rw [LinearEquiv.apply_symm_apply, map_smul, smul_smul, ← ContinuousLinearMap.mul_apply, ← map_mul,
          mul_inv_cancel, map_one]
        simp
      rw [hv', act_corr ho U Ξ q α w h, h, hL]
    · rw [(((geo ho U Ξ).act q γ w).2 s).2 p hp, (w.2 s).2 p hp]
  · intro hw X γ g
    have h1 := act_corr ho U Ξ q α w h (⟨γ, Subgroup.mem_top γ⟩ : (⊤ : Subgroup (GL (Fin a) E)))⁻¹
      (GeneralLinearGroup.map (pInf E) g) (GeneralLinearGroup.map (pFin E) g) X
    rw [hw, h, split_ga, inv_inv] at h1
    have h2 := congrArg (fun y => Ξ.mat (GeneralLinearGroup.map (pInf E) g)⁻¹ *ᵥ y) h1
    simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec] at h2
    exact h2.symm

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

section Components

variable {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ}

private def cmp (j : Fin d) : S ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] S :=
  (TensorProduct.rid ℂ S).toLinearMap ∘ₗ (LinearMap.proj j : (Fin d → ℂ) →ₗ[ℂ] ℂ).lTensor S

private theorem cmp_tmul (j : Fin d) (φ : S) (v : Fin d → ℂ) : cmp j (φ ⊗ₜ[ℂ] v) = v j • φ := by
  simp [cmp]

private theorem sum_cmp (m : S ⊗[ℂ] (Fin d → ℂ)) :
    ∑ j, cmp j m ⊗ₜ[ℂ] (Pi.single j 1 : Fin d → ℂ) = m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    simp only [cmp_tmul, TensorProduct.smul_tmul]
    rw [← TensorProduct.tmul_sum]
    congr 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  | add x y hx hy => simp only [map_add (f := _), TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

private theorem cmp_sum (L : Module.End ℂ S) (c : ℂ) (j : Fin d) (m : S ⊗[ℂ] (Fin d → ℂ)) :
    cmp j ((L.rTensor (Fin d → ℂ) + (Matrix.toLin' (c • (1 : Matrix (Fin d) (Fin d) ℂ))).lTensor S) m) =
      L (cmp j m) + c • cmp j m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => simp [cmp_tmul, smul_smul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _), smul_add]; abel

end Components

private theorem cmp_apply {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a d : ℕ}
    (m : Sm E a ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) (g : GA E a) : (cmp j m).1 g = ev m g j := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v => simp [cmp_tmul, mul_comm]
  | add x y hx hy => simp [hx, hy]

theorem levelVal : LevelVal := by
  intro E _ _ _ a U Ξ m
  refine ⟨fun hm => ?_, fun hl hr h0 => ?_⟩
  · induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, v, hφ, rfl⟩ := hx
      refine ⟨fun γ g => ?_, fun u hu g => ?_⟩
      · rw [ev_tmul, ev_tmul, hφ.1]
      · have h : φ.1 (g * finGL E a u) = φ.1 g := congrFun (congrArg Subtype.val (hφ.2.1 u hu)) g
        rw [ev_tmul, ev_tmul, h]
    | zero => exact ⟨fun γ g => by simp, fun u _ g => by simp⟩
    | add x y _ _ hx hy =>
      exact ⟨fun γ g => by simp only [map_add (f := _), Pi.add_apply, hx.1 γ g, hy.1 γ g],
        fun u hu g => by simp only [map_add (f := _), Pi.add_apply, hx.2 u hu g, hy.2 u hu g]⟩
    | smul c x _ hx =>
      exact ⟨fun γ g => by simp only [map_smul, Pi.smul_apply, hx.1 γ g],
        fun u hu g => by simp only [map_smul, Pi.smul_apply, hx.2 u hu g]⟩
  · rw [← sum_cmp m]
    refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨cmp j m, _, ⟨fun γ g => ?_, fun u hu => ?_, fun c hc => ?_⟩, rfl⟩
    · rw [cmp_apply, cmp_apply, hl]
    · refine Subtype.ext (funext fun g => ?_)
      change (cmp j m).1 (g * finGL E a u) = (cmp j m).1 g
      rw [cmp_apply, cmp_apply, hr u hu]
    · have h := cmp_sum (lie E a (oneL E a)) c j m
      rw [← hc] at h
      have h1 : cmp j (smLie Ξ (oneL E a) m) = 0 := by rw [h0, map_zero]
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left (h.symm.trans h1)

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem smooth_of_formula {f : GL (Fin a) (Cinf E) → ℂ} {F : Lie E a → ℂ} (h : ∀ y, f y = F (toL y.val))
    (hF : ContDiffOn ℝ ∞ F (invSet E a)) : ContDiffOn ℝ ∞ (extGL f) (invSet E a) :=
  hF.congr fun _ hx => (extGL_eventuallyEq h hx).self_of_nhds

private theorem smooth_reg (σ : GL (Fin a) (Cinf E) → GL (Fin a) (Cinf E))
    (h1 : ∀ τ i j, ContDiffOn ℝ ∞ (extGL fun y => coord τ ((σ y).val i j)) (invSet E a))
    (h2 : ∀ τ, ContDiffOn ℝ ∞ (extGL fun y => (coord τ (σ y).val.det)⁻¹) (invSet E a))
    {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) :
    ContDiffOn ℝ ∞ (extGL fun y => f (σ y)) (invSet E a) := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ | ⟨τ, rfl⟩ := hf
    exacts [h1 τ i j, h2 τ]
  | algebraMap c => exact smooth_of_formula (F := fun _ => c) (fun _ => rfl) contDiffOn_const
  | add f g _ _ hf hg => exact smooth_of_formula (fun y => by simp [extGL_val]) (hf.add hg)
  | mul f g _ _ hf hg => exact smooth_of_formula (fun y => by simp [extGL_val]) (hf.mul hg)

private theorem smooth_det (τ : E →+* ℂ) : ContDiff ℝ ∞ fun x : Lie E a => coord τ (Matrix.of x).det :=
  (coordL τ).contDiff.comp contDiff_det

private theorem smooth_det_inv (τ : E →+* ℂ) :
    ContDiffOn ℝ ∞ (fun x : Lie E a => (coord τ (Matrix.of x).det)⁻¹) (invSet E a) :=
  (smooth_det τ).contDiffOn.inv fun _ hx => (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (coord τ)).ne_zero

private theorem smooth_adj (τ : E →+* ℂ) (i j : Fin a) :
    ContDiff ℝ ∞ fun x : Lie E a => coord τ ((Matrix.of x).adjugate i j) := by
  have h : ContDiff ℝ ∞ fun x : Lie E a => (Function.update x j (Pi.single i 1) : Lie E a) := by
    refine contDiff_pi.2 fun k => ?_
    by_cases hk : k = j
    · subst hk
      simpa using contDiff_const
    · simpa [Function.update_of_ne hk] using contDiff_apply ℝ _ k
  simp only [Matrix.adjugate_apply]
  exact (smooth_det τ).comp h

omit [NumberField E] in
private theorem coord_inv_entry (τ : E →+* ℂ) (y : GL (Fin a) (Cinf E)) (i j : Fin a) :
    coord τ ((y⁻¹).val i j) = (coord τ y.val.det)⁻¹ * coord τ (y.val.adjugate i j) := by
  have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have e : y.val.adjugate = y.val.det • (y⁻¹).val := by
    calc y.val.adjugate = (y.val.adjugate * y.val) * (y⁻¹).val := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [Matrix.adjugate_mul, smul_mul_assoc, one_mul]
  rw [e, Matrix.smul_apply, smul_eq_mul, map_mul, inv_mul_cancel_left₀ (hu.map (coord τ)).ne_zero]

omit [NumberField E] in
private theorem coord_inv_det (τ : E →+* ℂ) (y : GL (Fin a) (Cinf E)) :
    (coord τ (y⁻¹).val.det)⁻¹ = coord τ y.val.det := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← map_mul, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, map_one]

theorem matSmooth : MatSmooth := by
  intro E _ _ a Ξ i j
  refine ⟨smooth_reg id (fun τ k l => ?_) (fun τ => ?_) (Ξ.reg i j),
    smooth_reg (fun y => y⁻¹) (fun τ k l => ?_) (fun τ => ?_) (Ξ.reg i j)⟩
  · exact smooth_of_formula (F := fun x => coordL τ (x k l)) (fun _ => rfl) (by fun_prop)
  · exact smooth_of_formula (fun _ => rfl) (smooth_det_inv τ)
  · exact smooth_of_formula (fun y => coord_inv_entry τ y k l) ((smooth_det_inv τ).mul (smooth_adj τ k l).contDiffOn)
  · exact smooth_of_formula (fun y => coord_inv_det τ y) (smooth_det τ).contDiffOn

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

namespace UpperTheory.V.Lit.Dr

theorem centralOf : CentralOf := by
  intro E _ _ a M _ _ _ _ L q η h1 h2 X
  let o : Herm E a := ⟨1, IsSelfAdjoint.one _⟩
  have h := h2 (Fin.cons o X) 0 rfl
  rw [dCo_apply, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero] at h
  · have e : Fin.removeNth (α := fun _ => Herm E a) 0 (Fin.cons o X) = X := by
      funext j; simp [Fin.removeNth]
    rw [e, Fin.val_zero, pow_zero, one_smul] at h
    exact h
  · intro i _
    have hz : η (Fin.removeNth (α := fun _ => Herm E a) i.succ (Fin.cons o X)) = 0 := by
      cases q with
      | zero => exact i.elim0
      | succ q =>
        refine h1 _ 0 ?_
        simp only [Fin.removeNth, Fin.succ_succAbove_zero, Fin.cons_zero]
        rfl
    rw [hz, map_zero, smul_zero]

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af
open scoped TensorProduct

namespace UpperTheory.V.Lit.Dr

theorem evK : EvK := by
  intro E _ _ _ a Ξ k m g
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    have h : ev (smK Ξ k (φ ⊗ₜ[ℂ] v)) g =
        φ.1 (g * infGL E a (Unitary.toUnits k)) • (Ξ.mat (Unitary.toUnits k) *ᵥ v) := rfl
    rw [h, ev_tmul, Matrix.mulVec_smul]
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy, Matrix.mulVec_add]

end UpperTheory.V.Lit.Dr
end
end
