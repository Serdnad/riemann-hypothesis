module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlgIrr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle405
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.count :
    UpperTheory.V.Lit.Bor.Count := by
  classical
  intro X S deg κ hκ
  have hq : ∀ q, Cardinal.mk {x : S // deg x = q} ≤ κ q := by
    intro q
    let e := Fintype.equivFin {x : S // deg x = q}
    rw [Cardinal.mk_fintype]
    refine hκ q _ (fun i => ((e.symm i).1 : X)) ?_ (fun i => ⟨(e.symm i).1.2, (e.symm i).2⟩)
    intro i j hij
    exact e.symm.injective (Subtype.ext (Subtype.ext hij))
  calc (S.card : Cardinal) = Cardinal.mk S := (Cardinal.mk_coe_finset).symm
    _ = Cardinal.mk (Σ q, {x : S // deg x = q}) :=
        (Cardinal.mk_congr (Equiv.sigmaFiberEquiv (fun x : S => deg x))).symm
    _ = Cardinal.sum (fun q => Cardinal.mk {x : S // deg x = q}) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum κ := Cardinal.sum_le_sum _ _ hq
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.ipDef :
    UpperTheory.V.Lit.Bor.IpDef := by
  intro E _ _ _ a n e he M _ _ _ _ H N hH q
  refine ⟨fun ω η => ?_, fun ω hω => ⟨?_, fun h0 => ?_⟩⟩

  · simp only [ip, map_sum]
    exact Finset.sum_congr rfl fun I _ => hH.herm _ _
  · simp only [ip, Complex.re_sum]
    exact Finset.sum_nonneg fun I _ => hH.nonneg _ (hω _)
  · have hre : ∑ I : Fin q → Fin n, (H (ω fun i => e (I i)) (ω fun i => e (I i))).re = 0 := by
      rw [← Complex.re_sum]
      exact congrArg Complex.re h0
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun I _ => hH.nonneg _ (hω _))).1 hre
    have h2 : ∀ I : Fin q → Fin n, (ω fun i => e (I i)) = 0 := fun I => by
      refine hH.definite _ (hω _) (Complex.ext (h1 I (Finset.mem_univ _)) ?_)
      exact Complex.conj_eq_iff_im.1 (hH.herm _ _).symm
    refine AlternatingMap.ext fun X => ?_
    have hX : X = fun i => ∑ j, trF (e j).1 (X i).1 • e j := funext fun i => he (X i)
    have h3 : ω X = ∑ I : Fin q → Fin n, ω fun i => trF (e (I i)).1 (X i).1 • e (I i) := by
      conv_lhs => rw [hX]
      exact ω.toMultilinearMap.map_sum (fun i j => trF (e j).1 (X i).1 • e j)
    rw [h3, AlternatingMap.zero_apply]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [ω.map_smul_univ (fun i => trF (e (I i)).1 (X i).1) (fun i => e (I i)), h2, smul_zero]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.kugaZero :
    UpperTheory.V.Lit.Bor.KugaZero := by
  intro E _ _ _ a n e M _ _ _ _ A B hc ω hω X
  rw [del_apply]
  simp only [cas, LinearMap.sub_apply, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := by
    have h : star (e j).1 = (e j).1 := (e j).2
    rw [star_smul, h, Complex.star_def, Complex.conj_I, neg_smul]
  have h0 := hω _ hs X
  rw [Fin.sum_univ_zero, LinearMap.add_apply, LinearMap.add_apply] at h0
  have h1 : ∀ (Y Z) (m : M), A Y (B Z m) = B Z (A Y m) := fun Y Z m => LinearMap.congr_fun (hc Y Z).eq m
  have h2 := congrArg (B (toL (Complex.I • (e j).1))) h0
  have h3 := congrArg (A (toL (Complex.I • (e j).1))) h0
  rw [map_add (f := _), map_zero] at h2 h3
  rw [h1] at h3
  have h4 : B (toL (Complex.I • (e j).1)) (B (toL (Complex.I • (e j).1)) (ω X)) =
      A (toL (Complex.I • (e j).1)) (A (toL (Complex.I • (e j).1)) (ω X)) := by
    rw [← sub_eq_zero, ← sub_self (0 : M)]
    nth_rewrite 1 [← h2]
    rw [← h3]
    abel
  rw [dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) X]
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero, LinearMap.add_apply, map_add (f := _), Module.End.mul_apply, h1, h4]
  abel
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem lie_left (X : Lie E a) (φ : Sm E a) (h g : GA E a) (hφ : ∀ g, φ.1 (h * g) = φ.1 g) :
    (lie E a X φ).1 (h * g) = (lie E a X φ).1 g := by
  have e : chart φ.1 (h * g) =ᶠ[nhds (oneL E a)] chart φ.1 g := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet (1 : GL (Fin a) (Cinf E)))] with x hx
    obtain ⟨u, hu⟩ := hx
    obtain rfl : x = toL u.val := hu.symm
    rw [chart_val, chart_val, mul_assoc, hφ]
  change fderiv ℝ (chart φ.1 (h * g)) (oneL E a) X = fderiv ℝ (chart φ.1 g) (oneL E a) X
  rw [e.fderiv_eq]

private theorem lie_fin (X : Lie E a) (k : GL (Fin a) (Af E)) (φ : Sm E a) :
    act (.fin k) (lie E a X φ) = lie E a X (act (.fin k) φ) :=
  (LinearMap.congr_fun (lie_rt_fin X k) φ).symm

private theorem lie_one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem level_lie (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) :
    IsOpen {k | act (.fin k) (lie E a X φ) = lie E a X φ} := by
  let ρ : GL (Fin a) (Af E) →* Module.End ℂ (Sm E a) := (rt E a).comp (finGL E a)
  let S : Sm E a → Subgroup (GL (Fin a) (Af E)) := fun ψ =>
    { carrier := {k | ρ k ψ = ψ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        change ρ (x * y) ψ = ψ
        rw [map_mul, mul_apply_eq_comp, hy, hx]
      inv_mem' := fun {x} hx => by
        change ρ x⁻¹ ψ = ψ
        have hx' : ρ x ψ = ψ := hx
        conv_lhs => rw [← hx', ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self] }
  have hle : S φ ≤ S (lie E a X φ) := fun k hk => (lie_fin X k φ).trans (congrArg (lie E a X) hk)
  exact Subgroup.isOpen_mono hle h

private theorem isSq_lie (r : ℝ) (X : Lie E a) (φ : Sm E a) (h : IsSq r φ) : IsSq r (lie E a X φ) := by
  refine ⟨fun γ g => lie_left X φ _ g (h.left γ), level_lie X φ h.level, ?_, ?_⟩
  · rw [lie_one_comm, h.one, map_smul]
  · intro l
    have := h.sq (l ++ [X])
    rwa [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, mul_apply_eq_comp] at this

end

theorem UpperTheory.V.Lit.Bor.sqLie :
    UpperTheory.V.Lit.Bor.SqLie := by
  intro E _ _ _ a r
  refine ⟨isSq_lie r, fun X φ hφ => ?_⟩
  have h : sqSub E a r ≤ (sqSub E a r).comap (lie E a X) :=
    Submodule.span_le.2 fun ψ hψ => Submodule.subset_span (isSq_lie r X ψ hψ)
  exact h hφ
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem cmp_lTensor_toLin {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j ((Matrix.toLin' Q).lTensor W y) = ∑ k, Q j k • cmp k y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul φ v =>
    simp only [LinearMap.lTensor_tmul, cmp_tmul, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Finset.sum_smul, smul_smul]
  | add a b ha hb =>
    simp only [map_add (f := _), ha, hb, smul_add, Finset.sum_add_distrib]

private theorem cmp_rTensor_end {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

theorem UpperTheory.V.Lit.Bor.tformAdj :
    UpperTheory.V.Lit.Bor.TformAdj := by
  intro W _ _ d H N G P Q S T
  refine ⟨fun hPQ x y => ?_, fun hST x hx y hy => ?_⟩
  · have key : ∀ a b, (G * Q) a b = (Pᴴ * G) a b := fun a b => by rw [hPQ]
    have hL : tform H G x ((Matrix.toLin' Q).lTensor W y)
        = ∑ a, ∑ b, (G * Q) a b * H (cmp a x) (cmp b y) := by
      rw [tform_apply]

      simp only [cmp_lTensor_toLin, map_sum, map_smul, smul_eq_mul, Matrix.mul_apply,
      Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    have hR : tform H G ((Matrix.toLin' P).lTensor W x) y
        = ∑ a, ∑ b, (Pᴴ * G) a b * H (cmp a x) (cmp b y) := by
      rw [tform_apply]

      simp only [cmp_lTensor_toLin, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.conjTranspose_apply,
      starRingEnd_apply, Finset.mul_sum, Finset.sum_mul]
      conv_lhs => rw [Finset.sum_comm]
      conv_lhs => enter [2, j]; rw [Finset.sum_comm]
      conv_lhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i _ => by ring
    rw [hL, hR]
    simp only [key]
  · rw [mem_tens] at hx hy
    rw [tform_apply, tform_apply]
    simp only [cmp_rTensor_end, hST _ (hx _) _ (hy _)]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.ipAdj :
    UpperTheory.V.Lit.Bor.IpAdj := by
  intro E _ _ _ a n e M _ _ _ _ L L' H N hadj q ω η hω hη
  have key : ∀ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
      H (ω fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) =
      ip e H (del L' e ω) η := fun i => by
    rw [← (Fin.insertNthEquiv (fun _ => Fin n) i).sum_comp, Fintype.sum_prod_type, Finset.sum_comm, ip]
    refine Finset.sum_congr rfl fun J _ => ?_

    rw [del_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : (fun k => e ((Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) k)) =
        i.insertNth (α := fun _ => Herm E a) (e j) (fun k => e (J k)) := by
      funext k
      refine Fin.succAboveCases i ?_ (fun k => ?_) k <;> simp [Fin.insertNthEquiv]
    have h2 : (Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) i = j := by simp [Fin.insertNthEquiv]
    rw [h1, h2, Fin.removeNth_insertNth, AlternatingMap.map_insertNth, ← hadj _ _ (hω _) _ (hη _),
      map_zsmul, map_zsmul, LinearMap.smul_apply, smul_smul, ← mul_pow]
    simp
  have h0 : ip e H ω (dCo L η) = ∑ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
      H (ω fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) := by
    rw [Finset.sum_comm, ip]
    refine Finset.sum_congr rfl fun I _ => ?_

    rw [dCo_apply, map_sum]
  rw [h0, Finset.sum_congr rfl fun i _ => key i]
  simp
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a}

private theorem rel_mono {P Q : Sm E a → Prop} (h : ∀ φ, P φ → Q φ) {q : ℕ}
    {ω : GlobalTheory.GKCoh.Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))} (hω : IsRelCochain Ξ P ω) :
    IsRelCochain Ξ Q ω :=
  ⟨hω.equiv, hω.basic, fun X => Submodule.span_mono (by
    rintro _ ⟨φ, v, hφ, rfl⟩
    exact ⟨φ, v, h φ hφ, rfl⟩) (hω.val X)⟩

private theorem level_mono {U U' : Subgroup (GL (Fin a) (Af E))} (h : U' ≤ U) (φ : Sm E a) (hφ : IsLevelFn U Ξ φ) :
    IsLevelFn U' Ξ φ := ⟨hφ.1, fun u hu => hφ.2.1 u (h hu), hφ.2.2⟩

variable {U : Subgroup (GL (Fin a) (Af E))} {r : ℝ} {n : ℕ} {e : Fin n → GlobalTheory.GKCoh.Herm E a}

private theorem harm_zero {q : ℕ} :
    IsHarm U Ξ r e (0 : GlobalTheory.GKCoh.Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) := by
  refine ⟨⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩, ?_, ?_⟩
  · exact AlternatingMap.ext fun X => by simp [dCo_apply]
  · cases q with
    | zero => trivial
    | succ q => exact AlternatingMap.ext fun X => by simp [del_apply]

private theorem harm_comb {q : ℕ} (c : ℂ)
    {ω η : GlobalTheory.GKCoh.Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))} (hω : IsHarm U Ξ r e ω)
    (hη : IsHarm U Ξ r e η) : IsHarm U Ξ r e (c • ω + η) := by
  have ap : ∀ X, (c • ω + η) X = c • ω X + η X := fun X => rfl
  refine ⟨⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, ?_, ?_⟩
  · rw [ap, ap, hω.rel.equiv k X, hη.rel.equiv k X, map_add (f := _), map_smul]
  · rw [ap, hω.rel.basic X i hi, hη.rel.basic X i hi, smul_zero, add_zero]
  · rw [ap]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hω.rel.val X)) (hη.rel.val X)
  · refine AlternatingMap.ext fun X => ?_
    have h1 := DFunLike.congr_fun hω.closed X
    have h2 := DFunLike.congr_fun hη.closed X
    rw [dCo_apply, AlternatingMap.zero_apply] at h1 h2 ⊢
    simp only [ap, map_add (f := _), map_smul, smul_add, Finset.sum_add_distrib, h2, add_zero]
    rw [← smul_zero c, ← h1, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · cases q with
    | zero => trivial
    | succ q =>
      refine AlternatingMap.ext fun X => ?_
      have h1 := DFunLike.congr_fun (show del _ e ω = 0 from hω.coclosed) X
      have h2 := DFunLike.congr_fun (show del _ e η = 0 from hη.coclosed) X
      rw [del_apply, AlternatingMap.zero_apply] at h1 h2 ⊢
      simp only [ap, map_add (f := _), map_smul, Finset.sum_add_distrib, h2, add_zero, ← Finset.smul_sum, h1, smul_zero]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Lit.Bor.harmLin :
    UpperTheory.V.Lit.Bor.HarmLin := by
  intro E _ _ _ a n e U Ξ r q
  refine ⟨fun s ω c h => ?_, fun ω => ⟨fun h => rel_mono (fun _ hφ => hφ.1) h.rel, fun U' hU =>
    ⟨fun h => ⟨rel_mono (fun φ hφ => ⟨level_mono hU φ hφ.1, hφ.2⟩) h.rel, h.closed, h.coclosed⟩,
      rel_mono (level_mono hU)⟩⟩⟩
  induction (Finset.univ : Finset (Fin s)) using Finset.cons_induction with
  | empty => exact harm_zero
  | cons j t hj ih =>
    rw [Finset.sum_cons]
    exact harm_comb _ (h j) ih
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem exp_of_deriv (f : ℝ → ℂ) (c : ℂ) (hf : ∀ u, HasDerivAt f (c * f u) u) (t : ℝ) :
    f t = Complex.exp (c * t) * f 0 := by
  have h1 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-c * v) * f v) 0 u := fun u => by
    have h2 : HasDerivAt (fun v : ℝ => -c * (v : ℂ)) (-c) u := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).const_mul (-c)
    exact (h2.cexp.fun_mul (hf u)).congr_deriv (by ring)
  have h3 := is_const_of_deriv_eq_zero (fun u => (h1 u).differentiableAt) (fun u => (h1 u).deriv) t 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h3
  rw [← h3, ← mul_assoc, ← Complex.exp_add]
  simp

section
variable (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)

private noncomputable def sc (t : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))

private theorem sc_zero : sc E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := Units.ext (funext fun _ => by simp [expU])
  rw [sc, h, map_one]

private theorem sc_deriv : HasDerivAt (fun t => toL (sc E a t).val) (oneL E a) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp (t : ℂ)) 1 0 := by
    simpa using (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w => ?_
  have e : (fun t : ℝ => toL (sc E a t).val i j w) = fun t : ℝ => Complex.exp (t : ℂ) * oneL E a i j w := by
    funext t
    by_cases h : i = j
    · subst h
      simp [sc, toL, oneL, expU, Matrix.scalar_apply]
    · simp [sc, toL, oneL, Matrix.scalar_apply, h]
  rw [e]
  exact (h1.mul_const _).congr_deriv (one_mul _)

end

theorem UpperTheory.V.Lit.Bor.aInv :
    UpperTheory.V.Lit.Bor.AInv := by
  intro E _ _ _ a φ c hφ t g
  have h := exp_of_deriv (fun u => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) c (fun u => by
    have h1 := hasDerivAt_curve φ (g * GlobalTheory.UnitaryBC.splitCentre E a u) (sc E a) (oneL E a) (sc_zero E a) (sc_deriv E a)
    have h2 : lieD (oneL E a) φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) = c * φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u) :=
      congrArg (fun ψ : Sm E a => ψ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a u)) hφ
    rw [h2] at h1
    have h3 := HasDerivAt.comp_sub_const u u (by rw [sub_self]; exact h1)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    have e := CuspidalL2GL.splitCentre_add (E := E) (a := a) u (x - u)
    rw [add_sub_cancel] at e
    simp only [e, mul_assoc]
    rfl) t
  rw [CuspidalL2GL.splitCentre_comm]
  simpa only [CuspidalL2GL.splitCentre_zero, mul_one] using h
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.oneEig :
    UpperTheory.V.Lit.Bor.OneEig := by
  intro E _ _ _ a π Ξ r hr hC
  obtain ⟨c, hc⟩ := GlobalTheory.CuspRep.Central.lie_scalar π 1
  have hc' : ∀ ψ ∈ π.V, lie E a (oneL E a) ψ = c • ψ := hc
  have h0 : c + (r : ℂ) = 0 := by
    by_contra hne
    refine not_hasCohomology_of_central hne (fun m => ?_) hC
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
    | tmul φ v =>
      have e : π.op (.lie (oneL E a)) φ = c • φ := Subtype.ext (hc' φ.1 φ.2)
      have hr' : Ξ.dmat (oneL E a) = (r : ℂ) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := hr
      rw [tensorLie_tmul, e, hr', Matrix.smul_mulVec, Matrix.one_mulVec, add_smul, TensorProduct.smul_tmul',
        TensorProduct.tmul_smul]
  intro φ hφ
  rw [hc' φ hφ, eq_neg_of_add_eq_zero_left h0]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.xiSchur :
    UpperTheory.V.Lit.Bor.XiSchur := by
  intro E _ _ _ a Ξ
  refine ⟨fun X Y => GlobalTheory.AlgInfChar.dmat_bracket Ξ X Y, fun P hP => ?_⟩
  rcases subsingleton_or_nontrivial (Fin Ξ.d → ℂ) with h | h
  · exact ⟨0, Matrix.ext fun i => congrFun (Subsingleton.elim (α := Fin Ξ.d → ℂ) _ _)⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' P : Module.End ℂ (Fin Ξ.d → ℂ))
  have hs : Stab (eEnd Ξ) (Module.End.eigenspace (Matrix.toLin' P : Module.End ℂ (Fin Ξ.d → ℂ)) c) := by
    intro τ i j w hw
    have hcm : Commute P (eL Ξ.dmat τ i j) := ((hP _).sub_right ((hP _).smul_right _)).smul_right _
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hw ⊢
    rw [eEnd, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hcm.eq, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  have ht := ((algIrr E a Ξ).2 _ hs).resolve_left hc
  refine ⟨c, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩
  have hv : v ∈ Module.End.eigenspace (Matrix.toLin' P : Module.End ℂ (Fin Ξ.d → ℂ)) c := by
    rw [ht]; trivial
  rw [Module.End.mem_eigenspace_iff.1 hv, map_smul, Matrix.toLin'_one]
  rfl
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.derivative_right_translate_L2 :
    UpperTheory.V.Lit.Bor.DerivativeRightTranslateL2 := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ _ φ ψ hφ hψ c hψc hc hc0 hcadd hder
  have hf : Continuous fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2 :=
    (GlobalTheory.AutomorphicL2Unitary.continuous_R hψ.toL2).comp hc
  have hI := hf.integral_hasStrictDerivAt 0 0
  have hE : (fun s : ℝ => (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hφ.toL2) =
      fun t => (∫ s in (0 : ℝ)..t, (GlobalTheory.AutomorphicL2Unitary.R Γ μ (c s)) hψ.toL2) + hφ.toL2 := by
    funext t
    rw [← GlobalTheory.CompanionTheory.TransDeriv.R_sub_eq_integral hφ hψ hψc hc hc0 hcadd hder t]
    abel
  rw [hE]
  have h := hI.hasDerivAt.add_const hφ.toL2
  simpa [hc0] using h
end
