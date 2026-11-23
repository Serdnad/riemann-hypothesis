module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

section SlopeTestRemainingChoices

variable {V M : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup M] [NormedSpace ℝ M]

end SlopeTestRemainingChoices

open LineDeriv in
theorem UpperTheory.V.Af.Smo.pftMul :
    UpperTheory.V.Af.Smo.PftMul := by
  unfold UpperTheory.V.Af.Smo.PftMul
  intro V M _ _ _ _ _ _ _ _ G
  have hbd : ∃ C, ∀ (z : V × M), ‖pft (⇑G) z‖ ≤ C := by
    set k : ℕ := Module.finrank ℝ V + 1 with hk
    set C0 : ℝ := 2 ^ k * ((Finset.Iic (k, 0)).sup fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) G with hC0
    have hint : Integrable (fun ξ : V ↦ (1 + ‖ξ‖) ^ (-(k : ℝ))) := by
      apply integrable_one_add_norm
      rw [hk]; push_cast; linarith
    refine ⟨C0 * ∫ ξ : V, (1 + ‖ξ‖) ^ (-(k : ℝ)), fun z ↦ ?_⟩
    have hpt : ∀ ξ : V, ‖G (ξ, z.2)‖ ≤ C0 * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
      intro ξ
      have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (le_refl k) (le_refl 0) G (ξ, z.2)
      rw [norm_iteratedFDeriv_zero] at h
      have hpos : 0 < 1 + ‖ξ‖ := by positivity
      have hn : ‖ξ‖ ≤ ‖((ξ, z.2) : V × M)‖ := norm_fst_le ((ξ, z.2) : V × M)
      have hle : (1 + ‖ξ‖) ^ k ≤ (1 + ‖((ξ, z.2) : V × M)‖) ^ k := by
        gcongr
      rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ‖G (ξ, z.2)‖ * (1 + ‖ξ‖) ^ k ≤ (1 + ‖((ξ, z.2) : V × M)‖) ^ k * ‖G (ξ, z.2)‖ := by
            rw [mul_comm]; gcongr
        _ ≤ C0 := h
    calc ‖pft (⇑G) z‖ = ‖∫ ξ : V, 𝐞 (-⟪ξ, z.1⟫) • G (ξ, z.2)‖ := by
          simp only [pft, Real.fourier_eq]
      _ ≤ ∫ ξ : V, ‖𝐞 (-⟪ξ, z.1⟫) • G (ξ, z.2)‖ := norm_integral_le_integral_norm _
      _ = ∫ ξ : V, ‖G (ξ, z.2)‖ := by simp [Circle.norm_smul]
      _ ≤ ∫ ξ : V, C0 * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) (hint.const_mul C0)
          exact Filter.Eventually.of_forall hpt
      _ = C0 * ∫ ξ : V, (1 + ‖ξ‖) ^ (-(k : ℝ)) := integral_const_mul _ _
  refine ⟨hbd, fun l ↦ ?_⟩
  set l1 : V →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ V M) with hl1
  set w : V := (InnerProductSpace.toDual ℝ V).symm l1 with hw
  have hwl : ∀ ξ : V, ⟪ξ, w⟫ = l1 ξ := by
    intro ξ
    rw [real_inner_comm, hw, InnerProductSpace.toDual_symm_apply]
  set L2 : V × M →L[ℝ] ℂ := Complex.ofRealCLM.comp
    (l.comp ((ContinuousLinearMap.inr ℝ V M).comp (ContinuousLinearMap.snd ℝ V M))) with hL2
  have hL2t : Function.HasTemperateGrowth (⇑L2) := L2.hasTemperateGrowth
  set c : ℂ := (2 * (Real.pi : ℂ) * Complex.I)⁻¹ with hc
  refine ⟨c • LineDeriv.lineDerivOp ((w, (0 : M)) : V × M) G + SchwartzMap.smulLeftCLM ℂ (⇑L2) G, ?_⟩
  funext z
  obtain ⟨v, m⟩ := z
  have hg : Function.HasTemperateGrowth (fun ξ : V => (ξ, m)) := by
    have h1 : Function.HasTemperateGrowth (fun ξ : V => ((ContinuousLinearMap.inl ℝ V M) ξ + ((0 : V), m))) :=
      (ContinuousLinearMap.inl ℝ V M).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    convert h1 using 2 with ξ
    simp
  have hgu : ∃ (k : ℕ) (C : ℝ), ∀ ξ : V, ‖ξ‖ ≤ C * (1 + ‖((ξ, m) : V × M)‖) ^ k := by
    refine ⟨1, 1, fun ξ ↦ ?_⟩
    have hn : ‖ξ‖ ≤ ‖((ξ, m) : V × M)‖ := norm_fst_le ((ξ, m) : V × M)
    simp only [pow_one, one_mul]
    linarith
  set S : 𝓢(V, ℂ) := SchwartzMap.compCLM ℝ hg hgu G with hS
  have hSa : ∀ ξ, S ξ = G (ξ, m) := fun ξ ↦ by
    rw [hS, SchwartzMap.compCLM_apply]; rfl
  have hder : ∀ ξ : V, fderiv ℝ (⇑S) ξ w = fderiv ℝ (⇑G) (ξ, m) (w, 0) := by
    intro ξ
    have hgd : HasFDerivAt (fun η : V => ((η, m) : V × M)) ((ContinuousLinearMap.id ℝ V).prod 0) ξ :=
      (hasFDerivAt_id ξ).prodMk (hasFDerivAt_const m ξ)
    have hGd : HasFDerivAt (⇑G) (fderiv ℝ (⇑G) (ξ, m)) (ξ, m) := (G.differentiableAt).hasFDerivAt
    have hc' := hGd.comp ξ hgd
    have hSf : (⇑S) = (⇑G) ∘ (fun η : V => ((η, m) : V × M)) := by
      funext η; exact hSa η
    rw [hSf, hc'.fderiv]
    simp
  have key : (fun ξ : V => (c • LineDeriv.lineDerivOp ((w, (0 : M)) : V × M) G + SchwartzMap.smulLeftCLM ℂ (⇑L2) G) (ξ, m))
      = ⇑(c • LineDeriv.lineDerivOp w S + ((l (0, m) : ℝ) : ℂ) • S) := by
    funext ξ
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL2t,
      SchwartzMap.lineDerivOp_apply_eq_fderiv, hder, hSa]
    simp [hL2, smul_eq_mul]
  simp only [pft]
  rw [key, ← SchwartzMap.fourier_coe]
  simp only [FourierTransform.fourier_add, FourierTransform.fourier_smul, SchwartzMap.fourier_lineDerivOp_eq]
  have hSf' : (fun ξ : V => G (ξ, m)) = ⇑S := by
    funext ξ; exact (hSa ξ).symm
  have hit : Function.HasTemperateGrowth (fun x : V ↦ ⟪x, w⟫) := ((innerSL ℝ).flip w).hasTemperateGrowth
  rw [hSf', ← SchwartzMap.fourier_coe]
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hit]
  simp only [hwl]
  have hlv : l (v, m) = l1 v + l (0, m) := by
    rw [hl1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, ← map_add (f := _)]
    simp
  rw [hlv, hc]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [smul_eq_mul, Complex.real_smul]
  field_simp
  push_cast
  ring
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem isY_map {R T : Type} [CommRing R] [CommRing T] {n m : ℕ} (φ : R →+* T) {p : GL (Fin n) R}
    (h : IsY m p.val) : IsY m (GeneralLinearGroup.map φ p).val := fun i hi =>
  ⟨by change φ (p.val i i) = 1; rw [(h i hi).1, map_one],
    fun j hj => by change φ (p.val i j) = 0; rw [(h i hi).2 j hj, map_zero]⟩

private theorem isY_one {R : Type} [CommRing R] {n m : ℕ} : IsY m (1 : GL (Fin n) R).val := fun i _ =>
  ⟨by simp, fun j hj => by simp [Matrix.one_apply_ne hj.ne']⟩

private theorem isY_mul {R : Type} [CommRing R] {n m : ℕ} {p q : GL (Fin n) R}
    (hp : IsY m p.val) (hq : IsY m q.val) : IsY m (p * q).val := by
  intro i hi
  have key : ∀ j, j ≤ i → (p * q).val i j = q.val i j := by
    intro j hj
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, (hp i hi).1, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hp i hi).2 k h, zero_mul]
      · rw [(hq k (hi.trans h.le)).2 j (hj.trans_lt h), mul_zero]
    · simp
  exact ⟨by rw [key i le_rfl, (hq i hi).1], fun j hj => by rw [key j hj.le, (hq i hi).2 j hj]⟩

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem exists_part (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (Af E)) :
    ∃ s : GL (Fin n) (Af E), SuppIn S s ∧ ∀ w ∈ S, cmp w s = cmp w g := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun w _ => map_one _, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert v S hv ih =>
    obtain ⟨s, h1, h2⟩ := ih
    refine ⟨s * locGL E n v (cmp v g), fun w hw => ?_, fun w hw => ?_⟩
    · rw [Finset.mem_insert, not_or] at hw
      rw [map_mul, h1 w hw.2, one_mul]
      exact GlobalTheory.CuspRep.pLoc_locGL_of_ne hw.1 _
    · rw [map_mul]
      rcases Finset.mem_insert.1 hw with rfl | h
      · rw [h1 w hv, one_mul]
        exact GlobalTheory.CuspRep.pLoc_locGL _ _
      · rw [h2 w h, show cmp w (locGL E n v (cmp v g)) = 1 from
          GlobalTheory.CuspRep.pLoc_locGL_of_ne (fun e : w = v => hv (e ▸ h)) _, mul_one]

private theorem af_ext {x y : Af E} (h : ∀ w, pLoc E w x = pLoc E w y) : x = y :=
  DFunLike.ext _ _ h

private theorem isY_af {m : ℕ} {s : GL (Fin n) (Af E)} (h : ∀ w, IsY m (cmp w s).val) : IsY m s.val := fun i hi =>
  ⟨af_ext fun w => by rw [map_one]; exact (h w i hi).1,
    fun j hj => af_ext fun w => by rw [map_zero]; exact (h w i hi).2 j hj⟩

private theorem pFin_finGL (k : GL (Fin n) (Af E)) : GeneralLinearGroup.map (pFin E) (finGL E n k) = k := by
  rw [finGL, GlobalTheory.CuspRep.map_cornerGL_of_hom _ _ (RingHom.id _) fun x => rfl]
  rfl

variable [IsTotallyReal E]

private theorem isY_ad {m : ℕ} {g : GA E n} (h1 : IsY m (GeneralLinearGroup.map (pInf E) g).val)
    (h2 : IsY m (GeneralLinearGroup.map (pFin E) g).val) : IsY m g.val := fun i hi =>
  ⟨TR.ad_ext (by rw [map_one]; exact (h1 i hi).1) (by rw [map_one]; exact (h2 i hi).1),
    fun j hj => TR.ad_ext (by rw [map_zero]; exact (h1 i hi).2 j hj) (by rw [map_zero]; exact (h2 i hi).2 j hj)⟩

private theorem exists_dec (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E n)
    (h1 : IsY (n - 1) (GeneralLinearGroup.map (pInf E) g).val)
    (h2 : ∀ w ∈ S, IsY (n - 1) (cmp w (GeneralLinearGroup.map (pFin E) g)).val) :
    ∃ p k, InPS S p ∧ Away S k ∧ g = p * finGL E n k := by
  obtain ⟨s, hs, hg⟩ := exists_part S (GeneralLinearGroup.map (pFin E) g)
  have e : GeneralLinearGroup.map (pFin E) (infGL E n (GeneralLinearGroup.map (pInf E) g) * finGL E n s) = s := by
    rw [map_mul, TR.pFin_infGL, pFin_finGL, one_mul]
  refine ⟨infGL E n (GeneralLinearGroup.map (pInf E) g) * finGL E n s, s⁻¹ * GeneralLinearGroup.map (pFin E) g,
    ⟨isY_ad ?_ ?_, ?_⟩, fun w hw => ?_, ?_⟩
  · rw [map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one]
    exact h1
  · rw [e]
    refine isY_af fun w => ?_
    by_cases hw : w ∈ S
    · rw [hg w hw]; exact h2 w hw
    · rw [hs w hw]; exact isY_one
  · rw [e]; exact hs
  · rw [map_mul, map_inv, hg w hw, inv_mul_cancel]
  · rw [mul_assoc, ← map_mul, mul_inv_cancel_left, TR.infGL_mul_finGL]

end

theorem UpperTheory.V.Af.Smo.vanish :
    UpperTheory.V.Af.Smo.SphAll → UpperTheory.V.Af.Smo.InjP → UpperTheory.V.Af.Smo.DenseAway → UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.Smo.EigMap → UpperTheory.V.Af.Smo.Vanish := by
  intro hSA hI hD hWB hEM E _ _ _ n hn S B f hf hS hK h0
  have hW : ∀ p, InPS S p → ∀ k, Away S k → whittaker f (p * finGL E n k) = 0 := fun p hp =>
    hSA E n S B (whittaker f) (hWB E n f hf).2.2
      (fun w hw => ⟨(hS w hw).1, (hEM E n w (B w) f (hS w hw).2).1 hf⟩)
      (fun g k hk => by
        unfold whittaker
        simp only [← mul_assoc, hK _ k hk]) p hp.2 (h0 p hp)
  have hX := hI E n hn f hf {g | IsY (n - 1) (GeneralLinearGroup.map (pInf E) g).val ∧
      ∀ w ∈ S, IsY (n - 1) (cmp w (GeneralLinearGroup.map (pFin E) g)).val}
    (fun γ hγ g hg => by
      have h : IsY (n - 1) (ratGL E n γ).val := isY_map _ hγ
      refine ⟨?_, fun w hw => ?_⟩
      · rw [map_mul]; exact isY_mul (isY_map _ h) hg.1
      · rw [map_mul, map_mul]; exact isY_mul (isY_map _ (isY_map _ h)) (hg.2 w hw))
    (fun g hg => by
      obtain ⟨p, k, hp, hk, rfl⟩ := exists_dec S g hg.1 hg.2
      exact hW p hp k hk)
  refine Continuous.ext_on (hD E n S) hf.cont continuous_const ?_
  rintro _ ⟨γ, k, hk, rfl⟩
  have h : f (finGL E n k) = 0 := hX _ ⟨by rw [TR.pInf_finGL]; exact isY_one, fun w hw => by
    rw [pFin_finGL, hk w hw]; exact isY_one⟩
  exact (hf.left γ _).trans h
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.avgChar :
    UpperTheory.V.Af.Smo.AvgChar := by
  intro A _ L₀ L _ hidx
  classical
  let H : AddSubgroup L := L₀.addSubgroupOf L
  haveI : Fintype (L ⧸ H) := AddSubgroup.fintypeOfIndexNeZero hidx
  let r : L ⧸ H → A := fun q => ((Quotient.out q : L) : A)
  have hr : Function.Injective r := Subtype.coe_injective.comp Quotient.out_injective
  refine ⟨Finset.univ.image r, Finset.univ_nonempty.image r, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact (Quotient.out q).2
  · intro χ hχ ⟨x, hxL, hx⟩
    have hχeq : ∀ a b : L, (a : L ⧸ H) = b → χ a = χ b := by
      intro a b hab
      have hm : -a + b ∈ H := QuotientAddGroup.eq.mp hab
      have hm' : ((-a + b : L) : A) ∈ L₀ := AddSubgroup.mem_addSubgroupOf.mp hm
      have h1 : χ ((-a + b : L) : A) = 1 := hχ _ hm'
      have h2 : (b : A) = a + ((-a + b : L) : A) := by simp
      rw [h2, AddChar.map_add_eq_mul, h1, mul_one]
    rw [Finset.sum_image (fun q _ q' _ h => hr h)]
    let xL : L := ⟨x, hxL⟩
    have hshift : ∀ q : L ⧸ H, χ (r (q + (xL : L ⧸ H))) = χ (r q) * χ x := by
      intro q
      have h3 : ((Quotient.out (q + (xL : L ⧸ H)) : L) : L ⧸ H) = ((Quotient.out q + xL : L) : L ⧸ H) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
      have h4 := hχeq _ _ h3
      simp only [r]
      rw [h4, AddSubgroup.coe_add, AddChar.map_add_eq_mul]
    have hS : ∑ q : L ⧸ H, χ (r q) = (∑ q : L ⧸ H, χ (r q)) * χ x := by
      calc ∑ q : L ⧸ H, χ (r q) = ∑ q : L ⧸ H, χ (r (q + (xL : L ⧸ H))) :=
            (Equiv.sum_comp (Equiv.addRight (xL : L ⧸ H)) (fun q => χ (r q))).symm
        _ = ∑ q : L ⧸ H, χ (r q) * χ x := Finset.sum_congr rfl (fun q _ => hshift q)
        _ = (∑ q : L ⧸ H, χ (r q)) * χ x := (Finset.sum_mul _ _ _).symm
    have h5 : (∑ q : L ⧸ H, χ (r q)) * (χ x - 1) = 0 := by
      rw [mul_sub, mul_one, ← hS, sub_self]
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact h6
    · exact absurd (sub_eq_zero.mp h6) hx
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.convCont :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.ConvCont := by
  intro hc E _ _ _ n f hf hb α
  obtain ⟨C, hC⟩ := hb
  obtain ⟨h1, h2⟩ := hc E n f hf
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hch : ∀ g x, ‖chart f g x‖ ≤ C := by
    intro g x
    unfold UpperTheory.V.TR.chart
    split_ifs
    · exact hC _
    · simpa using hC0
  have hbd : ∀ g x, ‖chart f g x * α x‖ ≤ C * ‖α x‖ := by
    intro g x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hch g x) (norm_nonneg _)
  haveI i1 : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hint : Integrable (fun x => C * ‖α x‖) := (α.integrable.norm).const_mul C
  haveI : FirstCountableTopology (GA E n) :=
    GroundTheory.Automorphic.FourierWhittaker.firstCountableTopology_adelicGL ..
  refine ⟨?_, ∫ x, C * ‖α x‖, fun g => ?_⟩
  · unfold conv
    refine continuous_of_dominated (bound := fun x => C * ‖α x‖) (fun g => ?_) (fun g => ?_) hint ?_
    · exact ((h2 g).mul α.continuous.measurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hbd g)
    · refine Filter.Eventually.of_forall fun x => ?_
      refine Continuous.mul ?_ continuous_const
      by_cases hx : x ∈ invSet E n
      · exact h1.comp_continuous (f := fun g : GA E n => (g, x)) (by fun_prop) fun g => ⟨Set.mem_univ _, hx⟩
      · have : (fun g => chart f g x) = fun _ => 0 := by
          funext g
          unfold UpperTheory.V.TR.chart
          exact dif_neg hx
        rw [this]
        exact continuous_const
  · exact norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall (hbd g))
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem linearMap_comp_eq_on_smul_of_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (A B : V →L[ℝ] V)
    (h1 : ∀ x, B (A x) = x) (h2 : ∀ x, A (B x) = x) (f : V → ℂ) :
    ∫ x, f (A x) ∂μ = ((|(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| : ℝ) : ℂ) * ∫ x, f x ∂μ := by
  let e : V ≃L[ℝ] V := ContinuousLinearEquiv.equivOfInverse A B h1 h2
  have hd : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 := (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hm : MeasurableEmbedding (A : V →ₗ[ℝ] V) := e.toHomeomorph.measurableEmbedding
  have := hm.integral_map (μ := μ) f
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hd, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _)] at this
  rw [← Complex.real_smul, this]
  rfl

theorem UpperTheory.V.Af.Smo.linChange :
    UpperTheory.V.Af.Smo.LinChange := by
  intro E _ _ n
  refine ⟨fun s => ((|(LinearMap.det (lmul (toL s.val) : Lie E n →ₗ[ℝ] Lie E n))⁻¹| : ℝ) : ℂ), ?_, fun s f => ?_⟩
  · have : (lmul (toL (1 : GL (Fin n) (Rinf E)).val) : Lie E n →ₗ[ℝ] Lie E n) = LinearMap.id :=
      LinearMap.ext fun x => one_mul (Matrix.of x)
    simp only [this]
    simp
  · haveI : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance
    haveI : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    exact linearMap_comp_eq_on_smul_of_eq volume (lmul (toL s.val)) (lmul (toL (s⁻¹).val))
      (fun x => s.inv_mul_cancel_left (Matrix.of x)) (fun x => s.mul_inv_cancel_left (Matrix.of x)) f
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.convFub :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.ConvFub := by
  classical
  intro hc E _ _ _ n f hf ⟨C, hC⟩ α X _ _ _ _ ν _ u a hu ha ⟨D, hD⟩ g
  have hS : MeasurableSet ((Set.univ : Set X) ×ˢ invSet E n) :=
    (isOpen_univ.prod TR.isOpen_invSet).measurableSet
  have h1 : ContinuousOn (fun z : X × Lie E n => chart f (u z.1 * g) z.2) (Set.univ ×ˢ invSet E n) :=
    (hc E n f hf).1.comp (f := fun z : X × Lie E n => (u z.1 * g, z.2))
      (((hu.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
      fun z hz => ⟨trivial, hz.2⟩
  have h2 : Measurable fun z : X × Lie E n => chart f (u z.1 * g) z.2 := by
    have := h1.measurable_piecewise (g := fun _ => 0) continuousOn_const hS
    convert this using 1
    funext z
    by_cases hz : z ∈ (Set.univ : Set X) ×ˢ invSet E n
    · rw [Set.piecewise_eq_of_mem _ _ _ hz]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz, chart]
      exact dif_neg fun h => hz ⟨trivial, h⟩
  have hb : ∀ g y, ‖chart f g y‖ ≤ C := fun g y => by
    unfold chart
    split_ifs
    · exact hC _
    · simpa using (norm_nonneg _).trans (hC 1)
  haveI : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hα : Integrable (fun y => α y) (volume : Measure (Lie E n)) := α.integrable
  have ha' : Integrable a ν := Integrable.of_bound ha.measurable.aestronglyMeasurable D (.of_forall hD)
  have hi : Integrable (fun z : X × Lie E n => chart f (u z.1 * g) z.2 * (a z.1 * α z.2)) (ν.prod volume) :=
    (ha'.mul_prod hα).bdd_mul h2.aestronglyMeasurable (.of_forall fun z => hb _ _)
  calc ∫ x, conv f α (u x * g) * a x ∂ν
      = ∫ x, (∫ y, chart f (u x * g) y * (a x * α y)) ∂ν := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [conv]
        rw [← integral_mul_const]
        exact integral_congr_ae (.of_forall fun y => by ring)
    _ = ∫ y, ∫ x, chart f (u x * g) y * (a x * α y) ∂ν := integral_integral_swap hi
    _ = _ := by
        unfold conv
        refine integral_congr_ae (.of_forall fun y => ?_)
        simp only [chart]
        split_ifs with h
        · rw [← integral_mul_const]
          exact integral_congr_ae (.of_forall fun x => by simp only [mul_assoc])
        · simp
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem corner_isY {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (m : ℕ) (s : R →ₙ+* S) (y : GL (Fin n) R)
    (h : IsY m y.val) :
    IsY m (GlobalTheory.CuspRep.cornerGL n s y).val ∧ supN (GlobalTheory.CuspRep.cornerGL n s y).val = s (supN y.val) := by
  have e : ∀ i j, (GlobalTheory.CuspRep.cornerGL n s y).val i j =
      (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s (y.val i j) := fun _ _ => rfl
  refine ⟨fun i hi => ⟨?_, fun j hj => ?_⟩, ?_⟩
  · rw [e, (h i hi).1]; simp
  · rw [e, (h i hi).2 j hj, Matrix.one_apply_ne hj.ne', Matrix.one_apply_ne hj.ne']; simp
  · unfold supN

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · have hne : i ≠ j := fun h' => by subst h'; omega
      rw [e, Matrix.one_apply_ne hne, Matrix.one_apply_ne hne]; simp
    · simp

theorem UpperTheory.V.Af.Smo.embY :
    UpperTheory.V.Af.Smo.EmbY := by
  intro E _ _ _ n m
  exact ⟨fun w y h => corner_isY m (sLoc E w) y h, fun y h => corner_isY m (sFin E) y h,
    fun y h => corner_isY m (sInf E) y h, fun w => GlobalTheory.CuspRep.CuspSub.continuous_locGL w⟩
end
