module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.FormTrace
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.FormTraceEq
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.HasTraceDistrOfAdmissible
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.UnitaryKirillovModel.LevelSmulSmul
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.UnipBEqUnipotent
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.MeasuresGL
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.PhiIndep
import GroundTheory.AutomorphicForms.GLnLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle040
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.ContragredientTranspose
  GroundTheory.Automorphic.Whittaker MeasureTheory PositivityTheory.PfBern.Unit

namespace PositivityTheory.RgUd.AB.Pf

section Faith

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsAdmissible ρ)
  {B₀ : Sesq V} (hpos : ∀ v, v ≠ 0 → 0 < (B₀ v v).re)

theorem formD_faithful [ρ.IsIrreducible] (hinv : ∀ g v w, B₀ (ρ g v) (ρ g w) = B₀ v w)
    (Pr : (G → ℂ) →ₗ[ℂ] testFn G) (hPr : ∀ f : testFn G, Pr f = f) (C : Sesq V)
    (h : ∀ f ∈ testFn G, formD μ hρ hpos hinv Pr C f = 0) : C = 0 := by
  refine LinearMap.ext fun v => LinearMap.ext fun u => ?_
  rw [LinearMap.zero_apply, LinearMap.zero_apply]
  by_cases hv0 : v = 0
  · rw [hv0, map_zero, LinearMap.zero_apply]
  by_cases hu0 : u = 0
  · rw [hu0, map_zero]
  have hU : (stabilizerOf ρ v : Set G) ∩ (stabilizerOf ρ u : Set G) ∈ nhds (1 : G) :=
    Filter.inter_mem ((hρ.1 v).mem_nhds (one_mem _)) ((hρ.1 u).mem_nhds (one_mem _))
  obtain ⟨K, hKc, hKU⟩ := exists_openSubgroup_isCompact_subset hU
  have hKo : IsOpen ((K : Subgroup G) : Set G) := K.isOpen
  have := hρ.2 (K : Subgroup G) hKc hKo
  have hvW : v ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).1
  have huW : u ∈ fixedVectors ρ (K : Subgroup G) := by
    rw [mem_fixedVectors]; intro x hx; exact (hKU hx).2
  have hW : fixedVectors ρ (K : Subgroup G) ≠ ⊥ := fun hb => hv0 (by
    have := hvW; rw [hb] at this; exact (Submodule.mem_bot ℂ).1 this)
  set W := fixedVectors ρ (K : Subgroup G)
  let vW : W := ⟨v, hvW⟩
  let uW : W := ⟨u, huW⟩
  let φ : W →ₗ[ℂ] ℂ := (B₀.flip u : V →ₗ[ℂ] ℂ) ∘ₗ W.subtype
  let A : Module.End ℂ W := φ.smulRight vW
  obtain ⟨r, hr⟩ := level_density (μ := μ) hKc hKo hρ.1 hW A
  let rf : locallyConstantCompactSupport G ℂ ℂ := (r : HeckeAlgebra μ)
  have hbi : BiInv (K : Subgroup G) (rf : G → ℂ) := fun κ hκ x => (HeckeAlgebraLevel.val_mem hKc hKo r) κ hκ x
  have hf := h rf rf.2
  rw [formD_apply, hPr rf] at hf
  change DF μ hρ hpos C rf = 0 at hf
  rw [DF_eq μ hρ hpos hinv C _ hKc hKo hbi] at hf
  have hres : ∀ x : W, resA μ hρ (K : Subgroup G) rf x = B₀ x u • v := by
    intro x
    have e := congrArg (fun T : Module.End ℂ W => (T x : V)) hr
    rw [← show ((levelLin hKc hKo ρ r x : W) : V) = resA μ hρ (K : Subgroup G) rf x from rfl, e]
    rfl
  have huu : (B₀ u u) ≠ 0 := fun e => by
    have := hpos u hu0
    rw [e] at this
    simp at this
  set N := rN μ hρ hpos hKc hKo C rf with hN
  have sN := rN_spec μ hρ hpos hKc hKo C rf
  let m : W := (B₀ u u)⁻¹ • N uW
  have hm : ∀ y : W, B₀ (m : V) y = C v y := by
    intro y
    have := sN uW y
    rw [hres] at this
    show B₀ ((B₀ u u)⁻¹ • (N uW : V)) y = C v y
    rw [map_smul, LinearMap.smul_apply, this, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, inv_mul_cancel₀ huu, one_mul]
  have hNe : N = φ.smulRight m := by
    refine riesz_unique hpos sN fun x y => ?_
    show B₀ ((φ x) • (m : V)) y = C (resA μ hρ (K : Subgroup G) rf x) y
    rw [hres, map_smul, LinearMap.smul_apply, hm, map_smul, LinearMap.smul_apply]
    rfl
  unfold DK at hf
  rw [← hN, hNe, LinearMap.trace_smulRight] at hf
  have : φ m = C v u := hm uW
  rw [← this]
  exact hf

end Faith

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem formTraceDistrGL : FormTraceDistrGL k := by
  intro n V _ _ π hadm hirr ⟨B₀, _, h2, h3⟩
  borelize (GL (Fin (n + 1)) k)
  have := hirr
  have := GroundTheory.Automorphic.Measures.isMulRightInvariant_GL k (n + 1) (Measure.haar : Measure (GL (Fin (n + 1)) k))
  obtain ⟨Pr, hPr⟩ := exists_testProj (G := GL (Fin (n + 1)) k)
  exact ⟨formD Measure.haar hadm h2 h3 Pr, fun g B f hf => formD_equiv Measure.haar hadm h2 h3 Pr hPr g B f hf,
    fun B hB => formD_faithful Measure.haar hadm h2 h3 Pr hPr B hB⟩

theorem theoremA_of_thmA (hA : PositivityTheory.RgUd.ThmA k) : TheoremA k := by
  intro n D hD g f hf
  have hf' : f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)) := ⟨hf, Set.subset_univ _⟩
  have hP : ∀ p ∈ GlobalTheory.BZMir.Mir k n, ∀ f ∈ supportedIn (Set.univ : Set (GL (Fin (n + 1)) k)),
      D (fun x => f (p * x * p⁻¹)) = D f := by
    intro p hp f hf
    have := hD p⁻¹ ((GlobalTheory.BZMir.Mir k n).inv_mem hp) f hf.1
    have e : conjFn p⁻¹ f = fun x => f (p * x * p⁻¹) := by
      funext x; unfold conjFn; rw [inv_inv]
    rw [← e]; exact this
  have := hA n D hP g⁻¹ f hf'
  have e : conjFn g f = fun x => f (g⁻¹ * x * g⁻¹⁻¹) := by
    funext x; unfold conjFn; rw [inv_inv]
  rw [e]; exact this

theorem thmB_of_kirillov (hK : KirillovForm k) : PositivityTheory.RgUd.ThmB k := by
  intro n V _ _ π hs hirr B hB β hβ
  have hadm : GroundTheory.Automorphic.IsAdmissible π :=
    (PositivityTheory.rg.gu.whit.isAdmissible_iff π).1 (PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k (n + 1) V π hs hirr)
  obtain ⟨c, hc⟩ := hK n V π B hadm hirr hB.1 hB.2.1 hB.2.2 β hβ
  exact ⟨c, fun v w => by rw [hc]; rfl⟩

theorem thmB (hA : PositivityTheory.RgUd.ThmA k) : PositivityTheory.RgUd.ThmB k :=
  thmB_of_kirillov k (kirillovForm_of_theoremA' k (theoremA_of_thmA k hA) (formTraceDistrGL k))

end PositivityTheory.RgUd.AB.Pf
end
end

section

noncomputable section

open Matrix Topology Filter GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

namespace Near

theorem cj_mul (g h : GL (Fin (n + 1)) k) (x : Mx k n) : cj (g * h) x = cj g (cj h x) := by
  simp only [cj, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem inv_cj (g : GL (Fin (n + 1)) k) (x : Mx k n) :
    ((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n) * cj g x * (g : Mx k n) = x := by
  simp only [cj, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ _ (g : Mx k n)]
  simp [← Units.val_mul, Matrix.mul_assoc]

theorem eventually_conj {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) :
    ∀ᶠ AB : Mx k n × Mx k n in 𝓝 (1, 1), ∀ y ∈ tsupport f, f (AB.1 * y * AB.2) = f y := by
  obtain ⟨hlc, hcs⟩ := hf
  apply hcs.eventually_forall_of_forall_eventually
  intro y _
  have hc : Continuous fun z : (Mx k n × Mx k n) × Mx k n => z.1.1 * z.2 * z.1.2 :=
    ((continuous_fst.fst).matrix_mul continuous_snd).matrix_mul continuous_fst.snd
  have h1 := (hlc.comp_continuous hc).eventually_eq (((1 : Mx k n), (1 : Mx k n)), y)
  have h2 := (hlc.comp_continuous continuous_snd).eventually_eq (((1 : Mx k n), (1 : Mx k n)), y)
  filter_upwards [h1, h2] with z hz1 hz2
  simp only [Function.comp_apply] at hz1 hz2
  rw [hz1, hz2]
  simp

def rE (w : Vc k n) : Mx k n := vecMulVec (eN k n) (w - eN k n)

theorem rE_mul (w : Vc k n) : rE w * rE w = (w (Fin.last n) - 1) • rE w := by
  unfold rE
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hd : (w - eN k n) ⬝ᵥ eN k n = w (Fin.last n) - 1 := by
    simp [eN, dotProduct_single]
  rw [hd]
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

def sw (w : Vc k n) (hw : w (Fin.last n) ≠ 0) : GL (Fin (n + 1)) k :=
  ⟨1 + rE w, 1 - (w (Fin.last n))⁻¹ • rE w, by
    have hc : (w (Fin.last n))⁻¹ * (w (Fin.last n) - 1) = 1 - (w (Fin.last n))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hw, mul_one]
    rw [add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, rE_mul,
      smul_smul, hc, sub_smul, one_smul]
    abel, by
    have hc : (w (Fin.last n))⁻¹ * (w (Fin.last n) - 1) = 1 - (w (Fin.last n))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hw, mul_one]
    rw [sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_one, rE_mul, smul_add, smul_smul, hc,
      sub_smul, one_smul]
    abel⟩

theorem sw_val (w : Vc k n) (hw : w (Fin.last n) ≠ 0) : ((sw w hw : GL (Fin (n + 1)) k) : Mx k n) = 1 + rE w := rfl

theorem sw_last (w : Vc k n) (hw : w (Fin.last n) ≠ 0) (j : Fin (n + 1)) :
    ((sw w hw : GL (Fin (n + 1)) k) : Mx k n) (Fin.last n) j = w j := by
  rw [sw_val]
  by_cases h : j = Fin.last n
  · subst h
    simp [rE, eN, vecMulVec]
  · have h' : Fin.last n ≠ j := fun e => h e.symm
    simp [rE, eN, vecMulVec, Matrix.one_apply, h, h']

end Near

private theorem conj_of_pair_lemma {f : Mx k n → ℂ} (g : GL (Fin (n + 1)) k)
    (h1 : ∀ y ∈ tsupport f, f ((g : Mx k n) * y * ((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n)) = f y)
    (h2 : ∀ y ∈ tsupport f, f (((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n) * y * (g : Mx k n)) = f y) :
    ∀ x, f (cj g x) = f x := by
  intro x
  by_cases hx : x ∈ tsupport f
  · exact h1 x hx
  · have hx0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hx0]
    by_contra hne
    have hy : cj g x ∈ tsupport f := subset_tsupport f hne
    have := h2 _ hy
    rw [Near.inv_cj] at this
    exact hne (this.symm.trans hx0)

private theorem near_lemma_2 {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) :
    ∀ᶠ w : Vc k n in 𝓝 (eN k n), ∀ hw : w (Fin.last n) ≠ 0,
      ∀ x, f (cj (Near.sw w hw)⁻¹ x) = f x := by
  have hr : Continuous (fun w : Vc k n => Near.rE w) := by
    refine continuous_matrix fun i j => ?_
    simp only [Near.rE, vecMulVec_apply]
    exact continuous_const.mul (((continuous_apply j).sub continuous_const))
  have h0 : Near.rE (eN k n) = 0 := by simp [Near.rE]
  have hi : Tendsto (fun w : Vc k n => (w (Fin.last n))⁻¹) (𝓝 (eN k n))
      (𝓝 ((eN k n (Fin.last n))⁻¹)) :=
    ((continuous_apply (Fin.last n)).tendsto _).inv₀ (by simp [eN])
  have hA : Tendsto (fun w : Vc k n => (1 : Mx k n) - (w (Fin.last n))⁻¹ • Near.rE w) (𝓝 (eN k n)) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : Mx k n))).sub (hi.smul (hr.tendsto (eN k n)))
    simpa [h0] using this
  have hB : Tendsto (fun w : Vc k n => (1 : Mx k n) + Near.rE w) (𝓝 (eN k n)) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : Mx k n))).add (hr.tendsto (eN k n))
    simpa [h0] using this
  have hS := Near.eventually_conj hf
  filter_upwards [(hA.prodMk_nhds hB).eventually hS, (hB.prodMk_nhds hA).eventually hS] with w h1 h2 hw
  have eA : (((Near.sw w hw)⁻¹ : GL (Fin (n + 1)) k) : Mx k n) = 1 - (w (Fin.last n))⁻¹ • Near.rE w := rfl
  have eB : (((Near.sw w hw)⁻¹⁻¹ : GL (Fin (n + 1)) k) : Mx k n) = 1 + Near.rE w := by
    rw [inv_inv]; exact Near.sw_val w hw
  apply conj_of_pair_lemma
  · intro y hy
    rw [eA, eB]
    exact h1 y hy
  · intro y hy
    rw [eA, eB]
    exact h2 y hy

open Near in
theorem phiNear : PhiNear k := by
  intro n Λ hΛ f₀ hf₀
  have hne : ∀ᶠ w : Vc k n in 𝓝 (eN k n), w (Fin.last n) ≠ 0 :=
    ((continuous_apply (Fin.last n)).tendsto (eN k n)).eventually_ne (by simp [eN])
  have hev := hne.and (near_lemma_2 hf₀)
  have ht : Tendsto (fun v : Vc k n => eN k n + v) (𝓝 0) (𝓝 (eN k n)) := by
    have hc : Continuous (fun v : Vc k n => eN k n + v) := by fun_prop
    simpa using hc.tendsto (0 : Vc k n)
  have hU := ht.eventually hev
  obtain ⟨t, htU⟩ := exists_box_subset hU
  refine ⟨t, fun s hst => ?_⟩
  funext w
  by_cases hw : w - eN k n ∈ box (Fin (n + 1)) s
  · have hP := htU (hst hw)
    simp only [Set.mem_setOf_eq, add_sub_cancel] at hP
    obtain ⟨hl, hc⟩ := hP
    have hw0 : w ≠ 0 := by
      intro h
      apply hl
      simp [h]
    have hmem : w ∈ {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s} := hw
    rw [Set.indicator_of_mem hmem]
    simp only [phi, if_neg hw0, Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    have hex : ∃ s : GL (Fin (n + 1)) k, ∀ j, (s : Mx k n) (Fin.last n) j = w j :=
      ⟨sw w hl, sw_last w hl⟩
    have hsec : ∀ j, ((sec w : GL (Fin (n + 1)) k) : Mx k n) (Fin.last n) j = w j := by
      simp only [sec, dif_pos hex]
      exact hex.choose_spec
    have hrow : ∀ M : Mx k n, eLast k n ᵥ* M = M (Fin.last n) := by
      intro M
      ext j
      simp [eLast, vecMul, dotProduct, Pi.single_apply]
    set p := sec w * (sw w hl)⁻¹ with hpdef
    have hp : p ∈ Mir k n := by
      show eLast k n ᵥ* ((p : GL (Fin (n + 1)) k) : Mx k n) = eLast k n
      have e1 : eLast k n ᵥ* ((sec w : GL (Fin (n + 1)) k) : Mx k n)
          = eLast k n ᵥ* ((sw w hl : GL (Fin (n + 1)) k) : Mx k n) := by
        rw [hrow, hrow]
        funext j
        rw [hsec j, sw_last w hl j]
      rw [hpdef, Units.val_mul, ← Matrix.vecMul_vecMul, e1, Matrix.vecMul_vecMul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    have hsecp : sec w = p * sw w hl := by simp [hpdef]
    have hfun : (fun x : Mx k n => f₀ (cj (sec w)⁻¹ x)) = f₀ ∘ cj p⁻¹ := by
      funext x
      rw [hsecp, _root_.mul_inv_rev, cj_mul, Function.comp_apply]
      exact hc hl _
    rw [hfun]
    exact hΛ p⁻¹ (inv_mem hp) f₀ hf₀
  · have hmem : w ∉ {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s} := hw
    rw [Set.indicator_of_notMem hmem]
    simp only [phi, Set.indicator_of_notMem hmem, mul_zero]
    split_ifs
    · rfl
    · exact map_zero Λ

end PositivityTheory.RgUd.AB.Pf
end
end

section

noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def pfTrGL {n : ℕ} (h : GL (Fin (n + 1)) k) : GL (Fin (n + 1)) k :=
  ⟨(h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ, ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_pfTrGL {n : ℕ} (h : GL (Fin (n + 1)) k) :
    GeneralLinearGroup.det (pfTrGL h) = GeneralLinearGroup.det h := by
  apply Units.ext
  simp [pfTrGL, GeneralLinearGroup.val_det_apply, det_transpose]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem transpose_mulVec_dotProduct_inv_mulVec {n : ℕ} (h : GL (Fin (n + 1)) k) (x z : Vc k n) :
    ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ x) ⬝ᵥ
        (((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z) = x ⬝ᵥ z := by
  rw [mulVec_transpose, dotProduct_mulVec, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    vecMul_one]

variable (k) in
theorem pfAct : PfAct k := by
  intro mk bs ν hν ψ c hc n F hF h
  funext z
  have key := integral_comp_mulVec_eq_smul ν (pfTrGL h)
    (fun u => F (cj h⁻¹ z.1, u) * ((ψ (u ⬝ᵥ (((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z.2)) : Circle) : ℂ))
  have hv : ((pfTrGL h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ := rfl
  simp only [hv, transpose_mulVec_dotProduct_inv_mulVec, det_pfTrGL] at key
  simp only [GlobalTheory.SplitDict.pf]
  rw [key, Complex.real_smul, Complex.ofReal_inv]

end PositivityTheory.RgUd.AB.Pf
end
end
