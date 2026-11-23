module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.OrthZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum

@[expose] public section

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE

private theorem weight_ex : ∃ w : ℝ → ℝ, Continuous w ∧ HasCompactSupport w ∧ (∀ s, 0 ≤ w s) ∧
    (∀ s ∈ Set.Ioo (-1 : ℝ) 1, w s ≠ 0) ∧ ∫ s, w s = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, b.continuous_normed, b.hasCompactSupport_normed, b.nonneg_normed, ?_,
    b.integral_normed⟩
  intro s hs
  have h : s ∈ Function.support (b.normed volume) := by
    rw [b.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.2 hs
  exact h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def slabSp (D : Dom E n 0) : Submodule ℂ (GA E n → ℂ) where
  carrier := {f | Slab D f}
  zero_mem' := ⟨continuous_const, fun _ _ => rfl, fun _ _ => rfl, fun u _ _ => by
    simp only [Pi.zero_apply, zero_mul]
    exact MemLp.zero⟩
  add_mem' := by
    rintro a b ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩
    refine ⟨a1.add b1, fun γ g => ?_, fun t g => ?_, fun u hu hc => ?_⟩
    · simp only [Pi.add_apply, a2, b2]
    · simp only [Pi.add_apply, a3, b3]
    · have h := (a4 u hu hc).add (b4 u hu hc)
      refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).1 h
      simp only [Pi.add_apply, add_mul]
  smul_mem' := by
    rintro c a ⟨a1, a2, a3, a4⟩
    refine ⟨a1.const_smul c, fun γ g => ?_, fun t g => ?_, fun u hu hc => ?_⟩
    · simp only [Pi.smul_apply, a2]
    · simp only [Pi.smul_apply, a3]
    · have h := (a4 u hu hc).const_smul c
      refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).1 h
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem zero_of_ae (hB : Basic) (hA : AeEq) (hn : 1 ≤ n) (D : Dom E n 0) {f : GA E n → ℂ} (hf : Slab D f)
    (h : ∀ᵐ x ∂D.ν, ldet x ∈ Set.Ioo (-1 : ℝ) 1 → f x.1 = 0) : f = 0 := by
  obtain ⟨hl, hm, -⟩ := hB E n hn
  have hinv : Inv (fun x : H E n 0 => f x.1) := by
    rintro ⟨_, ⟨p, q⟩, rfl⟩ x
    exact hf.2.1 p x.1
  have key := hA E n D (fun x => f x.1) (fun _ => 0) _ (hf.1.comp continuous_fst) continuous_const hinv
    (fun _ _ => rfl) isOpen_Ioo h
  funext g
  have h0 : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1)) ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [hm, hl, neg_add_cancel]
    constructor <;> norm_num
  exact (hf.2.2.1 _ g).symm.trans (key _ h0)

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.FE in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.formEx_pf :
    Basic → AeEq → WtInd → FormEx := by
  intro hB hA hW E _ _ _ n hn D
  obtain ⟨w, wc, ws, w0, wp, w1⟩ := weight_ex
  have uc : Continuous fun s => (w s : ℂ) := Complex.continuous_ofReal.comp wc
  have us : HasCompactSupport fun s => (w s : ℂ) := ws.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have u1 : ∫ s, (w s : ℂ) = 1 := by rw [integral_complex_ofReal, w1, Complex.ofReal_one]
  have hI : ∀ a b : slabSp D, Integrable
      (fun x : H E n 0 => starRingEnd ℂ (a.1 x.1) * b.1 x.1 * (w (ldet x) : ℂ)) D.ν :=
    fun a b => (hW E n hn D a.1 b.1 a.2 b.2 _ uc us).1
  let B : slabSp D →ₗ⋆[ℂ] slabSp D →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun a b => prW D (fun s => (w s : ℂ)) a.1 b.1)
      (fun a a' b => by
        simp only [prW]
        rw [← integral_add (hI a b) (hI a' b)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
        ring)
      (fun c a b => by
        simp only [prW, smul_eq_mul]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
        ring)
      (fun a b b' => by
        simp only [prW]
        rw [← integral_add (hI a b) (hI a b')]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_add, Pi.add_apply]
        ring)
      (fun c a b => by
        simp only [prW, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
        ring)
  have hBv : ∀ a b, B a b = prW D (fun s => (w s : ℂ)) a.1 b.1 := fun _ _ => rfl
  refine ⟨slabSp D, B, fun _ => Iff.rfl, fun a b => ?_, fun a ha => ?_, fun a b u hu hc => ?_, fun g hg a => ⟨?_, ?_⟩⟩
  · rw [hBv, hBv, prW, prW, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  · have he : ∀ x : H E n 0, starRingEnd ℂ (a.1 x.1) * a.1 x.1 * (w (ldet x) : ℂ) =
        ((Complex.normSq (a.1 x.1) * w (ldet x) : ℝ) : ℂ) := fun x => by
      rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    have hi : Integrable (fun x : H E n 0 => Complex.normSq (a.1 x.1) * w (ldet x)) D.ν := by
      have h := (hI a a).re
      simp only [he, RCLike.re_to_complex, Complex.ofReal_re] at h
      exact h
    have hnn : 0 ≤ fun x : H E n 0 => Complex.normSq (a.1 x.1) * w (ldet x) :=
      fun x => mul_nonneg (Complex.normSq_nonneg _) (w0 _)
    rw [hBv, prW]
    simp only [he]
    rw [integral_complex_ofReal, Complex.ofReal_re]
    refine lt_of_le_of_ne (integral_nonneg hnn) fun h0 => ha (Subtype.ext ?_)
    refine zero_of_ae hB hA hn D a.2 ?_
    filter_upwards [(integral_eq_zero_iff_of_nonneg hnn hi).1 h0.symm] with x hx hI'
    exact Complex.normSq_eq_zero.1 ((mul_eq_zero.1 hx).resolve_right (wp _ hI'))
  · exact (hW E n hn D a.1 b.1 a.2 b.2 u hu hc).2.1 _ uc us u1
  · exact ((hW E n hn D a.1 a.1 a.2 a.2 _ uc us).2.2 g hg).1
  · intro a' b b' h1 h2
    rw [hBv, hBv, funext h1, funext h2]
    exact ((hW E n hn D a.1 b.1 a.2 b.2 _ uc us).2.2 g hg).2
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.OZ

private def bump (s : ℝ) : ℂ := ((max 0 (min 1 (2 - |s|)) : ℝ) : ℂ)

private theorem bump_cont : Continuous bump := by
  unfold bump
  fun_prop

private theorem bump_supp : HasCompactSupport bump := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun s hs => ?_
  have h : 2 < |s| := by
    by_contra hc
    exact hs (abs_le.1 (not_lt.1 hc))
  have h1 : min 1 (2 - |s|) ≤ 0 := (min_le_right _ _).trans (by linarith)
  simp [bump, max_eq_left h1]

private theorem bump_one {s : ℝ} (h : s ∈ Set.Ioo (-1 : ℝ) 1) : bump s = 1 := by
  have h1 : |s| < 1 := abs_lt.2 h
  have h2 : min 1 (2 - |s|) = 1 := min_eq_left (by linarith)
  simp [bump, h2]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.OZ

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.OZ in
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.orthZero_pf :
    Basic → AeEq → WtInd → OrthZero := by
  intro hB hA _ E _ _ _ n hn D π _ f hf hS ho
  obtain ⟨hl, hmul, -⟩ := hB E n hn
  obtain ⟨hfc, hfr, hfs, -⟩ := hf
  obtain ⟨v, hv, hve⟩ := hS bump bump_cont bump_supp
  have horth : v ∈ (piSp D π Unit)ᗮ := by
    rw [piSp, Submodule.orthogonal_closure, Submodule.mem_orthogonal]
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨ψ, hψ, u, hu, hus, he⟩ := hg ()
      have hz := ho ψ hψ (fun s => starRingEnd ℂ (u s) * bump s)
        ((Complex.continuous_conj.comp hu).mul bump_cont)
        ((hus.comp_left (g := starRingEnd ℂ) (map_zero _)).mul_right)
      rw [PiLp.inner_apply]
      simp only [Finset.univ_unique, Finset.sum_singleton]
      rw [L2.inner_def]
      rw [← hz, prW]
      refine integral_congr_ae ?_
      filter_upwards [he, hve] with x h1 h2
      simp only [PUnit.default_eq_unit]
      rw [h1, h2]
      simp only [RCLike.inner_apply, map_mul]
      ring
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul r x _ hx => rw [inner_smul_left, hx, mul_zero]
  have hv0 : v = 0 := inner_self_eq_zero.1
    ((Submodule.mem_orthogonal _ _).1 horth v hv)
  have hlat : ∀ x : H E n 0, ldet x ∈ Set.Ioo (-1 : ℝ) 1 → f x.1 = 0 := by
    refine hA E n D (fun x => f x.1) (fun _ => 0) (Set.Ioo (-1 : ℝ) 1) (hfc.comp continuous_fst)
      continuous_const ?_ (fun _ _ => rfl) isOpen_Ioo ?_
    · intro γ x
      obtain ⟨⟨a, b⟩, hab⟩ := γ.2
      have h1 : (γ : H E n 0).1 = ratGL E n a := by rw [← hab]; rfl
      show f ((γ : H E n 0).1 * x.1) = f x.1
      rw [h1, hfr]
    · have hz : ((v () : Lp ℂ 2 D.ν) : H E n 0 → ℂ) =ᵐ[D.ν] 0 := by
        rw [hv0]
        exact Lp.coeFn_zero _ _ _
      filter_upwards [hve, hz] with x h1 h2 h3
      rw [h2] at h1
      simpa [bump_one h3] using h1.symm
  funext g
  have hx := hlat (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1)) (by
    rw [hmul, hl]; simp)
  have : (ac E n (-ldet ((g, 1) : H E n 0)) * (g, 1) : H E n 0).1 =
      splitCentre E n (-ldet ((g, 1) : H E n 0) / (n * Module.finrank ℚ E)) * g := rfl
  rw [this, hfs] at hx
  exact hx
end

section

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB

private lemma exists_projL {F : Type} [AddCommGroup F] [Module ℂ F] (B : F →ₗ⋆[ℂ] F →ₗ[ℂ] ℂ)
    (hsym : ∀ a b, starRingEnd ℂ (B a b) = B b a) (hpos : ∀ a, a ≠ 0 → 0 < (B a a).re)
    (S : Submodule ℂ F) [FiniteDimensional ℂ S] :
    ∃ P : F →ₗ[ℂ] F, (∀ x, P x ∈ S) ∧ ∀ x, ∀ a ∈ S, B a (x - P x) = 0 := by
  let core : InnerProductSpace.Core ℂ F :=
    { inner := fun a b => B a b
      conj_inner_symm := fun a b => hsym b a
      re_inner_nonneg := fun a => by
        by_cases h : a = 0
        · simp [h]
        · exact (hpos a h).le
      add_left := fun a b c => by simp
      smul_left := fun a b r => by simp
      definite := fun a h => by
        by_contra h0
        have h1 := hpos a h0
        have h2 : B a a = 0 := h
        simp [h2] at h1 }
  letI : NormedAddCommGroup F := core.toNormedAddCommGroup
  letI : InnerProductSpace ℂ F := InnerProductSpace.ofCore core.toCore
  haveI : CompleteSpace S := FiniteDimensional.complete ℂ S
  refine ⟨S.starProjection.toLinearMap, fun x => S.starProjection_apply_mem x, fun x a ha => ?_⟩
  have h0 := S.starProjection_inner_eq_zero x a ha
  have h1 : B (x - S.starProjection x) a = 0 := h0
  have h2 := hsym (x - S.starProjection x) a
  rw [h1, map_zero] at h2
  exact h2.symm

private lemma orbit_stable {Γ F : Type} [Group Γ] [AddCommGroup F] [Module ℂ F]
    (R : Representation ℂ Γ F) (x : F) (g : Γ) :
    ∀ a ∈ Submodule.span ℂ (Set.range fun k => R k x),
      R g a ∈ Submodule.span ℂ (Set.range fun k => R k x) := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨k, rfl⟩ := h
    refine Submodule.subset_span ⟨g * k, ?_⟩
    simp [map_mul, Module.End.mul_apply]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

private lemma self_mem_orbit {Γ F : Type} [Group Γ] [AddCommGroup F] [Module ℂ F]
    (R : Representation ℂ Γ F) (x : F) : x ∈ Submodule.span ℂ (Set.range fun k => R k x) :=
  Submodule.subset_span ⟨1, by simp⟩

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.absType_pf :
    AbsType := by
  intro Γ F _ _ _ R B W V Y z hsym hpos hinv hW hV hVf hY hYV hzf hzt
  have hRR : ∀ k a, R k (R k⁻¹ a) = a := fun k a => by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have hadj : ∀ k a b, B a (R k b) = B (R k⁻¹ a) b := fun k a b => by
    have h := hinv k (R k⁻¹ a) b
    rwa [hRR] at h
  let T : Submodule ℂ F :=
    { carrier := {x | ∀ l : F →ₗ[ℂ] ℂ, (fun k => l (R k x)) ∈ W}
      add_mem' := fun {a b} ha hb l => by
        have h := W.add_mem (ha l) (hb l)
        convert h using 1
        ext k; simp
      zero_mem' := fun l => by
        have h := W.zero_mem
        convert h using 1
        ext k; simp
      smul_mem' := fun c x hx l => by
        have h := W.smul_mem c (hx l)
        convert h using 1
        ext k; simp }
  have hTR : ∀ g, ∀ x ∈ T, R g x ∈ T := fun g x hx l => by
    have h := hW _ (hx l) g
    convert h using 1
    ext k; simp [map_mul, Module.End.mul_apply]
  haveI : FiniteDimensional ℂ Y := hY
  haveI : FiniteDimensional ℂ (V ⊓ T : Submodule ℂ F) :=
    Submodule.finiteDimensional_of_le (S₂ := Y) fun x hx => hYV x hx.1 hx.2
  obtain ⟨P, hPm, hPo⟩ := exists_projL B hsym hpos (V ⊓ T)
  refine ⟨P z, (hPm z).1, hYV _ (hPm z).1 (hPm z).2, ?_⟩
  have hz1T : z - P z ∈ T := T.sub_mem hzt (hPm z).2
  have hZT : Submodule.span ℂ (Set.range fun k => R k (z - P z)) ≤ T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact hTR k _ hz1T
  have hZperp : ∀ a ∈ V ⊓ T, ∀ w ∈ Submodule.span ℂ (Set.range fun k => R k (z - P z)), B a w = 0 := by
    intro a ha w hw
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨k, rfl⟩ := h
      show B a (R k (z - P z)) = 0
      rw [hadj]
      exact hPo z _ ⟨hV _ _ ha.1, hTR _ _ ha.2⟩
    | zero => simp
    | add a' b _ _ ha' hb => rw [map_add (f := _), ha', hb, add_zero]
    | smul c a' _ ha' => rw [map_smul, ha', smul_zero]
  intro v hv
  haveI := hVf v hv
  obtain ⟨Q, hQm, hQo⟩ := exists_projL B hsym hpos (Submodule.span ℂ (Set.range fun k => R k v))
  have hV0V : Submodule.span ℂ (Set.range fun k => R k v) ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    exact hV k v hv
  have hzero : ∀ d, B d d = 0 → d = 0 := fun d h => by
    by_contra h0
    have h1 := hpos d h0
    simp [h] at h1
  have hQR : ∀ g x, Q (R g x) = R g (Q x) := fun g x => by
    have hd : Q (R g x) - R g (Q x) ∈ Submodule.span ℂ (Set.range fun k => R k v) :=
      Submodule.sub_mem _ (hQm _) (orbit_stable R v g _ (hQm x))
    have h1 := hQo (R g x) _ hd
    have h2 : B (Q (R g x) - R g (Q x)) (R g x - R g (Q x)) = 0 := by
      rw [← map_sub, hadj]
      exact hQo x _ (orbit_stable R v g⁻¹ _ hd)
    have h3 : B (Q (R g x) - R g (Q x)) (Q (R g x) - R g (Q x)) = 0 := by
      have h4 : B (Q (R g x) - R g (Q x)) (Q (R g x) - R g (Q x)) =
          B (Q (R g x) - R g (Q x)) (R g x - R g (Q x)) -
            B (Q (R g x) - R g (Q x)) (R g x - Q (R g x)) := by
        rw [← map_sub]
        congr 1
        abel
      rw [h4, h1, h2, sub_zero]
    exact sub_eq_zero.1 (hzero _ h3)
  have hQT : ∀ w ∈ Submodule.span ℂ (Set.range fun k => R k (z - P z)), Q w ∈ T := fun w hw l => by
    have h := hZT hw (l ∘ₗ Q)
    convert h using 1
    ext k; simp [hQR]
  have hQ0 : Q (z - P z) = 0 := by
    have hw := self_mem_orbit R (z - P z)
    have h1 := hZperp (Q (z - P z)) ⟨hV0V (hQm _), hQT _ hw⟩ _ hw
    have h2 := hQo (z - P z) _ (hQm (z - P z))
    rw [map_sub, h1, zero_sub, neg_eq_zero] at h2
    exact hzero _ h2
  have h := hQo (z - P z) v (self_mem_orbit R v)
  rwa [hQ0, sub_zero] at h
end

section

noncomputable section

open MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.BCT PositivityTheory.Rg.BcB
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem coset_integral (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G} (hK : IsOpen (K : Set G))
    (hfin : μ (K : Set G) ≠ ⊤) {h : G → ℂ} (hc : HasCompactSupport h) (hinv : ∀ g, ∀ k ∈ K, h (g * k) = h g) :
    ∃ T : Finset (G ⧸ K), (∀ q : G ⧸ K, h q.out ≠ 0 → q ∈ T) ∧ ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) →
      ∫ y, h y * f y ∂μ = ∑ q ∈ T, (μ.real (K : Set G) : ℂ) * (h q.out * f q.out) := by
  let c : G ⧸ K → Set G := fun q => {y | q.out⁻¹ * y ∈ K}
  have hcm : ∀ q y, y ∈ c q ↔ (QuotientGroup.mk y : G ⧸ K) = q := by
    intro q y
    change q.out⁻¹ * y ∈ K ↔ _
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hco : ∀ q, IsOpen (c q) := fun q => hK.preimage (continuous_const.mul continuous_id)
  have hmeas : ∀ q, μ (c q) = μ (K : Set G) := fun q => measure_preimage_mul μ q.out⁻¹ (K : Set G)
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover (fun g => c (QuotientGroup.mk g))
    (fun g _ => (hco _).mem_nhds ((hcm _ g).2 rfl))
  let T : Finset (G ⧸ K) := t.image fun g => (QuotientGroup.mk g : G ⧸ K)
  have hT : ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ K) ∈ T := by
    intro y hy
    obtain ⟨g, hg, hyg⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport h hy))
    rw [(hcm _ y).1 hyg]
    exact Finset.mem_image_of_mem _ hg
  refine ⟨T, fun q hq => ?_, fun f hf => ?_⟩
  · simpa [QuotientGroup.out_eq'] using hT _ hq
  have hval : ∀ q y, y ∈ c q → h y * f y = h q.out * f q.out := by
    intro q y hy
    have e : y = q.out * (q.out⁻¹ * y) := by group
    rw [e, hinv _ _ hy, hf _ _ hy]
  have hsum : (fun y => h y * f y) = fun y => ∑ q ∈ T, (c q).indicator (fun _ => h q.out * f q.out) y := by
    funext y
    by_cases hy : (QuotientGroup.mk y : G ⧸ K) ∈ T
    · have hyc : y ∈ c (QuotientGroup.mk y) := (hcm _ y).2 rfl
      rw [Finset.sum_eq_single (QuotientGroup.mk y : G ⧸ K), Set.indicator_of_mem hyc, hval _ y hyc]
      · intro q _ hq
        exact Set.indicator_of_notMem (fun hyq => hq ((hcm q y).1 hyq).symm) _
      · exact fun h' => (h' hy).elim
    · have hy0 : h y = 0 := by
        by_contra h'
        exact hy (hT y h')
      rw [hy0, zero_mul]
      refine (Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem (fun hyq => hy ?_) _).symm
      rwa [(hcm q y).1 hyq]
  rw [hsum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hco q).measurableSet]
    simp only [Measure.real, hmeas q, Complex.real_smul]
  · intro q _
    refine (integrable_indicator_iff (hco q).measurableSet).2 ?_
    exact integrableOn_const (by rw [hmeas q]; exact hfin)

end Abs

theorem heckeSum_pf : HeckeSum := by
  intro E _ _ _ n K hKo hKc μf _ h hh y hy
  have hfix : ∀ k ∈ K, finRep E n k y = y := fun k hk => by
    simpa using hy ⟨k, hk⟩
  obtain ⟨T, hT, hI⟩ := coset_integral μf hKo hKc.measure_lt_top.ne hh.1 (fun g k hk => (hh.2 k hk g).2)
  funext x
  have hf := hI (fun g => y.1 (x * finGL E n g)) (fun g k hk => by
    have e := congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (hfix k hk)
    have e' : y.1 (x * finGL E n g * finGL E n k) = y.1 (x * finGL E n g) := e
    simpa [mul_assoc] using e')
  have hL : Lv (finRep E n) K h = ∑ q ∈ T, h q.out • finRep E n q.out := by
    have hs : (Function.support fun q : GF E n ⧸ K => h q.out • (finRep E n q.out ∘ₗ LinearMap.id)) ⊆ T := by
      intro q hq
      refine hT q fun h0 => hq ?_
      simp [h0]
    simp only [Lv, levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
    rw [finsum_eq_sum_of_support_subset _ hs]
    rfl
  have hv : (∑ q ∈ T, (h q.out • finRep E n q.out) y : Sm E n).1 x =
      ∑ q ∈ T, h q.out * y.1 (x * finGL E n q.out) := by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [hL, heckeOp, hf, LinearMap.sum_apply, hv, Finset.mul_sum]
  rfl

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end
