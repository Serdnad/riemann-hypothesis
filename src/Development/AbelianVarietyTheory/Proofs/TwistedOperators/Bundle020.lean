module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle006
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle017
public import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

theorem schwartzBruhat_eventually_invariant_of_continuous_action :
    ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
      (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) →
      Continuous (fun p : X × G => r p.1 p.2) →
      ∀ Φ : SB X, ∀ᶠ u in nhds (1 : G), ∀ x, Φ.1 (r x u) = Φ.1 x := by
  intro G X _ _ _ _ r h1 hmul hc Φ
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  obtain ⟨hlc, hcs⟩ := hΦ
  have hA : IsLocallyConstant (fun z : G × X => Φ.1 (r z.2 z.1)) :=
    hlc.comp_continuous (hc.comp continuous_swap)
  have hB : IsLocallyConstant (fun z : G × X => Φ.1 z.2) :=
    hlc.comp_continuous continuous_snd
  have key : ∀ᶠ u in nhds (1 : G), ∀ x ∈ tsupport Φ.1, Φ.1 (r x u) = Φ.1 x := by
    refine IsCompact.eventually_forall_of_forall_eventually
      (P := fun u x => Φ.1 (r x u) = Φ.1 x) hcs ?_
    intro y _
    filter_upwards [hA.eventually_eq ((1 : G), y), hB.eventually_eq ((1 : G), y)] with z hz hz'
    rw [hz, hz']
    simp only [h1]
  have key' : ∀ᶠ u in nhds (1 : G), ∀ x ∈ tsupport Φ.1, Φ.1 (r x u⁻¹) = Φ.1 x := by
    have ht : Filter.Tendsto (fun u : G => u⁻¹) (nhds 1) (nhds 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact ht.eventually key
  filter_upwards [key, key'] with u hu hu' x
  by_cases hx : x ∈ tsupport Φ.1
  · exact hu x hx
  · by_cases hy : r x u ∈ tsupport Φ.1
    · have := hu' _ hy
      rw [← hmul, mul_inv_cancel, h1] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory.FockFamily

theorem fockForm_family_contDiff {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : ℝ → (V × V) →ₗ[ℝ] (V × V)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockB (J t)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => GlobalTheory.FockFamily.blockD (J t)) →
    (∀ t, IsUnit (GlobalTheory.FockFamily.blockB (J t))) →
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.FockFamily.fockForm β (J t) x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => GlobalTheory.FockFamily.fockForm β (J p.1) p.2 p.2) := by
  intro hB hD hU

  let β₁ : V →ₗ[ℝ] (V →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ β
  let βc : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap β₁
  have hβc : ∀ x y, βc x y = β x y := fun x y => rfl

  have hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => Ring.inverse (blockB (J t))) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    exact (contDiffAt_ringInverse ℝ (hU t).unit).comp t hB.contDiffAt
  have hDC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t => (blockD (J t)).comp (Ring.inverse (blockB (J t)))) := hD.clm_comp hC
  have hπ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ × V => (Real.pi : ℂ) * Complex.I) := contDiff_const
  have hπ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℝ => (Real.pi : ℂ) * Complex.I) := contDiff_const
  have hR : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ},
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun e => ((f e : ℝ) : ℂ)) :=
    fun hf => Complex.ofRealCLM.contDiff.comp hf
  constructor
  · intro x y
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => Real.pi * βc x (Ring.inverse (blockB (J t)) y)) :=
      contDiff_const.mul (contDiff_const.clm_apply (hC.clm_apply contDiff_const))
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t => βc x (((blockD (J t)).comp (Ring.inverse (blockB (J t)))) y)) :=
      contDiff_const.clm_apply (hDC.clm_apply contDiff_const)
    have := (hR h1).add (hπ'.mul (hR h2))
    simpa only [fockForm_apply, hβc, ContinuousLinearMap.comp_apply] using this
  · have hCp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => Ring.inverse (blockB (J p.1)) p.2) :=
      (hC.comp contDiff_fst).clm_apply contDiff_snd
    have hDCp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => ((blockD (J p.1)).comp (Ring.inverse (blockB (J p.1)))) p.2) :=
      (hDC.comp contDiff_fst).clm_apply contDiff_snd
    have hβp : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => βc p.2) :=
      βc.contDiff.comp contDiff_snd
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => Real.pi * βc p.2 (Ring.inverse (blockB (J p.1)) p.2)) :=
      contDiff_const.mul (hβp.clm_apply hCp)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × V => βc p.2 (((blockD (J p.1)).comp (Ring.inverse (blockB (J p.1)))) p.2)) :=
      hβp.clm_apply hDCp
    have := (hR h1).add (hπ.mul (hR h2))
    simpa only [fockForm_apply, hβc, ContinuousLinearMap.comp_apply] using this

end GlobalTheory.FockFamily
end

section

open MeasureTheory

noncomputable section

namespace GlobalTheory.FockFamily

theorem fderiv_eq_of_dHeis {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (hB : IsUnit (blockB J)) (g : V → ℂ)
    (heq : ∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) (x y : V) :
    fderiv ℝ g x y = 2 * fockForm β J x y * g x := by
  have h := heq (0, Ring.inverse (blockB J) y) x
  have h1 : (J (0, Ring.inverse (blockB J) y)).1 = y := by
    rw [← blockB_apply, ← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hB]; rfl
  have h2 : (J (0, Ring.inverse (blockB J) y)).2 = blockD J (Ring.inverse (blockB J) y) := rfl
  simp only [GlobalTheory.GaussLine.dHeis, h1, h2, map_zero, zero_sub] at h
  rw [fockForm_apply]
  push_cast
  linear_combination h - 2 * Real.pi * (β x (Ring.inverse (blockB J) y) : ℂ) * g x * Complex.I_sq

theorem solution_eq_gauss {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : (V × V) →ₗ[ℝ] (V × V)) (hB : IsUnit (blockB J)) (g : V → ℂ)
    (hg : Differentiable ℝ g)
    (heq : ∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) (x : V) :
    g x = g 0 * Complex.exp (fockForm β J x x) := by
  set c : ℂ := fockForm β J x x with hc
  let h : ℝ → ℂ := fun s => g (s • x) * Complex.exp (-(((s ^ 2 : ℝ)) : ℂ) * c)
  have hd : ∀ s : ℝ, HasDerivAt h 0 s := by
    intro s
    have e1 : HasDerivAt (fun t : ℝ => g (t • x)) (fderiv ℝ g (s • x) x) s := by
      have := (hg (s • x)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).smul_const x)
      simp only [one_smul] at this
      exact this
    have e2 : HasDerivAt (fun t : ℝ => Complex.exp (-(((t ^ 2 : ℝ)) : ℂ) * c))
        (Complex.exp (-(((s ^ 2 : ℝ)) : ℂ) * c) * (-((((2 : ℕ) : ℝ) * s ^ (2 - 1) * 1 : ℝ) : ℂ) * c)) s := by
      exact ((((hasDerivAt_id s).pow 2).ofReal_comp).neg.mul_const c).cexp
    have hf : fderiv ℝ g (s • x) x = 2 * ((s : ℂ) * c) * g (s • x) := by
      rw [fderiv_eq_of_dHeis β J hB g heq, map_smul, LinearMap.smul_apply, Complex.real_smul]
    show HasDerivAt (fun t : ℝ => g (t • x) * Complex.exp (-(((t ^ 2 : ℝ)) : ℂ) * c)) 0 s
    refine (e1.mul e2).congr_deriv ?_
    rw [hf]
    push_cast
    ring
  have hconst : ∀ a b : ℝ, h a = h b := fun a b =>
    is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) a b
  have := hconst 1 0
  simp only [h, one_smul, zero_smul, one_pow, Complex.ofReal_one, neg_mul, one_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, mul_one] at this
  rw [← this, mul_assoc, ← Complex.exp_add]
  simp

end GlobalTheory.FockFamily

end
end

section

open MeasureTheory

noncomputable section

namespace GlobalTheory.FockFamily

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem isUnit_of_injective_clm (B : V →L[ℝ] V) (h : Function.Injective B) : IsUnit B := by
  have hs : Function.Surjective (B : V →ₗ[ℝ] V) := LinearMap.injective_iff_surjective.mp h
  let e : V ≃ₗ[ℝ] V := LinearEquiv.ofBijective (B : V →ₗ[ℝ] V) ⟨h, hs⟩
  let e' : V ≃L[ℝ] V := e.toContinuousLinearEquiv
  refine ⟨(ContinuousLinearEquiv.unitsEquiv ℝ V).symm e', ?_⟩
  ext x; rfl

theorem dense_pair_ne_zero (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (q x₀ : V) (hx : β x₀ q ≠ 0) :
    Dense {x | β x q ≠ 0} := by
  have hint : interior ((LinearMap.ker (β.flip q) : Submodule ℝ V) : Set V) = ∅ := by
    by_contra hne
    have := Submodule.eq_top_of_nonempty_interior' _ (Set.nonempty_iff_ne_empty.mpr hne)
    apply hx
    have : x₀ ∈ LinearMap.ker (β.flip q) := by rw [this]; trivial
    simpa using this
  have := interior_eq_empty_iff_dense_compl.mp hint
  convert this using 1
  ext x; simp

theorem isUnit_blockB_of_solution (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hβ : ∀ q, (∀ x, β x q = 0) → q = 0)
    (J : (V × V) →ₗ[ℝ] (V × V)) (g : V → ℂ) (hg : Continuous g) (hg0 : g ≠ 0)
    (hJ : ∀ w x, GlobalTheory.GaussLine.dHeis β (J w) g x = Complex.I * GlobalTheory.GaussLine.dHeis β w g x) :
    IsUnit (blockB J) := by
  apply isUnit_of_injective_clm
  refine (injective_iff_map_eq_zero (blockB J)).mpr ?_
  intro q hq
  apply hβ q
  by_contra hne
  push_neg at hne
  obtain ⟨x₀, hx₀⟩ := hne
  have hzero : ∀ x, β x q ≠ 0 → g x = 0 := by
    intro x hx
    have h := hJ (0, q) x
    have h1 : (J (0, q)).1 = 0 := by rw [← blockB_apply]; exact hq
    simp only [GlobalTheory.GaussLine.dHeis, h1, map_zero] at h
    have key : (((β x q : ℝ) : ℂ) + Complex.I * ((β x (J (0, q)).2 : ℝ) : ℂ)) * g x = 0 := by
      have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
        have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      have h2 : (2 * Real.pi : ℂ) * ((((β x q : ℝ) : ℂ) + Complex.I * ((β x (J (0, q)).2 : ℝ) : ℂ)) * g x) = 0 := by
        linear_combination (-1 : ℂ) * h + (2 * Real.pi * ((β x q : ℝ) : ℂ) * g x) * Complex.I_sq
      exact (mul_eq_zero.mp h2).resolve_left hpi
    rcases mul_eq_zero.mp key with h3 | h3
    · exfalso; apply hx
      have := congrArg Complex.re h3
      simpa using this
    · exact h3
  apply hg0
  have hd := dense_pair_ne_zero β q x₀ hx₀
  exact Continuous.ext_on hd hg continuous_const (fun x hx => hzero x hx)
end FockFamily
end GlobalTheory
end
end

section

open MeasureTheory

namespace GlobalTheory

open LineDeriv

theorem dHeis_schwartz {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (w : V × V) (f : SchwartzMap V ℂ) :
    ∃ g : SchwartzMap V ℂ, ∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x := by
  let L : V →L[ℝ] ℂ := Complex.ofRealCLM.comp (LinearMap.toContinuousLinearMap (β.flip w.2))
  have hL : Function.HasTemperateGrowth (fun x : V => (L x : ℂ)) := L.hasTemperateGrowth
  refine ⟨∂_{w.1} f - (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x : V => (L x : ℂ)) f, ?_⟩
  intro x
  rw [SchwartzMap.sub_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hL,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp [GlobalTheory.GaussLine.dHeis, L, smul_eq_mul]
  ring

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory.StabGen

open GlobalTheory.TensHead

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stabClosure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) : Submodule ℂ M :=
  sInf {N | Rel ≤ N ∧ Stab Op N ∧ S ⊆ N}

theorem rel_le_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Rel ≤ stabClosure Op Rel S :=
  le_sInf fun _ hN => hN.1

theorem subset_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    S ⊆ stabClosure Op Rel S := fun _ hx =>
  Submodule.mem_sInf.2 fun _ hN => hN.2.2 hx

theorem stab_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Stab Op (stabClosure Op Rel S) := by
  intro g hg x hx
  rw [stabClosure, Submodule.mem_sInf] at hx ⊢
  intro N hN
  exact hN.2.1 g hg x (hx N hN)

theorem closure_le {Op : Set (Module.End ℂ M)} {Rel N : Submodule ℂ M} {S : Set M}
    (h1 : Rel ≤ N) (h2 : Stab Op N) (h3 : S ⊆ N) : stabClosure Op Rel S ≤ N :=
  sInf_le ⟨h1, h2, h3⟩

theorem closure_mono {Op : Set (Module.End ℂ M)} {Rel : Submodule ℂ M} {S T : Set M}
    (h : S ⊆ T) : stabClosure Op Rel S ≤ stabClosure Op Rel T :=
  closure_le (rel_le_closure Op Rel T) (stab_closure Op Rel T)
    (h.trans (subset_closure Op Rel T))

noncomputable def chainSet [DecidableEq M] (pick : Finset M → M) : ℕ → Finset M
  | 0 => ∅
  | n + 1 => insert (pick (chainSet pick n)) (chainSet pick n)

theorem exists_finset_generating (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M)
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) :
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N →
      (↑F : Set M) ⊆ ↑N → N = ⊤ := by
  classical
  obtain ⟨L, hL⟩ := hL
  by_contra hne
  push_neg at hne
  have hx : ∀ F : Finset M, ∃ x, x ∉ stabClosure Op Rel (F : Set M) := by
    intro F
    obtain ⟨N, h1, h2, h3, h4⟩ := hne F
    by_contra h
    push_neg at h
    exact h4 (eq_top_iff.2 fun x _ => closure_le h1 h2 h3 (h x))
  choose pick hpick using hx
  have hD : StrictMono fun n => stabClosure Op Rel (↑(chainSet pick n) : Set M) := by
    refine strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne ?_ ?_
    · exact closure_mono (Finset.coe_subset.2 (Finset.subset_insert _ _))
    · intro h
      apply hpick (chainSet pick n)
      have hmem : pick (chainSet pick n) ∈ stabClosure Op Rel (↑(chainSet pick (n + 1)) : Set M) :=
        subset_closure Op Rel _ (by simp [chainSet])
      rw [← h] at hmem
      exact hmem
  have := hL (L + 1) (fun j => stabClosure Op Rel (↑(chainSet pick j) : Set M))
    (fun a b hab => hD hab) (fun j => ⟨rel_le_closure _ _ _, stab_closure _ _ _⟩)
  omega

end GlobalTheory.StabGen
end

section

open scoped TensorProduct

namespace GlobalTheory.TensHead

theorem exists_maximal_stab_of_finset {V : Type} [AddCommGroup V] [Module ℂ V]
    (G : Set (Module.End ℂ V)) (R : Submodule ℂ V) (F : Finset V)
    (hF : ∀ N : Submodule ℂ V, R ≤ N → Stab G N → (↑F : Set V) ⊆ ↑N → N = ⊤) :
    ∀ N : Submodule ℂ V, R ≤ N → Stab G N → N ≠ ⊤ →
      ∃ N' : Submodule ℂ V, N ≤ N' ∧ Stab G N' ∧ N' ≠ ⊤ ∧
        ∀ U : Submodule ℂ V, Stab G U → N' ≤ U → U = N' ∨ U = ⊤ := by
  intro N hRN hN hNtop
  let s : Set (Submodule ℂ V) := {U | R ≤ U ∧ Stab G U ∧ ¬ (↑F : Set V) ⊆ ↑U}
  have hcomp := (isCompactElement_iff_le_of_directed_sSup_le _).1
    (Submodule.finset_span_isCompactElement (R := ℂ) F)
  have hNs : N ∈ s := ⟨hRN, hN, fun h => hNtop (hF N hRN hN h)⟩
  obtain ⟨M, hNM, hM⟩ := zorn_le_nonempty₀ s (by
    intro c hcs hc y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨le_trans (hcs hy).1 (le_sSup hy), ?_, ?_⟩, fun z hz => le_sSup hz⟩
    · intro g hg x hx
      obtain ⟨U, hU, hxU⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨U, hU, (hcs hU).2.1 g hg x hxU⟩
    · intro hFc
      have hspan : Submodule.span ℂ (↑F : Set V) ≤ sSup c := Submodule.span_le.2 hFc
      obtain ⟨U, hU, hle⟩ := hcomp c hne hdir hspan
      exact (hcs hU).2.2 (Submodule.span_le.1 hle)) N hNs
  refine ⟨M, hNM, hM.prop.2.1, fun h => hM.prop.2.2 (by rw [h]; exact fun _ _ => trivial), ?_⟩
  intro U hU hMU
  by_cases hFU : (↑F : Set V) ⊆ ↑U
  · exact Or.inr (hF U (le_trans hM.prop.1 hMU) hU hFU)
  · exact Or.inl (le_antisymm (hM.2 ⟨le_trans hM.prop.1 hMU, hU, hFU⟩ hMU) hMU)

end GlobalTheory.TensHead
end

section

open scoped TensorProduct

namespace GlobalTheory.TensHead


open scoped TensorProduct in
theorem _root_.GlobalTheory.TensHead.stab_piOps_piKer {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i))
    (h : ∀ i, _root_.GlobalTheory.TensHead.Stab (Op i) (K i)) :
    _root_.GlobalTheory.TensHead.Stab (_root_.GlobalTheory.TensHead.piOps Op) (_root_.GlobalTheory.TensHead.piKer K) := by
  unfold _root_.GlobalTheory.TensHead.Stab at h ⊢
  rintro _ ⟨i, g, hg, rfl⟩ x hx
  unfold _root_.GlobalTheory.TensHead.piKer at hx ⊢
  have hle : Submodule.span ℂ {t | ∃ y : ∀ j, M j, (∃ j, y j ∈ K j) ∧ t = PiTensorProduct.tprod ℂ y}
      ≤ (Submodule.span ℂ {t | ∃ y : ∀ j, M j, (∃ j, y j ∈ K j) ∧ t = PiTensorProduct.tprod ℂ y}).comap
        (_root_.GlobalTheory.TensHead.piOp i g) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, ⟨j, hj⟩, rfl⟩
    refine Submodule.subset_span ⟨fun k => Function.update (fun _ => LinearMap.id) i g k (y k), ⟨j, ?_⟩, ?_⟩
    · by_cases hji : j = i
      · subst hji
        simpa using h j g hg _ hj
      · simpa [Function.update_of_ne hji] using hj
    · simp [_root_.GlobalTheory.TensHead.piOp]
  exact hle hx

end GlobalTheory.TensHead
end

section

open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

theorem smulInvariantMeasure_shear_map (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H) (hNc : IsClosed (N : Set H))
    (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (hκ : κ.IsHaarMeasure)
    (hconj : ∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) :
    SMulInvariantMeasure (pairGroup Γ N hN) (H × H) ((κ.prod ν).map (shear N)) := by
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI : SigmaFinite κ := inferInstance
  refine ⟨fun g s hs => ?_⟩
  obtain ⟨⟨u, v⟩, hu, hv, huv⟩ := g
  have hmeasg : Measurable (fun x : H × H => ((⟨(u, v), hu, hv, huv⟩ : pairGroup Γ N hN)) • x) := by
    change Measurable (fun x : H × H => (u * x.1, v * x.2))
    exact (measurable_fst.const_mul u).prodMk (measurable_snd.const_mul v)
  let δ : N := ⟨u * v⁻¹, huv⟩
  let c : N → N := fun n => ⟨v * n * v⁻¹, hN v hv n n.2⟩
  have hc : MeasurePreserving c κ κ :=
    ⟨(show Continuous c from ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _).measurable,
      hconj v hv⟩
  have hf : MeasurePreserving (fun n : N => δ * c n) κ κ := (measurePreserving_mul_left κ δ).comp hc
  have hT : MeasurePreserving (Prod.map (fun n : N => δ * c n) (fun h : H => v * h)) (κ.prod ν) (κ.prod ν) :=
    hf.prod (measurePreserving_mul_left ν v)
  have hsh := (measurableEmbedding_shear (N := N) hNc)
  have key : (fun x : H × H => ((⟨(u, v), hu, hv, huv⟩ : pairGroup Γ N hN)) • x) ∘ shear N
      = shear N ∘ Prod.map (fun n : N => δ * c n) (fun h : H => v * h) := by
    funext p
    change (u * (p.1 * p.2), v * p.2) = (((u * v⁻¹) * (v * p.1 * v⁻¹)) * (v * p.2), v * p.2)
    congr 1
    group
  rw [← Measure.map_apply hmeasg hs, Measure.map_map hmeasg hsh.measurable, key,
    ← Measure.map_map hsh.measurable hT.measurable, hT.map_eq]

end GlobalTheory.UnfoldNormal
end
