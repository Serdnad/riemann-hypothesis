module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

private theorem fderiv_apply_elim0_eq_zero_of_extDeriv_eq_zero {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : V → V [⋀^Fin 0]→L[ℝ] F) (x : V)
    (hd : DifferentiableAt ℝ f x) (h : extDeriv f x = 0) :
    fderiv ℝ (fun y => f y Fin.elim0) x = 0 := by
  ext1 h'
  have := extDeriv_apply hd (fun _ : Fin 1 => h')
  rw [h, Fin.sum_univ_one] at this
  rw [Subsingleton.elim (Fin.removeNth 0 fun _ : Fin 1 => h') Fin.elim0] at this
  simpa using this.symm

theorem inclFacts : InclFacts := by
  intro Γ V S _ _ _ d G hconv hne
  obtain ⟨p0, hp0⟩ := hne
  have back : ∀ (γ : Γ) (p : V), p ∉ G.Y → (G.ρ γ⁻¹) p ∉ G.Y := by
    intro γ p hp h
    have h2 := G.maps γ _ h
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply] at h2
    exact hp h2
  refine ⟨?_, ?_, ?_⟩
  · intro γ f
    apply Subtype.ext
    funext s p
    change G.Y.indicator (fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0)
        (G.ξ γ *ᵥ f ((G.σ γ⁻¹) s))) p =
      G.tr 0 γ (G.Y.indicator (fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0)
        (f ((G.σ γ⁻¹) s))) ((G.ρ γ⁻¹) p))
    by_cases hp : p ∈ G.Y
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (G.maps γ⁻¹ p hp)]
      ext v i
      simp [Geo.tr]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (back γ p hp), map_zero]
  · intro f g hfg
    funext s
    have h := congrArg (fun w : G.Om 0 => (w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p0 Fin.elim0) hfg
    simpa [Geo.incl, Set.indicator_of_mem hp0] using h
  · intro w
    constructor
    · intro hw
      have hd : ∀ s, ∀ x ∈ G.Y, extDeriv ((w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s) x = 0 := by
        intro s x hx
        have := congrArg (fun w' : G.Om 1 => (w' : S → V → V [⋀^Fin 1]→L[ℝ] (Fin d → ℂ)) s x) hw
        simpa [Geo.dOm, Set.indicator_of_mem hx] using this
      refine ⟨fun s => (w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p0 Fin.elim0, ?_⟩
      apply Subtype.ext
      funext s p
      have hda : ∀ y ∈ G.Y, DifferentiableAt ℝ ((w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s) y := fun y hy =>
        ((w.2 s).1.contDiffAt (G.isOpen.mem_nhds hy)).differentiableAt (by simp)
      have hdiff : DifferentiableOn ℝ (fun y => (w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s y Fin.elim0) G.Y := fun y hy =>
        ((hda y hy).continuousAlternatingMap_apply_const _).differentiableWithinAt
      have hconst : ∀ y ∈ G.Y, (w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s y Fin.elim0 = (w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p0 Fin.elim0 := fun y hy =>
        hconv.is_const_of_fderivWithin_eq_zero hdiff (fun x hx => by
          rw [fderivWithin_of_isOpen G.isOpen hx]
          exact fderiv_apply_elim0_eq_zero_of_extDeriv_eq_zero _ x (hda x hx) (hd s x hx)) hy hp0
      change G.Y.indicator (fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0)
        ((w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p0 Fin.elim0)) p = (w : S → V → V [⋀^Fin 0]→L[ℝ] (Fin d → ℂ)) s p
      by_cases hp : p ∈ G.Y
      · rw [Set.indicator_of_mem hp]
        ext v
        rw [Subsingleton.elim v Fin.elim0]
        simp [hconst p hp]
      · rw [Set.indicator_of_notMem hp, (w.2 s).2 p hp]
    · rintro ⟨f, rfl⟩
      apply Subtype.ext
      funext s p
      change G.Y.indicator (extDeriv (G.Y.indicator fun _ =>
        ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (f s))) p = 0
      by_cases hp : p ∈ G.Y
      · rw [Set.indicator_of_mem hp, Filter.EventuallyEq.extDeriv_eq
          (Filter.eventuallyEq_of_mem (G.isOpen.mem_nhds hp) (fun x hx => Set.indicator_of_mem hx _))]
        rw [extDeriv, fderiv_const_apply, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
          map_zero]
      · rw [Set.indicator_of_notMem hp]

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

namespace UpperTheory.V.Lit.Dr

open groupCohomology

theorem shiftOne : ShiftOne := by
  intro Γ M Ω Z _ _ _ _ _ _ _ ρM ρΩ ρZ ι π hι hπ hinj hsurj hex n w hw hlift
  classical
  choose y hy using fun i => hsurj (w i)
  have hker : ∀ i γ, π (ρΩ γ (y i) - y i) = 0 := by
    intro i γ
    rw [map_sub, hπ, hy, hw, sub_self]
  choose φ hφ using fun i γ => (hex (ρΩ γ (y i) - y i)).1 (hker i γ)
  have hcoc : ∀ i, φ i ∈ groupCohomology.cocycles₁ (Rep.of ρM) := by
    intro i
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    apply hinj
    rw [Rep.of_ρ]
    change ι (φ i (g * h)) = ι ((ρM g) (φ i h) + φ i g)
    rw [map_add (f := _), hι, hφ, hφ, hφ, map_mul, Module.End.mul_apply, map_sub]
    abel
  let v : Fin n → groupCohomology (Rep.of ρM) 1 :=
    fun i => (groupCohomology.H1π (Rep.of ρM)).hom ⟨φ i, hcoc i⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : (∑ i, g i • v i) =
        (groupCohomology.H1π (Rep.of ρM)).hom (∑ i, g i • (⟨φ i, hcoc i⟩ : groupCohomology.cocycles₁ (Rep.of ρM))) := by

      simp only [map_sum, map_smul, v]
    rw [hsum, groupCohomology.H1π_eq_zero_iff] at hg
    obtain ⟨m, hm⟩ := hg
    have key : Subtype.val (∑ i, g i • (⟨φ i, hcoc i⟩ : groupCohomology.cocycles₁ (Rep.of ρM))) = ∑ i, g i • φ i := by
      rw [Submodule.coe_sum]
      rfl
    have hm' : ∀ γ, ρM γ m - m = ∑ i, g i • φ i γ := by
      intro γ
      have := congrFun hm γ
      rw [groupCohomology.d₀₁_hom_apply, Rep.of_ρ] at this
      rw [this]
      exact (congrFun key γ).trans (Finset.sum_apply _ _ _)
    have hzero := hlift g ⟨(∑ i, g i • y i) - ι m, ?_, ?_⟩
    · intro i
      rw [hzero]
      rfl
    · intro γ
      have h1 : ι (ρM γ m) - ι m = ∑ i, g i • (ρΩ γ (y i) - y i) := by

        rw [← map_sub, hm', map_sum]
        simp only [map_smul, hφ]
      rw [hι] at h1

      rw [map_sub, map_sum]
      simp only [map_smul]
      simp only [smul_sub, Finset.sum_sub_distrib] at h1
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      abel

    · rw [map_sub, hex.apply_apply_eq_zero, sub_zero, map_sum]
      simp only [map_smul, hy]
  have := hli.cardinal_le_rank
  simpa using this

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

namespace UpperTheory.V.Lit.Dr

theorem shiftZero : ShiftZero := by
  intro Γ M _ _ _ ρ n w hw hlin
  let v : Fin n → (Rep.of ρ).ρ.invariants :=
    fun i => ⟨w i, (Representation.mem_invariants _ _).2 (hw i)⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ∑ i, g i • w i = 0 := by
      have := congrArg Subtype.val hg
      rw [Submodule.coe_sum] at this
      exact this
    rw [hlin g h0]
    intro i
    rfl
  have h1 := hli.cardinal_le_rank
  rw [Cardinal.mk_fin] at h1
  have hinj : Function.Injective (groupCohomology.H0Iso (Rep.of ρ)).inv.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact h1.trans (LinearMap.rank_le_of_injective _ hinj)

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem cutoff : Cutoff := by
  intro Γ V S _ _ _ _ d G W hW
  obtain ⟨hWo, hWc, hWf⟩ := hW
  choose φ hφs hφd hφr using fun s => (hWo s).1.exists_contDiff_support_eq (n := ⊤)
  have hnn : ∀ s x, 0 ≤ φ s x := fun s x => (hφr s ⟨x, rfl⟩).1
  have hne : ∀ s x, φ s x ≠ 0 ↔ x ∈ W s := fun s x => by rw [← Function.mem_support, hφs]
  have hmulσ : ∀ (a b : Γ) (s : S), G.σ (a * b) s = G.σ a (G.σ b s) := by
    intro a b s
    rw [map_mul, Equiv.Perm.mul_apply]
  have hmulρ : ∀ (a b : Γ) (x : V), G.ρ (a * b) x = G.ρ a (G.ρ b x) := by
    intro a b x
    rw [map_mul, ContinuousLinearMap.mul_apply]
  let Φ : S → V → ℝ := fun s p => ∑ᶠ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)
  have hinv : ∀ (δ : Γ) s p, Φ (G.σ δ⁻¹ s) (G.ρ δ⁻¹ p) = Φ s p := by
    intro δ s p
    show ∑ᶠ γ, φ (G.σ γ⁻¹ (G.σ δ⁻¹ s)) (G.ρ γ⁻¹ (G.ρ δ⁻¹ p)) = ∑ᶠ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)
    rw [← finsum_comp_equiv (Equiv.mulLeft δ) (f := fun γ => φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))]
    congr 1
    funext γ
    change φ (G.σ γ⁻¹ (G.σ δ⁻¹ s)) (G.ρ γ⁻¹ (G.ρ δ⁻¹ p)) =
      φ (G.σ (δ * γ)⁻¹ s) (G.ρ (δ * γ)⁻¹ p)
    rw [mul_inv_rev, hmulσ, hmulρ]
  have hloc : ∀ s, ∀ p ∈ G.Y, ∃ N ∈ nhds p, ∃ F : Finset Γ, ∀ x ∈ N, ∀ γ,
      φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x) ≠ 0 → γ ∈ F := by
    intro s p hp
    obtain ⟨N, hN, hNf⟩ := hWf s p hp
    exact ⟨N, hN, hNf.toFinset, fun x hx γ hγ => hNf.mem_toFinset.2 ⟨x, hx, (hne _ _).1 hγ⟩⟩
  have hΦeq : ∀ s (F : Finset Γ) x, (∀ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x) ≠ 0 → γ ∈ F) →
      Φ s x = ∑ γ ∈ F, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x) :=
    fun s F x h => finsum_eq_sum_of_support_subset _ (fun γ hγ => h γ hγ)
  have hpos : ∀ s, ∀ p ∈ G.Y, 0 < Φ s p := by
    intro s p hp
    obtain ⟨N, hN, F, hF⟩ := hloc s p hp
    rw [hΦeq s F p (hF p (mem_of_mem_nhds hN))]
    obtain ⟨γ, hγ⟩ := hWc s p hp
    have h0 : φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) ≠ 0 := (hne _ _).2 hγ
    exact Finset.sum_pos' (fun i _ => hnn _ _)
      ⟨γ, hF p (mem_of_mem_nhds hN) γ h0, lt_of_le_of_ne (hnn _ _) (Ne.symm h0)⟩
  have hsmooth : ∀ s, ∀ p ∈ G.Y, ContDiffAt ℝ ∞ (Φ s) p := by
    intro s p hp
    obtain ⟨N, hN, F, hF⟩ := hloc s p hp
    have hc : ContDiff ℝ ∞ (fun x => ∑ γ ∈ F, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x)) :=
      ContDiff.sum (fun γ _ => (hφd _).comp (G.ρ γ⁻¹).contDiff)
    refine hc.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hN] with x hx
    exact hΦeq s F x (hF x hx)
  refine ⟨fun s x => φ s x / Φ s x, fun s => ?_, fun s p hp => ?_, fun s p hp => ?_⟩
  · intro p hp
    exact ((hφd s).contDiffAt.div (hsmooth s p hp) (hpos s p hp).ne').contDiffWithinAt
  · obtain ⟨N, hN, hNf⟩ := hWf s p hp
    refine ⟨N, hN, hNf.subset ?_⟩
    rintro γ ⟨x, hx, hne0⟩
    exact ⟨x, hx, (hne _ _).1 (fun h => hne0 (by simp only [h, zero_div]))⟩
  · have e : ∀ γ : Γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) / Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) =
        φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) * (Φ s p)⁻¹ := fun γ => by rw [hinv, div_eq_mul_inv]
    show ∑ᶠ γ, φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) / Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = 1
    rw [finsum_congr e, ← finsum_mul]
    exact mul_inv_cancel₀ (hpos s p hp).ne'

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem applySmooth : ApplySmooth := by
  intro X _ _ V F _ _ _ _ q f v x hf hv
  let B : (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin q => V) F :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
  have hB : ContDiffAt ℝ ∞ (fun p : (V [⋀^Fin q]→L[ℝ] F) × (Fin q → V) => B p.1 p.2)
      (f x, fun i => v i x) :=
    (B.cpolynomialAt_uncurry_of_multilinear).contDiffAt
  have hin : ContDiffAt ℝ ∞ (fun y => (f y, fun i => v i y)) x :=
    hf.prodMk (contDiffAt_pi.mpr hv)
  exact hB.comp x hin

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

namespace UpperTheory.V.Lit.Dr

theorem altSym : AltSym := by
  intro V F _ _ _ _ q w p L γ u D hw hL hγ hu hD
  have hA : HasFDerivAt w (fderiv ℝ w p) p := hw.hasFDerivAt
  have hDi : ∀ i, D i = fderiv ℝ w p (L i p) (fun j => L (i.succAbove j) p) +
      ∑ j : Fin q, w p (Function.update (fun j' => L (i.succAbove j') p) j
        (L (i.succAbove j) (L i p))) := by
    intro i
    have hg : ∀ j : Fin q, HasFDerivAt (fun t => u i (i.succAbove j) t)
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (L (i.succAbove j) (L i p))) 0 :=
      fun j => ((hu i (i.succAbove j)).2).hasFDerivAt
    have hA' : HasFDerivAt w (fderiv ℝ w p) (γ i 0) := by
      rw [(hγ i).1]
      exact hA
    have hf : HasFDerivAt (fun t => w (γ i t))
        ((fderiv ℝ w p).comp (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (L i p))) 0 :=
      hA'.comp 0 (hγ i).2.hasFDerivAt
    have H := (hf.continuousAlternatingMap_apply hg).hasDerivAt
    rw [(hD i).unique H]
    have hu0 : ∀ j, u i j 0 = L j p := fun j => (hu i j).1
    simp [hu0, (hγ i).1]
  have hrm : ∀ i : Fin (q + 1), Fin.removeNth i (fun k => L k p) = fun j => L (i.succAbove j) p :=
    fun i => rfl
  rw [extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp only [hDi, smul_add, Finset.sum_add_distrib, hrm]
  suffices hS : ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • ∑ j : Fin q,
      w p (Function.update (fun j' => L (i.succAbove j') p) j (L (i.succAbove j) (L i p))) = 0 by
    rw [hS, add_zero]
  set M : Fin (q + 1) → Fin (q + 1) → V := fun i k => L k (L i p) with hM
  have hMs : ∀ i k, M i k = M k i := fun i k => hL k i
  set Y : Fin (q + 1) → Fin (q + 1) → Fin (q + 1) → V :=
    fun i k m => if m = i ∨ m = k then M i k else L m p with hYdef
  set c : Fin (q + 1) → Fin (q + 1) → F :=
    fun i k => if i = k then 0 else (-1 : ℤ) ^ (i : ℕ) • w p (Fin.removeNth i (Y i k)) with hcdef
  have hc : ∀ i k, c i k + c k i = 0 := by
    intro i k
    by_cases hik : i = k
    · subst hik
      simp [c]
    · have hY : Y k i = Y i k := by
        funext m
        simp only [Y, hMs k i, or_comm]
      simp only [c, hik, Ne.symm hik, if_false, hY]
      exact (w p).neg_one_pow_smul_map_removeNth_add_eq_zero_of_eq (v := Y i k) (by simp [Y]) hik
  have hsum : ∑ i, ∑ k, c i k = 0 := by
    have h1 : ∑ i, ∑ k, c i k = -∑ i, ∑ k, c i k := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      exact eq_neg_iff_add_eq_zero.mpr (hc k i)
    have h2 : (2 : ℝ) • ∑ i, ∑ k, c i k = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h1]
      exact add_neg_cancel _
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hne : ∀ (i : Fin (q + 1)) (j : Fin q), i ≠ i.succAbove j := fun i j => (Fin.succAbove_ne i j).symm
  have hrow : ∀ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • ∑ j : Fin q, w p (Function.update
      (fun j' => L (i.succAbove j') p) j (L (i.succAbove j) (L i p))) = ∑ k, c i k := by
    intro i
    rw [Fin.sum_univ_succAbove _ i, Finset.smul_sum]
    simp only [c, if_pos rfl, zero_add, hne, if_false]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    funext j'
    by_cases hj : j' = j
    · subst hj
      simp [Fin.removeNth_apply, Y, M]
    · simp [Fin.removeNth_apply, Y, M, Function.update_of_ne hj, Fin.succAbove_ne i j', hj]
  rw [← hsum]
  exact Finset.sum_congr rfl fun i _ => hrow i

end UpperTheory.V.Lit.Dr
end
end
