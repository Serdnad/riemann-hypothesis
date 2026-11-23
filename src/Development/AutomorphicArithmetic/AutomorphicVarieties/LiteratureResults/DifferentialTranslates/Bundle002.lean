module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

section

noncomputable section

open Matrix
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

private theorem extDeriv_comp_linear_eq_of_differentiableAt {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} (f : V → V [⋀^Fin n]→L[ℝ] W)
    (A : V →L[ℝ] V) (M : W →L[ℝ] W) (p : V) (hf : DifferentiableAt ℝ f (A p))
    (v : Fin (n + 1) → V) :
    extDeriv (fun x => (ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ V W W (Fin n) M ∘SL
      ContinuousAlternatingMap.compContinuousLinearMapCLM A) (f (A x))) p v =
      M (extDeriv f (A p) (A ∘ v)) := by
  set L := ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ V W W (Fin n) M ∘SL
      ContinuousAlternatingMap.compContinuousLinearMapCLM A with hL
  have hd : DifferentiableAt ℝ (fun x => L (f (A x))) p :=
    L.differentiableAt.comp p (hf.comp p A.differentiableAt)
  have key : ∀ u : Fin n → V, HasFDerivAt (fun x => L (f (A x)) u)
      (M ∘L ((fderiv ℝ f (A p)).flipAlternating (A ∘ u)) ∘L A) p := by
    intro u
    exact M.hasFDerivAt.comp p
      ((hf.hasFDerivAt.continuousAlternatingMap_apply_const (A ∘ u)).comp p A.hasFDerivAt)

  rw [extDeriv_apply hd, extDeriv_apply hf, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(key _).fderiv, fderiv_continuousAlternatingMap_apply_const hf]
  simp
  rfl

theorem dEquiv : DEquiv := by
  intro Γ V S _ _ _ d G q γ w
  apply Subtype.ext
  funext s p
  change G.Y.indicator (extDeriv (fun x => G.tr q γ
      ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x)))) p =
    G.tr (q + 1) γ (G.Y.indicator
      (extDeriv ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ((G.σ γ⁻¹) s))) ((G.ρ γ⁻¹) p))
  by_cases hp : p ∈ G.Y
  · have hAp : (G.ρ γ⁻¹) p ∈ G.Y := G.maps γ⁻¹ p hp
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hAp]
    refine ContinuousAlternatingMap.ext fun v => ?_
    have hdiff : DifferentiableAt ℝ ((w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ((G.σ γ⁻¹) s))
        ((G.ρ γ⁻¹) p) :=
      ((w.2 ((G.σ γ⁻¹) s)).1.contDiffAt (G.isOpen.mem_nhds hAp)).differentiableAt (by simp)
    exact extDeriv_comp_linear_eq_of_differentiableAt _ _ (mulVecL (G.ξ γ)) p hdiff v
  · have hAp : (G.ρ γ⁻¹) p ∉ G.Y := by
      intro h
      have h2 := G.maps γ _ h
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        ContinuousLinearMap.one_apply] at h2
      exact hp h2
    rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hAp, map_zero]

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open scoped ContDiff Topology
open Set MeasureTheory

namespace UpperTheory.V.Lit.Dr

theorem paramDeriv : ParamDeriv := by
  intro V F _ _ _ _ _ _ p W Φ hW hWp hΦ
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hdiff : DifferentiableOn ℝ Φ W := hΦ.differentiableOn (by simpa using h1)
  set G : V × ℝ → V →L[ℝ] F := fun z => (fderiv ℝ Φ z).comp (ContinuousLinearMap.inl ℝ V ℝ) with hG
  have hGc : ContinuousOn G W :=
    (hΦ.continuousOn_fderiv_of_isOpen hW h1).clm_comp continuousOn_const
  have hpart : ∀ z ∈ W, HasFDerivAt (fun x => Φ (x, z.2)) (G z) z.1 := by
    intro z hz
    have hz1 : HasFDerivAt Φ (fderiv ℝ Φ z) z :=
      ((hdiff z hz).differentiableAt (hW.mem_nhds hz)).hasFDerivAt
    exact hz1.comp z.1 (hasFDerivAt_prodMk_left z.1 z.2)
  have hI : ∀ t ∈ Set.uIoc (0 : ℝ) 1, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    exact Ioc_subset_Icc_self ht
  have hline : ∀ x : V, Continuous (fun t : ℝ => (x, t)) := fun x =>
    continuous_const.prodMk continuous_id
  obtain ⟨u, v, hu, hv, hpu, hIv, huv⟩ := generalized_tube_lemma isCompact_singleton
    isCompact_Icc hW (by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      simp only [mem_singleton_iff] at hx
      subst hx
      exact hWp t ht)
  obtain ⟨ε, εpos, hball⟩ := Metric.isOpen_iff.mp hu p (hpu rfl)
  have hε : 0 < ε / 2 := half_pos εpos
  have hKW : Metric.closedBall p (ε / 2) ×ˢ Icc (0 : ℝ) 1 ⊆ W := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact huv ⟨hball (Metric.closedBall_subset_ball (by linarith) hx), hIv ht⟩
  have hKc : IsCompact (Metric.closedBall p (ε / 2) ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_closedBall p (ε / 2)).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hGc.mono hKW)
  have hpW : ∀ t ∈ Icc (0 : ℝ) 1, (p, t) ∈ W := hWp
  have hcont1 : ContinuousOn (fun t : ℝ => G (p, t)) (Icc 0 1) :=
    hGc.comp (hline p).continuousOn (fun t ht => hpW t ht)
  refine ⟨?_, ?_⟩
  · refine hcont1.congr ?_
    intro t ht
    exact (hpart (p, t) (hpW t ht)).fderiv
  · have hxW : ∀ x ∈ Metric.closedBall p (ε / 2), ∀ t ∈ Set.uIoc (0 : ℝ) 1, (x, t) ∈ W :=
      fun x hx t ht => hKW ⟨hx, hI t ht⟩
    have main := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume) (F := fun x t => Φ (x, t)) (F' := fun x t => G (x, t))
      (bound := fun _ => C) (s := Metric.closedBall p (ε / 2)) (a := 0) (b := 1)
      (Metric.closedBall_mem_nhds p hε)
      (by
        filter_upwards [Metric.closedBall_mem_nhds p hε] with x hx
        exact (hΦ.continuousOn.comp (hline x).continuousOn
          (fun t ht => hxW x hx t ht)).aestronglyMeasurable measurableSet_uIoc)
      (by
        apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le zero_le_one]
        exact hΦ.continuousOn.comp (hline p).continuousOn (fun t ht => hpW t ht))
      ((hcont1.mono (fun t ht => hI t ht)).aestronglyMeasurable measurableSet_uIoc)
      (Filter.Eventually.of_forall fun t ht x hx => hC _ ⟨hx, hI t ht⟩)
      intervalIntegrable_const
      (Filter.Eventually.of_forall fun t ht x hx => hpart (x, t) (hxW x hx t ht))
    refine main.congr_fderiv ?_
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact ((hpart (p, t) (hpW t ht)).fderiv).symm

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open CategoryTheory

namespace UpperTheory.V.Lit.Dr

theorem acyclic : Acyclic := by
  intro Γ Ω _ _ _ ρ hP n
  obtain ⟨P, hconst, hequi⟩ := hP
  let S : Subgroup Γ := ⊥
  haveI : Subsingleton S := ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  let A : Rep ℂ S := Rep.of (Representation.trivial ℂ S Ω)
  let C : Rep ℂ Γ := Rep.coind S.subtype A
  have hC : Subsingleton (groupCohomology C (n + 1)) := by
    have hz : Limits.IsZero (groupCohomology C (n + 1)) :=
      (isZero_groupCohomology_succ_of_subsingleton A n).of_iso (groupCohomology.coindIso A (n + 1))
    have h0 : 𝟙 (groupCohomology C (n + 1)) = 0 := hz.eq_of_src _ _
    refine ⟨fun a b => ?_⟩
    have ha := congrArg (fun f => f.hom a) h0
    have hb := congrArg (fun f => f.hom b) h0
    simp only [ModuleCat.hom_id, ModuleCat.hom_zero, LinearMap.id_apply, LinearMap.zero_apply] at ha hb
    rw [ha, hb]
  let L : Ω →ₗ[ℂ] (Γ → Ω) := LinearMap.pi fun h => ρ h
  have hL : ∀ x, L x ∈ Representation.coindV S.subtype A.ρ := by
    intro x g h
    have hg : (g : Γ) = 1 := Subgroup.mem_bot.1 g.2
    simp [L, hg, A]
  let iL : Ω →ₗ[ℂ] Representation.coindV S.subtype A.ρ := LinearMap.codRestrict _ L hL
  let M : Representation.coindV S.subtype A.ρ →ₗ[ℂ] (Γ → Ω) :=
    LinearMap.pi fun g => ρ g ∘ₗ LinearMap.proj g⁻¹ ∘ₗ Submodule.subtype _
  let rL : Representation.coindV S.subtype A.ρ →ₗ[ℂ] Ω := P ∘ₗ M
  let i : Rep.of ρ ⟶ C := Rep.ofHom ⟨iL, fun γ => by
    refine LinearMap.ext fun x => Subtype.ext (funext fun h => ?_)
    simp only [iL, L, LinearMap.comp_apply]
    show (ρ h) ((ρ γ) x) = (ρ (h * γ)) x
    rw [map_mul, Module.End.mul_apply]⟩
  let r : C ⟶ Rep.of ρ := Rep.ofHom ⟨rL, fun γ => by
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, rL, M]
    rw [hequi]
    congr 1
    funext g
    simp [mul_inv_rev, ← Module.End.mul_apply, ← map_mul]
    rfl⟩
  have hri : i ≫ r = 𝟙 _ := by
    ext x
    simp [i, r, rL, M, iL, L, ← Module.End.mul_apply, ← map_mul, hconst]
    show P (fun g => ρ g (ρ g⁻¹ x)) = x
    rw [show (fun g => ρ g (ρ g⁻¹ x)) = fun _ => x from
      funext fun g => by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply], hconst]
  let F := groupCohomology.functor ℂ Γ (n + 1)
  have hinj : Function.Injective (F.map i).hom := by
    intro a b hab
    have key : ∀ z, (F.map r).hom ((F.map i).hom z) = z := by
      intro z
      rw [← ModuleCat.comp_apply, ← F.map_comp, hri, F.map_id]
      rfl
    rw [← key a, ← key b, hab]
  haveI : Subsingleton (F.obj C) := hC
  exact hinj.subsingleton

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open CategoryTheory

namespace UpperTheory.V.Lit.Dr

theorem shiftUp : ShiftUp := by
  intro Γ M Ω Z _ _ _ _ _ _ _ ρM ρΩ ρZ ι π hι hπ hinj hsurj hex hΩ n
  let f : Rep.of ρM ⟶ Rep.of ρΩ := Rep.ofHom ⟨ι, fun γ => by ext m; exact hι γ m⟩
  let g : Rep.of ρΩ ⟶ Rep.of ρZ := Rep.ofHom ⟨π, fun γ => by ext x; exact hπ γ x⟩
  have hfg : f ≫ g = 0 := by
    ext m
    exact hex.apply_apply_eq_zero m
  let X : ShortComplex (Rep ℂ Γ) := ShortComplex.mk f g hfg
  have hX : X.ShortExact :=
    { exact := (forget₂ (Rep ℂ Γ) (ModuleCat ℂ)).reflects_exact_of_faithful _ <|
        (ShortComplex.moduleCat_exact_iff _).2 fun x hx => (hex x).1 hx
      mono_f := (Rep.mono_iff_injective _).2 hinj
      epi_g := (Rep.epi_iff_surjective _).2 hsurj }
  have hz : Limits.IsZero (groupCohomology X.X₂ (n + 1)) := by
    haveI := hΩ n
    exact ModuleCat.isZero_of_subsingleton _
  have hmono := groupCohomology.mono_δ_of_isZero hX (n + 1) hz
  have hinjδ := (ModuleCat.mono_iff_injective _).1 hmono
  exact LinearMap.rank_le_of_injective _ hinjδ

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open Set Topology Filter

namespace UpperTheory.V.Lit.Dr

private theorem exists_compact_open_exhaustion_of_isOpen {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Y : Set V) (hY : IsOpen Y) :
    ∃ K O : ℕ → Set V, (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ Y) ∧ (∀ n, IsOpen (O n)) ∧
      (∀ n, K n ⊆ O n) ∧ (∀ n, O n ⊆ K (n+1)) ∧ ∀ p ∈ Y, ∃ n, p ∈ K n := by
  refine ⟨fun n => Metric.closedBall (0:V) n \ Metric.thickening (1/((n:ℝ)+1)) Yᶜ,
    fun n => Metric.ball (0:V) ((n:ℝ)+1) \ Metric.cthickening (1/((n:ℝ)+2)) Yᶜ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (isCompact_closedBall _ _).diff Metric.isOpen_thickening
  · intro n x hx
    dsimp only at hx
    by_contra h
    exact hx.2 (Metric.self_subset_thickening (by positivity) _ h)
  · intro n
    exact Metric.isOpen_ball.sdiff Metric.isClosed_cthickening
  · intro n x hx
    dsimp only at hx ⊢
    refine ⟨?_, fun h => hx.2 (Metric.cthickening_subset_thickening' (by positivity)
      (one_div_lt_one_div_of_lt (by positivity) (by linarith)) _ h)⟩
    have h1 := hx.1
    rw [Metric.mem_closedBall] at h1
    rw [Metric.mem_ball]
    linarith
  · intro n x hx
    dsimp only at hx ⊢
    refine ⟨?_, fun h => hx.2 (Metric.thickening_subset_cthickening _ _ ?_)⟩
    · have h1 := hx.1
      rw [Metric.mem_ball] at h1
      rw [Metric.mem_closedBall]
      push_cast
      linarith
    · have e : (((n+1 : ℕ) : ℝ) + 1) = (n:ℝ) + 2 := by push_cast; ring
      rw [e] at h
      exact h
  · intro p hp
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hY p hp
    obtain ⟨n, hn⟩ := exists_nat_gt (max ‖p‖ (1/ε))
    refine ⟨n, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (le_max_left _ _).trans hn.le
    · rw [Metric.mem_thickening_iff]
      rintro ⟨y, hy, hd⟩
      apply hy
      apply hb
      rw [Metric.mem_ball, dist_comm]
      refine hd.trans ?_
      have h1 : 1/ε < n := (le_max_right _ _).trans_lt hn
      rw [div_lt_iff₀ hε] at h1
      rw [div_lt_iff₀ (by positivity)]
      nlinarith

theorem windowOne : WindowOne := by
  intro Γ V S _ _ _ _ d G hS hP
  rcases isEmpty_or_nonempty S with hE | ⟨⟨s₀⟩⟩
  · exact ⟨fun _ => ∅, fun s => isEmptyElim s, fun s => isEmptyElim s, fun s => isEmptyElim s⟩
  have hmul : ∀ (a b : Γ) (x : V), G.ρ (a * b) x = G.ρ a (G.ρ b x) := fun a b x => by
    rw [map_mul, ContinuousLinearMap.mul_apply]
  have hfin : ∀ K ⊆ G.Y, IsCompact K → {γ : Γ | ∃ p ∈ K, G.ρ γ p ∈ K}.Finite := fun K hK hKc =>
    (hP K hK hKc s₀ s₀).subset (fun γ h => ⟨Subsingleton.elim _ _, h⟩)
  have hball : ∀ p ∈ G.Y, ∃ r > 0, Metric.closedBall p r ⊆ G.Y := by
    intro p hp
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp G.isOpen p hp
    exact ⟨ε/2, half_pos hε, (Metric.closedBall_subset_ball (half_lt_self hε)).trans hb⟩
  have hsat : ∀ C ⊆ G.Y, IsCompact C → ∀ p ∈ G.Y, (¬ ∃ γ, G.ρ γ p ∈ C) →
      ∀ᶠ x in 𝓝 p, ¬ ∃ γ, G.ρ γ x ∈ C := by
    intro C hC hCc p hp hn
    obtain ⟨r, hr, hrY⟩ := hball p hp
    have hF := hfin _ (Set.union_subset hrY hC) ((isCompact_closedBall p r).union hCc)
    have h1 : ∀ᶠ x in 𝓝 p, x ∈ Metric.closedBall p r := Metric.closedBall_mem_nhds p hr
    have h2 : ∀ᶠ x in 𝓝 p, ∀ γ ∈ {γ : Γ | ∃ q ∈ Metric.closedBall p r ∪ C,
        G.ρ γ q ∈ Metric.closedBall p r ∪ C}, G.ρ γ x ∉ C := by
      rw [Filter.eventually_all_finite hF]
      intro γ _
      have ho : IsOpen ((G.ρ γ) ⁻¹' C)ᶜ := (hCc.isClosed.preimage (G.ρ γ).continuous).isOpen_compl
      exact ho.mem_nhds (fun h => hn ⟨γ, h⟩)
    filter_upwards [h1, h2] with x hx1 hx2
    rintro ⟨γ, hγ⟩
    exact hx2 γ ⟨x, Or.inl hx1, Or.inr hγ⟩ hγ
  obtain ⟨K, O, hKc, hKY, hOo, hKO, hOK, hcov⟩ := exists_compact_open_exhaustion_of_isOpen G.Y G.isOpen
  have hmono : Monotone K := monotone_nat_of_le_succ (fun n => (hKO n).trans (hOK n))
  have hOY : ∀ n, O n ⊆ G.Y := fun n => (hOK n).trans (hKY (n+1))
  have hmin : ∀ p ∈ G.Y, ∃ n γ, G.ρ γ p ∈ K n ∧ ∀ m < n, ¬ ∃ γ, G.ρ γ p ∈ K m := by
    intro p hp
    classical
    have hx : ∃ n, ∃ γ, G.ρ γ p ∈ K n := by
      obtain ⟨n, hn⟩ := hcov p hp
      exact ⟨n, 1, by rwa [map_one, ContinuousLinearMap.one_apply]⟩
    obtain ⟨γ, hγ⟩ := Nat.find_spec hx
    exact ⟨Nat.find hx, γ, hγ, fun m hm => Nat.find_min hx hm⟩
  let W0 : Set V := ⋃ n, {q | q ∈ O n ∧ ∀ m < n, ¬ ∃ γ, G.ρ γ q ∈ K m}
  refine ⟨fun _ => W0, fun s => ⟨?_, ?_⟩, fun s p hp => ?_, fun s p hp => ?_⟩
  · show IsOpen W0
    rw [isOpen_iff_mem_nhds]
    intro q hq
    obtain ⟨n, hqn⟩ := Set.mem_iUnion.mp hq
    have hq' : q ∈ O n ∧ ∀ m < n, ¬ ∃ γ, G.ρ γ q ∈ K m := hqn
    have hA : ∀ᶠ x in 𝓝 q, x ∈ O n := (hOo n).mem_nhds hq'.1
    have hB : ∀ᶠ x in 𝓝 q, ∀ m ∈ Set.Iio n, ¬ ∃ γ, G.ρ γ x ∈ K m := by
      rw [Filter.eventually_all_finite (Set.finite_Iio n)]
      intro m hm
      exact hsat (K m) (hKY m) (hKc m) q (hOY n hq'.1) (hq'.2 m hm)
    filter_upwards [hA, hB] with x hx1 hx2
    exact Set.mem_iUnion.mpr ⟨n, hx1, fun m hm => hx2 m hm⟩
  · show W0 ⊆ G.Y
    exact Set.iUnion_subset (fun n q hq => hOY n hq.1)
  · obtain ⟨n, γ, hγ, hm⟩ := hmin p hp
    refine ⟨γ⁻¹, ?_⟩
    show G.ρ γ⁻¹⁻¹ p ∈ W0
    rw [inv_inv]
    exact Set.mem_iUnion.mpr ⟨n, hKO n hγ, fun m hm' ⟨δ, hδ⟩ => hm m hm' ⟨δ * γ, by rw [hmul]; exact hδ⟩⟩
  · obtain ⟨n, γ, hγ, -⟩ := hmin p hp
    obtain ⟨r, hr, hrY⟩ := hball p hp
    have hF := hfin _ (Set.union_subset hrY (hKY (n+2))) ((isCompact_closedBall p r).union (hKc (n+2)))
    refine ⟨Metric.closedBall p r ∩ (G.ρ γ) ⁻¹' (O n),
      Filter.inter_mem (Metric.closedBall_mem_nhds p hr)
        (((hOo n).preimage (G.ρ γ).continuous).mem_nhds (hKO n hγ)), ?_⟩
    refine (hF.preimage (f := fun g : Γ => g⁻¹) (fun _ _ _ _ h => inv_injective h)).subset ?_
    rintro δ ⟨x, ⟨hx1, hx2⟩, hxW⟩
    obtain ⟨k, hk1, hk2⟩ := Set.mem_iUnion.mp hxW
    have hkn : k ≤ n + 1 := by
      by_contra hlt
      push_neg at hlt
      refine hk2 (n+1) hlt ⟨γ * δ, ?_⟩
      rw [hmul, ← hmul δ δ⁻¹ x, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
      exact hOK n hx2
    exact ⟨x, Or.inl hx1, Or.inr (hmono (by omega : k + 1 ≤ n + 2) (hOK k hk1))⟩

end UpperTheory.V.Lit.Dr
end
end

section

noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem avgMem : AvgMem := by
  intro Γ V S _ _ _ d G u hu q c
  obtain ⟨hsm, hfin, -⟩ := hu
  have hc : ∀ γ s, ContDiffOn ℝ ∞ ((c γ : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
      ∀ p ∉ G.Y, (c γ : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 :=
    fun γ s => (c γ).2 s
  simp only [Geo.Om, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  intro s
  refine ⟨?_, ?_⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro p hp
    obtain ⟨N, hN, hF⟩ := hfin s p hp
    obtain ⟨O, hON, hO, hpO⟩ := mem_nhds_iff.mp hN
    refine ⟨O, hO, hpO, ?_⟩
    have hsum : ContDiffOn ℝ ∞ (fun x => ∑ γ ∈ hF.toFinset,
        u ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x) • (c γ : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) (G.Y ∩ O) := by
      apply ContDiffOn.sum
      intro γ _
      have h1 : ContDiffOn ℝ ∞ (fun x => u ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x)) (G.Y ∩ O) :=
        ((hsm _).comp (G.ρ γ⁻¹).contDiff.contDiffOn
          (fun x hx => G.maps γ⁻¹ x hx.1))
      exact h1.smul ((hc γ s).1.mono Set.inter_subset_left)
    refine hsum.congr ?_
    intro x hx
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    rw [Set.Finite.coe_toFinset]
    refine ⟨x, hON hx.2, ?_⟩
    intro h0
    rw [Function.mem_support] at hγ
    exact hγ (by rw [h0, zero_smul])
  · intro p hp
    apply finsum_eq_zero_of_forall_eq_zero
    intro γ
    simp [(hc γ s).2 p hp]

end UpperTheory.V.Lit.Dr
end
end
