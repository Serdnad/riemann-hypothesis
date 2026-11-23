module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NoCommonZeroCombVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle026
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle019
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle020
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle034
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle002
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle017
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem continuous_section_polynomial_growth_of_isProper : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProper p → ∀ (B : LB Y), B.IsLB → ∀ s ∈ fibSec p (RingHom.id ℂ) B, (∀ j, ContinuousOn (s j) (ptsIn p (RingHom.id ℂ) (B.U j))) → ∀ (i : B.ι) (V : Y.Opens), IsAffineOpen V → V ≤ B.U i → ∃ (n : ℕ) (u : Fin n → Γ(Y, V)) (C : ℝ) (m : ℕ), ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ‖s i y‖ ≤ C * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  intro Y p hp B hB s hs hc i V hVa hV
  have := compactSpace_cxPts_of_isProper Y p hp
  obtain ⟨n, u, hu⟩ := GlobalTheory.T.regular_function_polynomial_growth Y p inferInstance inferInstance V hVa
  refine ⟨n, u, ?_⟩
  have h0 (y) : 0 ≤ ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine SectionGrowth.global_bound _ (fun y => ‖s i y‖) _ (fun y => le_add_of_nonneg_right (h0 y)) fun y₀ => ?_
  obtain ⟨j, hj⟩ := exists_mem_ptsIn hB.cover y₀
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := B.U j) (mem_ptsIn.1 hj)
  have h2 : W ≤ B.U j := hle
  have hW₀ : y₀ ∈ ptsIn p (RingHom.id ℂ) W := mem_ptsIn.2 hxW
  have h3 : V ⊓ W ≤ B.U i ⊓ B.U j := inf_le_inf hV h2
  obtain ⟨r, m, w, hb⟩ := hu W hW (resG Y h3 (B.g i j).val)
  have hn := (isOpen_ptsIn W).mem_nhds hW₀
  let F : CxPts p (RingHom.id ℂ) → ℝ := fun y => (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) * ‖s j y‖
  have hF : ContinuousAt F y₀ :=
    (tendsto_finsetSum _ fun k _ => ((continuousOn_ev (w k)).continuousAt hn).norm).mul
      ((hc j).continuousAt ((isOpen_ptsIn _).mem_nhds hj)).norm
  refine ⟨|F y₀| + 1, m, by positivity, ?_⟩
  filter_upwards [hn, hF.eventually (eventually_le_nhds (lt_of_le_of_lt (le_abs_self _) (lt_add_one |F y₀|)))]
    with y hy hFy hyV
  have hVW : y ∈ ptsIn p (RingHom.id ℂ) (V ⊓ W) := mem_ptsIn_inf.2 ⟨hyV, hy⟩
  have hb' := hb y hVW
  have hij : y ∈ ptsIn p (RingHom.id ℂ) (B.U i ⊓ B.U j) := ptsIn_mono h3 hVW
  have e : ev p (RingHom.id ℂ) (V ⊓ W) (resG Y h3 (B.g i j).val) y = ev p (RingHom.id ℂ) (B.U i ⊓ B.U j) (B.g i j).val y :=
    ev_res _ hVW _
  rw [e] at hb'
  rw [hs.1 i j y (ptsIn_mono hV hyV) (ptsIn_mono h2 hy), CxPts.gv, norm_mul]
  have hT : 0 ≤ (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := pow_nonneg (add_nonneg zero_le_one (h0 y)) _
  calc _ ≤ ((∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m) * ‖s j y‖ :=
        mul_le_mul_of_nonneg_right hb' (norm_nonneg _)
    _ = F y * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by simp only [F]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hFy hT

end GlobalTheory.CompanionTheory.Gaga
end
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.cone_series_differentiable_left_strip : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B N : ℕ) (cs : List (Fin r)) (u : (Fin r → ℕ) → ℚ), Fintype.card ι * B + 2 ≤ N → BddW u →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  DifferentiableOn ℂ (fun s => ∑' m, (u m : ℂ) * DL cs (coneTerm a b s) m) {s | -(B : ℝ) < s.re} := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.differentiableOn_tsum_weighted_DL_halfplane | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.differentiableOn_tsum_weighted_DL_halfplane | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.differentiableOn_tsum_weighted_DL_halfplane <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem exists_coneDomain : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v := by
  intro F _ _ _ 𝔣 h𝔣
  classical
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_congruence_unit_balancing_embeddings F 𝔣 h𝔣
  obtain ⟨κ, _, b, hbpos, hbcov⟩ := GlobalTheory.T.exists_totally_positive_basis_positive_coords F M
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.totally_positive_basis_ratio_bound F b hbpos

  obtain ⟨σ₁⟩ : Nonempty (F →+* ℝ) := by
    have w : InfinitePlace F := Classical.choice inferInstance
    exact ⟨w.embedding_of_isReal (IsTotallyReal.isReal w)⟩

  let G := ↥(congSubgroup 𝔣)
  let φ : G →* F := ((algebraMap (𝓞 F) F : 𝓞 F →+* F) : 𝓞 F →* F).comp ((Units.coeHom (𝓞 F)).comp (congSubgroup 𝔣).subtype)
  have hφ : ∀ g : G, φ g = (((g : (𝓞 F)ˣ) : 𝓞 F) : F) := fun g => rfl
  have hgpos : ∀ g : G, TotPos F (φ g) := fun g => g.2.2
  let f : G →* ℝ := (σ₁ : F →* ℝ).comp φ
  have hf : ∀ g : G, f g = σ₁ (φ g) := fun g => rfl
  have hfpos : ∀ g, 0 < f g := fun g => hgpos g σ₁
  have hφinj : Function.Injective φ := by
    intro g g' h
    apply Subtype.ext
    apply Units.ext
    exact RingOfIntegers.coe_injective h
  have hfinj : Function.Injective f := fun g g' h => hφinj (σ₁.injective h)
  let D : Set F := {x | ∀ i, 0 < b.repr x i}

  have hDpos : ∀ x ∈ D, TotPos F x := by
    intro x hx σ
    have hk : Nonempty κ := b.index_nonempty

    rw [← b.sum_repr x, map_sum]
    refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_pos (by exact_mod_cast hx i) (hbpos i σ)
  have hfin : {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite := by
    have hfin0 := GlobalTheory.T.finite_units_bounded_embedding_ratio F (R * R)
    refine Set.Finite.of_finite_image (f := fun g : G => (g : (𝓞 F)ˣ)) (hfin0.subset ?_) (Subtype.val_injective.injOn)
    rintro _ ⟨g, ⟨x, hx, hgx⟩, rfl⟩
    refine ⟨hgpos g, fun σ τ => ?_⟩
    have h1 := hR _ hgx σ τ
    have h2 := hR x hx τ σ
    have hxσ := hDpos x hx σ
    have hgτ := hgpos g τ
    rw [map_mul, map_mul] at h1
    have h3 : σ (φ g) * σ x ≤ (R * R * τ (φ g)) * σ x := by
      calc σ (φ g) * σ x ≤ R * (τ (φ g) * τ x) := h1
        _ ≤ R * (τ (φ g) * (R * σ x)) := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 hxσ
  let E : Set F := {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D}
  let T := {g : G | ∃ x ∈ D, φ g * x ∈ D}
  let Λ : Set (F →ₗ[ℚ] ℚ) := (fun p : G × κ => (b.coord p.2).comp (LinearMap.mulLeft ℚ (φ p.1))) '' (T ×ˢ Set.univ)
  have hΛ : Λ.Finite := (hfin.prod Set.finite_univ).image _
  have hsign : ∀ (p q : ℚ), SignType.sign p = SignType.sign q → 0 < p → 0 < q := by
    intro p q h hp
    rw [sign_pos hp] at h
    exact sign_eq_one_iff.mp h.symm
  have htile : Tile ((posCone F : ConvexCone ℚ F) : Set F) (fun _ => True) E := by
    refine GlobalTheory.T.cone_tiling_by_sign_regions (posCone F) b hbpos Λ hΛ E (fun x hx => hx.1) ?_
    intro x y hx hy hs hxE
    refine ⟨hy, fun g' hg' hyD => ?_⟩
    refine hxE.2 g' hg' ?_
    have hgT : g' ∈ T := ⟨y, hy, hyD⟩
    intro i
    have := hs _ ⟨(g', i), ⟨hgT, trivial⟩, rfl⟩
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.mulLeft_apply] at this
    exact hsign _ _ this.symm (hyD i)
  have h0 : (0 : F) ∉ E := by
    intro h
    have := hDpos 0 h.1 σ₁
    simp at this
  obtain ⟨ι, hι, r, v, hr, hli, hvP, hsub, hun⟩ := GlobalTheory.T.shintani_cone_decomposition _ _ E htile h0
  refine ⟨ι, hι, r, v, hr, hli, hvP, ?_⟩
  intro x hx

  obtain ⟨u, hu, hub⟩ := hM x hx
  have hxD : ∃ g : G, φ g * x ∈ D := by
    refine ⟨⟨u, hu⟩, hbcov _ ?_ hub⟩
    intro σ
    rw [map_mul]
    exact mul_pos (hu.2 σ) (hx σ)
  obtain ⟨g, hg, hguniq⟩ := GlobalTheory.T.unique_reduced_orbit_representative φ f hfpos hfinj D hfin x hxD
  obtain ⟨c, hc, hcuniq⟩ := hun _ hg
  refine ⟨(⟨g.1, g.2⟩, c), hc, ?_⟩
  rintro ⟨⟨u', hu'⟩, c'⟩ hp
  have hp' : φ ⟨u', hu'⟩ * x ∈ openCone (v c') := hp
  have hg' : (⟨u', hu'⟩ : G) = g := hguniq _ (hsub c' hp')
  have hc' : c' = c := by
    apply hcuniq
    rw [← hg']
    exact hp'
  subst hc'
  have := congrArg Subtype.val hg'
  simp only at this
  simp [this]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CuspNbhd

open GlobalTheory.AdelicU

theorem real_mul_level_mem_nhds : ∀ (D : D7) (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ N ∈ 𝓝 (1 : GA D V), {g : GA D V | ∃ r k : GA D V, r ∈ GinfC V ∧ r ∈ N ∧ k ∈ U ∧ k ∈ GfC V ∧ g = r * k} ∈ 𝓝 (1 : GA D V) := by
  intro D V U hU N hN
  have hr : Continuous fun g : GA D V =>
      ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g) :=
    (continuous_ofInf _ _).comp (continuous_projInf _ _)
  have hk : Continuous fun g : GA D V =>
      ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g) :=
    (continuous_ofFin _ _).comp (continuous_projFin _ _)
  have h1 : ∀ᶠ g : GA D V in 𝓝 1, ofInf D.sp.cm.sig V.gram (projInf D.sp.cm.sig V.gram g) ∈ N := by
    have := hr.continuousAt (x := (1 : GA D V))
    simp only [ContinuousAt, map_one] at this
    exact this hN
  have h2 : ∀ᶠ g : GA D V in 𝓝 1, ofFin D.sp.cm.sig V.gram (projFin D.sp.cm.sig V.gram g) ∈ U := by
    have := hk.continuousAt (x := (1 : GA D V))
    simp only [ContinuousAt, map_one] at this
    exact this (hU.mem_nhds U.one_mem)
  filter_upwards [h1, h2] with g hg1 hg2
  exact ⟨_, _, mem_infPts.2 (by simp), hg1, hg2, mem_finPts.2 (by simp),
    (ofInf_projInf_mul_ofFin_projFin D.sp.cm.sig V.gram g).symm⟩

end GlobalTheory.CompanionTheory.CuspNbhd
end
