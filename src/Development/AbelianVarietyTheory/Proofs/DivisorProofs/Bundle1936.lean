module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1908
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotDvdDiscrIffRamificationIdx
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapFinPartILocFEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle054
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle048
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle047
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SmallRoute

theorem continuous_translates_kerSmall : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ),
    Continuous (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
      translates z (kerSmall W Θ' p.1 g₁) p.2) := by
  intro D T L sc G μ₀ hL W B ρ t i j Θ Θ' hΘ g₁ z
  obtain ⟨_, _, _, _, hTG, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid i j))
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have hm := W.om_is (.mu t (i : ℕ) j) ⟨i.2.le, j.2⟩
  have hK : ∀ d ∈ Θ'.support, Continuous (fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
      W.kerA (.down t i j) d.1.2 q.1 q.2 * W.kerA (.right i j) d.2 q.2 g₁) := by
    intro d hd
    obtain ⟨h2, h1⟩ := theta_of_matched hΘ hd
    refine Continuous.mul ?_ ?_
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
        thetaKO (W.om (.mu t (i : ℕ) j)) q.2 q.1 d.1.2
      exact (hm.om_cont _ h1 0).comp (continuous_snd.prodMk continuous_fst)
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
        thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) q.2 d.2
      exact (hc.om_cont _ h2 0).comp (continuous_const.prodMk continuous_snd)
  unfold translates kerSmall
  simp only [Finsupp.sum]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  refine continuous_finsetSum _ fun d hd => continuous_const.mul ?_
  exact (hK d hd).comp (continuous_fst.prodMk (continuous_snd.mul continuous_const))

end GlobalTheory.SmallRoute
end

section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory

theorem fderiv_smul_eq_zero_of_invariant {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (ξ : E) (hf : ∀ (x : E) (c : ℂ), f (x + c • ξ) = f x) (x : E) (c : ℂ) :
    fderiv ℝ f x (c • ξ) = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have hl : HasDerivAt (fun t : ℝ => x + t • (c • ξ)) (c • ξ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (c • ξ)).const_add x
    have hx : x + (0 : ℝ) • (c • ξ) = x := by simp
    have hd' : DifferentiableAt ℝ f (x + (0 : ℝ) • (c • ξ)) := by rw [hx]; exact hd
    have h1 := hd'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
    rw [hx] at h1
    have hconst : (fun t : ℝ => f (x + t • (c • ξ))) = fun _ => f x := by
      funext t
      rw [← smul_assoc]
      exact hf x _
    have h2 : HasDerivAt (fun t : ℝ => f (x + t • (c • ξ))) 0 0 := by
      rw [hconst]; exact hasDerivAt_const _ _
    exact h1.unique h2
  · rw [fderiv_zero_of_not_differentiableAt hd]; rfl

end GlobalTheory

namespace GlobalTheory

theorem ddc_eq_zero_of_invariant : ∀ (n : ℕ) (u : V n → ℝ) (z ξ η : V n), ContDiffAt ℝ 2 u z → (∀ (x : V n) (c : ℂ), u (x + c • ξ) = u x) → ddc u z ξ η = 0 ∧ ddc u z η ξ = 0 := by
  intro n u z ξ η hu hinv
  have hinv' : ∀ (x : V n) (c : ℂ), (fun y => ((u y : ℝ) : ℂ)) (x + c • ξ) = (fun y => ((u y : ℝ) : ℂ)) x := by
    intro x c; simp only [hinv x c]
  have hdbar : (fun x => dbar (fun y => ((u y : ℝ) : ℂ)) x ξ) = fun _ => 0 := by
    funext x
    rw [dbar_apply]
    have h1 := fderiv_smul_eq_zero_of_invariant (fun y => ((u y : ℝ) : ℂ)) ξ hinv' x 1
    have h2 := fderiv_smul_eq_zero_of_invariant (fun y => ((u y : ℝ) : ℂ)) ξ hinv' x Complex.I
    rw [one_smul] at h1
    rw [h1, h2]; simp
  have hL1 : leviForm u z η ξ = 0 := by
    rw [leviForm_eq_del_dbar hu, hdbar, del_const]; rfl
  have hL2 : leviForm u z ξ η = 0 := by
    rw [← leviForm_conj_symm hu, hL1, map_zero]
  have e : ∀ a b, ddc u z a b = kappa * leviForm u z a b := fun a b => rfl
  exact ⟨by rw [e, hL2, mul_zero], by rw [e, hL1, mul_zero]⟩

end GlobalTheory
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.SqNum.NuCond

open GlobalTheory.Mem.Col2.SplitChar GlobalTheory.Mem.Chr

theorem levelLe_mono {K : Type} [Field K] [NumberField K] {χ : _root_.Formalism.L2.Host.HChar K} {v : HeightOneSpectrum (𝓞 K)} {a b : ℕ}
    (h : χ.LevelLe v a) (hab : a ≤ b) : χ.LevelLe v b :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hab))))

variable {D : D7}

theorem val_le_of_mem_pow {v : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ} {b : 𝓞 D.host.E} (hb : b ∈ v.asIdeal ^ n) :
    v.valuation D.host.E (b : D.host.E) ≤ WithZero.exp (-(n : ℤ)) := by
  show v.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) ≤ _
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_iff_mem]
  exact hb

theorem vl_le_of_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h𝔪 : ∀ b ∈ 𝔪, v.valuation D.host.E (b : D.host.E) ≤ WithZero.exp (-(n : ℤ))) {y : AE D} (hy : y ∈ hatId D 𝔪) :
    vl D v y ≤ WithZero.exp (-(n : ℤ)) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hx
    rw [map_mul, vl_inc]
    exact (mul_le_of_le_one_right' (vl_le hs v)).trans (h𝔪 b hb)
  | zero => rw [map_zero]; exact zero_le'
  | add x y _ _ hx hy => exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [Valuation.map_neg]

theorem condE_le {T : Type} {L : LevCh D T} (P : Places L) {s : HeightOneSpectrum (𝓞 D.host.F)} (hs : s ∈ P.S0) :
    condE P ≤ (P.w s).asIdeal ^ condExp P s :=
  Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hs)

end GlobalTheory.FunObj.SqNum.NuCond


open GlobalTheory.FunObj.SqNum.NuCond GlobalTheory.Mem.Col2.SplitChar in
theorem GlobalTheory.FunObj.SqNum.heckeU_nuInv_eq_one_of_cong : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) {N : ℕ} (χν : HeckeU D N), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → ∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) → χν.f u = 1 := by
  classical
  intro D T L sc μ₀ hL G i j N χν hχ u hu hm
  rw [hχ]
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  obtain ⟨n, hn⟩ : ∃ n : HeightOneSpectrum (𝓞 D.host.E) → ℕ, ∀ v, n v =
      if v.under (𝓞 D.host.F) ∈ G.pl.S0 then condExp G.pl (v.under (𝓞 D.host.F)) else 0 := ⟨_, fun _ => rfl⟩
  have hlev : ∀ v, (nuH G μ₀ i j).LevelLe v (n v) := by
    intro v
    have hμ := L.C.isMu0 j
    rw [show nuH G μ₀ i j = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) from rfl, hL.xi_base, mul_one, div_eq_mul_inv]
    refine Formalism.L2.Host.HChar.LevelLe.mul ?_ (Formalism.L2.Host.HChar.LevelLe.inv ?_)
    · by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · refine levelLe_mono (hμ.tame v) ?_
        rw [hn v, if_pos h, condExp]
        split_ifs <;> omega
      · refine Formalism.L2.Host.HChar.UnrAt.levelLe (hμ.unr v fun k hk => h ?_) _
        rw [G.pl.mem_S0_of_sum_eq]
        right
        rw [S1_mem_OmF]
        have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (v.under (𝓞 D.host.F)).asIdeal := by
          show _ ∈ v.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
          rw [Ideal.mem_comap, map_natCast]
          exact hk
        fin_cases k
        · exact Or.inl hk'
        · exact Or.inr (Or.inl hk')
    · by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · by_cases h0 : v.under (𝓞 D.host.F) = G.pl.v0
        · rw [hn v, if_pos h, condExp, if_pos h0]
          exact (G.ch.lev0 _ k1 k2 v h0).1
        · have h1 := (G.pl.mem_S0_of_sum_eq.1 h).resolve_left h0
          rw [hn v, if_pos h, condExp, if_neg h0]
          exact (G.ch.lev1 _ k1 k2 v h1).1
      · rw [hn v, if_neg h]
        exact Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ k1 k2 v h) 0
  have hval : ∀ v, vl D v ((u : AE D) - 1) ≤ WithZero.exp (-(n v : ℤ)) := by
    intro v
    by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
    · rw [hn v, if_pos h]
      refine vl_le_of_mem_hatId (fun b hb => ?_) hm
      have hw : (G.pl.w (v.under (𝓞 D.host.F))).under (𝓞 D.host.F) = v.under (𝓞 D.host.F) := G.pl.w_over _ h
      rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (G.pl.w (v.under (𝓞 D.host.F))) v).1 hw.symm with e | e
      · have hb1 : b ∈ condE G.pl := Ideal.mul_le_left hb
        have hb2 := condE_le G.pl h hb1
        rw [← e] at hb2
        exact val_le_of_mem_pow hb2
      · have hb1 : b ∈ D.host.conj • condE G.pl := Ideal.mul_le_right hb
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb1
        have hb2 := val_le_of_mem_pow (condE_le G.pl h hb1)
        have e2 := e (((D.host.conj⁻¹ • b : 𝓞 D.host.E)) : D.host.E)
        have e3 : c.toRingEquiv (((D.host.conj⁻¹ • b : 𝓞 D.host.E)) : D.host.E) = (b : D.host.E) := by
          show c _ = _
          rw [hc]
          show D.host.conj (D.host.conj⁻¹ (b : D.host.E)) = _
          exact AlgEquiv.apply_symm_apply _ _
        rw [e3] at e2
        rw [e2]
        exact hb2
    · rw [hn v, if_neg h, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact vl_le (sub_mem hu.1 (one_mem _)) v
  have hU := finIdl_unit hu
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j)⁻¹.2.1 (finIdl D u) hU
    (fun w => by rw [finIdl_fst]; rfl) (fun v x hx => ?_)
  have hxu : Formalism.L2.Host.IsUnitAt v x := by
    show Valued.v (x : v.adicCompletion D.host.E) = 1
    rw [hx]
    exact hU v
  refine (hlev v).inv x hxu ?_
  rw [hx, vl_sub_one]
  exact hval v

end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open scoped nonZeroDivisors

namespace GlobalTheory.FunObj.SqNum

theorem pt_mem_of_entries_mem (D : D7) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}
    (w : Matrix (Fin d) (Fin a) D.host.E) (hw : ∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) :
    pt D (tor0 D ⊤ δ) δ w ∈ La0 D (tor0 D ⊤ δ) a d ∧
      pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) := by
  have key : ∀ L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E), (∀ x ∈ stdL D a, w.mulVec x ∈ L') →
      pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) L' := by
    intro L' hL'
    refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, w, ?_, rfl⟩
    refine Submodule.subset_span ⟨1, ?_, w, Submodule.subset_span hL', (one_smul _ _).symm⟩
    refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  have hent : ∀ x ∈ stdL D a, ∀ i, w.mulVec x i ∈
      ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) := by
    intro x hx i
    show ∑ j, w i j * x j ∈ _
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨b, hb, hbw⟩ := hw i j
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hx j trivial)
    refine (FractionalIdeal.mem_coeIdeal _).2 ⟨b * y, 𝔪.mul_mem_right y hb, ?_⟩
    rw [hbw, ← hy, map_mul]
  refine ⟨key _ fun x hx i _ => ?_, key _ fun x hx i _ => ?_⟩
  · have := (FractionalIdeal.coe_le_coe.2 FractionalIdeal.coeIdeal_le_one) (hent x hx i)
    rw [FractionalIdeal.coe_one] at this
    exact this
  · by_cases h𝔪 : 𝔪 = ⊥
    · have := hent x hx i
      rw [h𝔪, FractionalIdeal.coeIdeal_bot] at this
      have h0 : w.mulVec x i = 0 := by simpa using this
      rw [h0]
      exact zero_mem _
    · have hne : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
        rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
        intro h
        apply h𝔪
        have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
        simpa using this
      have hle : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤
          (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
            ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
        rw [FractionalIdeal.le_div_iff_mul_le hne]
        first
        | exact mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one
        | exact mul_le_of_le_one_right (zero_le _) FractionalIdeal.coeIdeal_le_one
        | exact (mul_le_mul_left FractionalIdeal.coeIdeal_le_one _).trans_eq (mul_one _)
        | exact (FractionalIdeal.mul_le_mul_left FractionalIdeal.coeIdeal_le_one _).trans_eq (mul_one _)
        | exact (mul_le_mul_of_nonneg_left FractionalIdeal.coeIdeal_le_one (zero_le _)).trans_eq (mul_one _)
      exact (FractionalIdeal.coe_le_coe.2 hle) (hent x hx i)

end GlobalTheory.FunObj.SqNum
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.BadPlaceExp

theorem under_eq_of_isConjPl {D : D7} {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl w w') :
    w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  have le : (w.under (𝓞 D.host.F)).asIdeal ≤ (w'.under (𝓞 D.host.F)).asIdeal := by
    intro c hc
    obtain ⟨c', h1, h2⟩ := h _ hc
    have hs : star ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c : 𝓞 D.host.E) : D.host.E) := by
      letI := D.host.isCMField_hostE
      exact IsCMField.complexConj_apply_eq_self D.host.E (c : D.host.F)
    have : c' = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) c := RingOfIntegers.ext (h2.trans hs)
    show algebraMap _ _ c ∈ w'.asIdeal
    rwa [← this]
  exact HeightOneSpectrum.ext ((w.under (𝓞 D.host.F)).isMaximal.eq_of_le (w'.under (𝓞 D.host.F)).isPrime.ne_top le)

theorem main : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → IsBaseCond (condF G.pl) → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → ¬ (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ (q : 𝓞 D.host.E) ∉ w.asIdeal ^ 2 ∧ ExpAt (nuH G μ₀ i j) w 2 := by
  intro D T Lc sc G μ₀ hL hB i j t w hx hn
  have hm := Lc.C.isMu0 j
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have e : nuH G μ₀ i j = Lc.C.mu0 j / G.ch.chiH (D.R.m - i) := by
    rw [nuH, hL.xi_base, mul_one]
  have hE : ExpAt (nuH G μ₀ i j) w (expIn (condF G.pl) (w.under (𝓞 D.host.F))) := by
    rw [e]
    refine Model.expAt_div G a1 a2 hm.tame (fun Q hQ => hm.unr Q fun k hk => hQ ((S1_mem_OmF D).2 ?_)) w
    have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)
  have hS0 : w.under (𝓞 D.host.F) ∈ G.pl.S0 := by
    by_contra h
    rw [Model.expIn_condF, if_neg h] at hE
    exact hn ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 ((hE 0).2 le_rfl))
  have hv0 : w.under (𝓞 D.host.F) ≠ G.pl.v0 := by
    rcases (hL.Q_ram t w).1 hx with h | ⟨PP', hP', hc⟩
    · exact G.pl.levelPlace_ne_basePlace t w h
    · rw [← under_eq_of_isConjPl hc]; exact G.pl.levelPlace_ne_basePlace t PP' hP'
  have hc2 : condExp G.pl (w.under (𝓞 D.host.F)) = 2 := by rw [condExp, if_neg hv0]
  have h2 : expIn (condF G.pl) (w.under (𝓞 D.host.F)) = 2 := by
    rw [Model.expIn_condF, if_pos hS0, hc2]
  rw [h2] at hE
  have hdvd : (w.under (𝓞 D.host.F)).asIdeal ∣ condF G.pl :=
    (dvd_pow_self _ (by rw [hc2]; norm_num)).trans (Finset.dvd_prod_of_mem _ hS0)
  obtain ⟨-, -, hb⟩ := hB
  obtain ⟨-, -, l, hl, -, hlv, hdisc, hnorm⟩ := hb _ hdvd
  have hlw : (l : 𝓞 D.host.E) ∈ w.asIdeal := by
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ w.asIdeal := hlv
    rwa [map_natCast] at this
  refine ⟨l, hl, ?_, ?_, hE⟩
  · rw [← hnorm w hlw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · exact GlobalTheory.Mem.RaySplit.not_mem_sq hl hlw
      ((GlobalTheory.Mem.RaySplit.not_dvd_discr_iff_ramificationIdx D.host.E hl).1 hdisc _ w.isPrime hlw)

end GlobalTheory.BadPlaceExp
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

theorem _root_.GlobalTheory.T.bottomRanks_sum_le_two_exponent_add_centre : ∀ (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau), ((GlobalTheory.FunObj.SqNum.botBig D i j + GlobalTheory.FunObj.SqNum.botSmall D i j : ℕ) : ℤ) ≤ 2 * ((GlobalTheory.ChiGrid.num D C τ).e (j + 1) + GlobalTheory.ChiGrid.cen D C τ (D.R.m - i)) := by
  first | exact @GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen | exact GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen | (intros; apply GlobalTheory.ChiGrid.botBig_add_botSmall_le_two_e_add_two_cen <;> assumption)
end

section

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

theorem _root_.GlobalTheory.T.meanValuationNormOverDegree_smul_eq_add_valuation : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (u : K) (p q : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → GlobalTheory.FunObj.SqNum.IsMinPol σ (σ u * β) q → β ≠ 0 → u ≠ 0 → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, GlobalTheory.FunObj.SqNum.meanVal_vw w q = GlobalTheory.FunObj.SqNum.meanVal_vw w p + vw w u := by
  first | exact @GlobalTheory.FunObj.SqNum.meanVal_vw_smul | exact GlobalTheory.FunObj.SqNum.meanVal_vw_smul | (intros; apply GlobalTheory.FunObj.SqNum.meanVal_vw_smul <;> assumption)
end

section

open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

theorem _root_.GlobalTheory.T.valuation_minpoly_coeff_zero_ge_of_pow_mul_integral : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]) (l N : ℕ), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → l.Prime → GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ (N : ℤ) * β) → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, (l : 𝓞 K) ∈ w.asIdeal → -(((N * p.natDegree : ℕ) : ℤ) * vw w (l : K)) ≤ vw w (p.coeff 0) := by
  first | exact @GlobalTheory.FunObj.SqNum.LowVal.vw_coeff_zero_ge | exact GlobalTheory.FunObj.SqNum.LowVal.vw_coeff_zero_ge | (intros; apply GlobalTheory.FunObj.SqNum.LowVal.vw_coeff_zero_ge <;> assumption)
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
noncomputable section

namespace GlobalTheory.FunObj.SqNum

theorem exists_heckeU_alphaH : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ →
    ∀ (G : GridData L sc) (i j : Fin D.R.m), ∃ χ : HeckeU D (botSmall D i j),
      ∀ x, χ.f x = (alphaH L μ₀ i j).1 (finIdl D x) := by
  intro D T L sc μ₀ hL _ i j
  obtain ⟨χ₁, h1, -⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_of_isMu0 (N := 0) ⟨0, rfl⟩ (L.C.isMu0 j) fun g => (D.hc _).e_int j
  have hr := (ranks_exact D i j).2.1
  rcases Nat.mod_two_eq_zero_or_one (rankV D i j) with h | h
  · refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₁ (GlobalTheory.Mem.Col2.SplitChar.trivial D (N := 0) ⟨0, rfl⟩)
      (Int.even_iff.2 (by omega)), fun x => ?_⟩
    rw [GlobalTheory.AlphaSplit.mulU_f, h1]
    simp [alphaH, h, hL.xi_base, GlobalTheory.Mem.Col2.SplitChar.trivial]
  · refine ⟨GlobalTheory.AlphaSplit.mulU _ χ₁ (GlobalTheory.AlphaSplit.etaU L.C.isEta) (Int.even_iff.2 (by omega)), fun x => ?_⟩
    rw [GlobalTheory.AlphaSplit.mulU_f, h1, GlobalTheory.AlphaSplit.etaU_f]
    simp [alphaH, h, hL.xi_base]

end GlobalTheory.FunObj.SqNum
end
end

section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.crystalline_block_lattices_over_power_series_ring : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ (l : ℤ) ∣ NumberField.discr E → ∀ (σ : Equiv.Perm (E →+* PadicAlgCl l)), IsFrobPerm σ → ∀ (n t h : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), (∀ i a, 0 ≤ J i a ∧ J i a ≤ h) → (∀ i (s : Fin t), 0 ≤ bot i + ((s : ℕ) : ℤ) ∧ bot i + ((s : ℕ) : ℤ) ≤ h) → BlockPair E Ω l n t J bot → ∃ (O' F L' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : Algebra ℤ_[l] O') (_ : Field F) (_ : CharP F l) (_ : Field L') (I : Ideal O') (_ : IsAdicComplete I O') (Wl : Formalism.CohomologicalDescent.FrobeniusPeriodChange.WLat (E →+* PadicAlgCl l) t n O' F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (kap : (E →+* PadicAlgCl l) → Fin t → ℤ) (ζ : O') (em : O' →+* L') (jj : ℕ → PowerSeries O' →+* PowerSeries L'), Formalism.CohomologicalDescent.FrobeniusPeriodChange.NInputs Wl σ l h u c J (fun i s => bot i + ((s : ℕ) : ℤ)) kap I ζ em jj := by
  first | exact @GlobalTheory.WachBlock.wach_inputs | exact GlobalTheory.WachBlock.wach_inputs | (intros; apply GlobalTheory.WachBlock.wach_inputs <;> assumption)
end
