module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelBlockOfEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle676
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.UpIdeleMod

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteCompletionMap finiteCompletionMap_coe finiteCompletionMap_mapsTo)

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]


omit [NumberField K] in
theorem valued_algebraMap {R : Type} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  HeightOneSpectrum.adicCompletion.valued_coe K v k

theorem valued_finiteCompletionMap (w : HeightOneSpectrum (𝓞 E)) (x : (w.under (𝓞 K)).adicCompletion K) :
    Valued.v (finiteCompletionMap K E w x) =
      Valued.v x ^ ((w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal) := by
  have he : (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 K)).ne_bot
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero, map_zero, zero_pow he]
  have hx0 : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K (w.under (𝓞 K))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set m := WithZero.log (Valued.v x)
  set k : K := π ^ (-m)
  have hvk : (w.under (𝓞 K)).valuation K k = Valued.v x := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp only [smul_eq_mul, neg_mul_neg, mul_one]
    exact WithZero.exp_log hx0
  set c : (w.under (𝓞 K)).adicCompletion K := algebraMap K _ k
  have hc : Valued.v c = Valued.v x := (valued_algebraMap (w.under (𝓞 K)) k).trans hvk
  have hc0 : c ≠ 0 := fun h => hx0 (by rw [← hc, h, map_zero])
  set u := x * c⁻¹
  have hu0 : u ≠ 0 := mul_ne_zero hx (inv_ne_zero hc0)
  have hu : Valued.v u = 1 := by
    rw [map_mul, map_inv₀, hc, mul_inv_cancel₀ hx0]
  have hu1 : u ∈ (w.under (𝓞 K)).adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  have hu2 : u⁻¹ ∈ (w.under (𝓞 K)).adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, inv_one]
  have a1 := finiteCompletionMap_mapsTo K E w hu1
  have a2 := finiteCompletionMap_mapsTo K E w hu2
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at a1 a2
  have hfu : Valued.v (finiteCompletionMap K E w u) = 1 := by
    have hprod : finiteCompletionMap K E w u * finiteCompletionMap K E w u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
    have h3 := congrArg Valued.v hprod
    rw [map_mul, map_one] at h3
    exact eq_one_of_one_le_mul_left a1 a2 h3.ge
  have hxu : x = u * c := by
    simp only [u, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  conv_lhs => rw [hxu, map_mul, map_mul, hfu, one_mul, finiteCompletionMap_coe, valued_algebraMap,
    ← HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 K)) w k, hvk]
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 K)).ne_bot]

theorem factor_upIdele (t : (Af K)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ WithZero.log (Valued.v ((upIdele K E t : Af E) w)) =
      (((Ideal.absNorm (w.under (𝓞 K)).asIdeal : ℕ) : ℝ) ^
          WithZero.log (Valued.v ((t : Af K) (w.under (𝓞 K))))) ^
        (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
  haveI := w.isMaximal
  haveI := (w.under (𝓞 K)).isMaximal
  have h1 : ((upIdele K E t : Af E) w) = finiteCompletionMap K E w ((t : Af K) (w.under (𝓞 K))) := rfl
  rw [h1, valued_finiteCompletionMap, WithZero.log_pow,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 K)).ne_bot,
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.under (𝓞 K)).asIdeal (w.under (𝓞 K)).isPrime
      (w.under (𝓞 K)).ne_bot,
    Ideal.inertiaDeg'_eq_inertiaDeg]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring


open Classical in
theorem sum_fiber (v : HeightOneSpectrum (𝓞 K)) (s : Finset (HeightOneSpectrum (𝓞 E)))
    (hs : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 K) = v → w ∈ s) :
    ∑ w ∈ s with w.under (𝓞 K) = v, w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) =
      Module.finrank K E := by
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E, ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine Finset.sum_bij'
    (fun w hw => (⟨w.asIdeal, w.isPrime, by
      rw [← (Finset.mem_filter.mp hw).2]
      exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under K E w⟩ : v.asIdeal.primesOver (𝓞 E)))
    (fun q _ => (⟨q.1, q.2.1, by
      haveI := q.2.2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1⟩ : HeightOneSpectrum (𝓞 E)))
    (fun _ _ => Finset.mem_univ _) (fun q _ => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hq : (⟨q.1, q.2.1, by
      haveI := q.2.2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 K) = v :=
    HeightOneSpectrum.ext q.2.2.over.symm
  exact Finset.mem_filter.mpr ⟨hs _ hq, hq⟩

theorem modF_upIdele (t : (Af K)ˣ) : modF (upIdele K E t) = modF t ^ Module.finrank K E := by
  classical
  set a : HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ WithZero.log (Valued.v ((t : Af K) v)) with ha
  have hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}.Finite :=
    Filter.eventually_cofinite.mp (FiniteAdeleRing.isUnit_iff.mp t.isUnit).2
  have hT : ((fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 K)) ⁻¹'
      {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}).Finite := by
    have h2 := Filter.mem_cofinite.mp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K E hfin.compl_mem_cofinite)
    rwa [Set.preimage_compl, compl_compl] at h2
  set S := hfin.toFinset
  set T := hT.toFinset
  have haS : ∀ v, v ∉ S → a v = 1 := fun v hv => by
    have h3 : Valued.v ((t : Af K) v) = 1 := by
      by_contra h
      exact hv (hfin.mem_toFinset.mpr h)
    simp only [ha, h3, WithZero.log_one, zpow_zero]
  have h1 : modF t = ∏ v ∈ S, a v := by
    refine finprod_eq_prod_of_mulSupport_subset a fun v hv => ?_
    by_contra h
    exact hv (haS v h)
  have h2 : modF (upIdele K E t) = ∏ w ∈ T, a (w.under (𝓞 K)) ^
      (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
    unfold modF
    rw [finprod_congr (factor_upIdele t)]
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw => ?_
    by_contra h
    apply hw
    have h4 : w.under (𝓞 K) ∉ S := fun h5 => h (hT.mem_toFinset.mpr (hfin.mem_toFinset.mp h5))
    show a (w.under (𝓞 K)) ^ _ = 1
    rw [haS _ h4, one_pow]
  rw [h2, h1, ← Finset.prod_fiberwise_of_maps_to (s := T) (t := S) (g := fun w => w.under (𝓞 K))
    (fun w hw => hfin.mem_toFinset.mpr (hT.mem_toFinset.mp hw)), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Finset.prod_congr rfl (g := fun w => a v ^ (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)))
      (fun w hw => by rw [(Finset.mem_filter.mp hw).2]),
    Finset.prod_pow_eq_pow_sum, sum_fiber v T fun w hw => hT.mem_toFinset.mpr (by
      show w.under (𝓞 K) ∈ {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}
      rw [hw]; exact hfin.mem_toFinset.mp hv)]

end GlobalTheory.UpIdeleMod
end
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix

namespace GlobalTheory.PullBdd

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem castFrame_mem_GG {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {G : Matrix (Fin r) (Fin r) E}
    {p0 : ℕ} {x : Frame Ψ r} (hx : x ∈ GG Ψ G p0) : castFrame h x ∈ GG Ψ' G p0 := by
  subst h; exact hx

theorem castFrame_mem_Bor {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) : castFrame h b ∈ Bor Ψ' r := by
  subst h; exact hb

theorem bchar_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (la : Wt Ψ' r) (b : Frame Ψ r) :
    bchar la (castFrame h b) = bchar (castWt h la) b := by
  subst h; rfl

theorem castFrame_rmul {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x b : Frame Ψ r) :
    castFrame h (rmul x b) = rmul (castFrame h x) (castFrame h b) := rfl

theorem castFrame_lact {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (β : GL (Fin r) E) (x : Frame Ψ r) :
    castFrame h (lact β x) = lact β (castFrame h x) := rfl

theorem lact_rmul {Ψ : Finset (E →+* ℂ)} (β : GL (Fin r) E) (x b : Frame Ψ r) :
    lact β (rmul x b) = rmul (lact β x) b := by
  funext τ
  show ((β : Matrix (Fin r) (Fin r) E).map τ.1 * (mat x τ * mat b τ) : Matrix (Fin r) (Fin r) ℂ) =
    (β : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ
  rw [Matrix.mul_assoc]

theorem lact_lact {Ψ : Finset (E →+* ℂ)} (β γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact β (lact γ x) = lact (β * γ) x := by
  funext τ
  show ((β : Matrix (Fin r) (Fin r) E).map τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
      Matrix (Fin r) (Fin r) ℂ) =
    ((↑(β * γ) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

theorem dmin_lact {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {β : GL (Fin r) E}
    (hβ : ∀ u v, herm G ((β : Matrix (Fin r) (Fin r) E) *ᵥ u) ((β : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm G u v) (x : Frame Ψ r) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G (lact β x) τ i = dmin G x τ i := by
  have e1 : mat (lact β x) τ = (β : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have e2 : gram τ.1 G (mat (lact β x) τ) = gram τ.1 G (mat x τ) := by
    ext a b
    simp only [gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hβ]
  unfold dmin
  rw [e2]

theorem nfac_cast {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (G : Matrix (Fin r) (Fin r) E)
    (la : Wt Ψ' r) (x : Frame Ψ r) :
    (∏ τ : Ψ', ∏ i : Fin r, ‖dmin G (castFrame h x) τ i.succ / dmin G (castFrame h x) τ i.castSucc‖ ^
      (-(la τ i : ℝ) / 2)) =
    ∏ τ : Ψ, ∏ i : Fin r, ‖dmin G x τ i.succ / dmin G x τ i.castSucc‖ ^
      (-(castWt h la τ i : ℝ) / 2) := by
  subst h; rfl

theorem isBddSec_transport (X Y : Data E r) (hΨ : X.Ψ = Y.Ψ) (hG : X.Gm = Y.Gm) (hp : X.p0 = Y.p0)
    (β : GL (Fin r) E)
    (hβ : ∀ u v, herm Y.Gm ((β : Matrix (Fin r) (Fin r) E) *ᵥ u) ((β : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm Y.Gm u v)
    (hΓ : ∀ γ ∈ X.Γ, β * γ * β⁻¹ ∈ Y.Γ) (la : Wt Y.Ψ r)
    (hχX : ∀ γ ∈ X.Γ, X.χ (castWt hΨ la) γ = 1) (hχY : ∀ γ ∈ Y.Γ, Y.χ la γ = 1)
    (Q : Frame Y.Ψ r → ℂ) (hQ : Y.IsBddSec la Q) :
    X.IsBddSec (castWt hΨ la) (fun x => Q (lact β (castFrame hΨ x))) := by
  obtain ⟨⟨hQd, hQB, hQΓ⟩, C, hC⟩ := hQ
  have hmaps : ∀ x ∈ X.dom, lact β (castFrame hΨ x) ∈ Y.dom := by
    intro x hx
    have h1 := castFrame_mem_GG hΨ hx
    rw [hG, hp] at h1
    exact GlobalTheory.FrameFibre.lact_mem_GG hβ h1
  refine ⟨⟨?_, ?_, ?_⟩, C, fun x hx => ?_⟩
  · have hd : Differentiable ℂ (fun x : Frame X.Ψ r => lact β (castFrame hΨ x)) := by
      rw [differentiable_pi]; intro τ; rw [differentiable_pi]; intro a; rw [differentiable_pi]; intro b
      simp only [lact, castFrame, mat, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
      fun_prop
    exact hQd.comp hd.differentiableOn hmaps
  · intro x hx b hb
    simp only
    rw [castFrame_rmul, lact_rmul, hQB _ (hmaps x hx) _ (castFrame_mem_Bor hΨ hb), bchar_castFrame]
  · intro γ hγ x hx
    simp only
    rw [hχX γ hγ, one_mul, castFrame_lact, lact_lact,
      show β * γ = (β * γ * β⁻¹) * β by group, ← lact_lact, hQΓ _ (hΓ γ hγ) _ (hmaps x hx),
      hχY _ (hΓ γ hγ), one_mul]
  · refine le_trans (le_of_eq ?_) (hC _ (hmaps x hx))
    unfold Data.pnorm
    congr 1
    simp only [dmin_lact hβ]
    rw [← hG]
    exact (nfac_cast hΨ X.Gm la x).symm

end

theorem pull_isBddSec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type)
    [Group U] [MulAction U C] (M : TwoLevels E r U C) (la : Wt M.Ψ r) (F : C → Frame M.Ψ r → ℂ),
    F ∈ M.SS la → ∀ (h : U) (c : C),
      (M.comp c).IsBddSec (castWt (M.comp_Ψ c) la) (fun x => M.pull h F c (castFrame (M.comp_Ψ c) x)) := by
  intro E _ _ _ r U C _ _ M la F hF h c
  have hY := (hF (h • c)).1
  exact isBddSec_transport (M.comp c).toData (M.comp (h • c)).toData
    ((M.comp_Ψ c).trans (M.comp_Ψ (h • c)).symm) (by rw [M.comp_Gm, M.comp_Gm])
    (by rw [M.comp_basePoint, M.comp_basePoint]) (M.tr h c) (by rw [M.comp_Gm]; exact M.tr_herm h c)
    (fun γ hγ => (M.tr_conj h c γ).1 hγ) (castWt (M.comp_Ψ (h • c)) la)
    (fun γ hγ => M.χ_one c _ γ hγ) (fun γ hγ => M.χ_one (h • c) _ γ hγ) _ hY

end GlobalTheory.PullBdd
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullDegSymm

section Bundle

variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

theorem base_cancel {G : X ⟶ X'} (h : G ≫ F = 𝟙 X) (x : X) : F (G x) = x := by
  have := congrArg (fun f : X ⟶ X => f x) h
  exact this

theorem le_rev {G : X ⟶ X'} (h : G ≫ F = 𝟙 X) (p : (LB.div (L'.pull G) L).ι) :
    (LB.div (L'.pull G) L).U p ≤ G ⁻¹ᵁ ((L.pull F).U (fun _ => p.2) ⊓ L'.U (p.1 PUnit.unit)) :=
  fun x hx => ⟨mem_pull.2 (by rw [base_cancel h]; exact hx.2), mem_pull.1 hx.1⟩

def revIso (w : LB.Iso L' (L.pull F)) (G : X ⟶ X') (h : G ≫ F = 𝟙 X) : LB.Iso L (L'.pull G) :=
  ⟨fun p => (res (le_rev h p) (pullU G _ (w.s (fun _ => p.2, p.1 PUnit.unit))))⁻¹⟩

theorem gw_revIso (w : LB.Iso L' (L.pull F)) {G : X ⟶ X'} (h : G ≫ F = 𝟙 X) {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z)
    (j' : L'.ι) (j : L.ι) (h₁ : G (f z) ∈ L'.U j') (h₂ : f z ∈ L.U j) :
    gw (revIso w G h) f z j' j = (gw w (f ≫ G) z j j')⁻¹ := by
  have hm : f z ∈ (LB.div (L'.pull G) L).U (fun _ => j', j) := ⟨mem_pull.2 h₁, h₂⟩
  exact (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res f z _ hm _).trans (gm_pull f G z _ (le_rev h _ hm) _)))

theorem revIso_isGen (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) {G : X ⟶ X'} (h : G ≫ F = 𝟙 X) :
    (revIso w G h).IsGen := by
  refine (isGen_iff _).2 fun Z f z j j' k k' hj hj' hk hk' => ?_
  have hp := (isGen_iff w).1 hw Z (f ≫ G) z k k' j j' (show F (G (f z)) ∈ _ by rw [base_cancel h]; exact hk)
    (show F (G (f z)) ∈ _ by rw [base_cancel h]; exact hk') hj hj'
  have e : (f ≫ G) ≫ F = f := by rw [Category.assoc, h, Category.comp_id]
  rw [e] at hp
  rw [gw_revIso w h f z j k hj hk, gw_revIso w h f z j' k' hj' hk', hp]
  simp only [mul_inv, inv_inv]
  ac_rfl

theorem carriesAt_iff (w : LB.Iso L' (L.pull F)) (p' : Y ⟶ X') (p : Y ⟶ X) (hp : p' ≫ F = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p') (fun _ => n)))
    (b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    CarriesAt L L' F w p' p hp n a b ↔ ∀ (y : Y) (j : L.ι) (j' : L'.ι), F (p' y) ∈ L.U j → p' y ∈ L'.U j' →
      gm (𝟙 Y) y _ (b.s (fun _ => j)) = gw w p' y j j' ^ n * gm (𝟙 Y) y _ (a.s (fun _ => j')) := by
  constructor
  · intro H y j j' h₁ h₂
    have hm : y ∈ p' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') := ⟨mem_pull.2 h₁, h₂⟩
    have e := congrArg (gm (𝟙 Y) y _) (H j j')
    refine (gm_res _ y _ hm _).symm.trans (e.trans ?_)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ n) ?_)) (gm_res _ y _ hm _))
    exact (gm_pull _ _ y _ hm _).trans (by rw [Category.id_comp]; rfl)
  · intro H j j'
    apply unit_ext
    intro y hm
    refine (gm_res _ y _ hm _).trans ((H y j j' (mem_pull.1 hm.1) hm.2).trans ?_)
    refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ n) ?_)) (gm_res _ y _ hm _)))
    exact (gm_pull _ _ y _ hm _).trans (by rw [Category.id_comp]; rfl)

theorem carriesAt_rev (w : LB.Iso L' (L.pull F)) {G : X ⟶ X'} (h : G ≫ F = 𝟙 X) {p' : Y ⟶ X'} {p : Y ⟶ X}
    (hp : p' ≫ F = p) (hq : p ≫ G = p') (n : ℤ)
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p') (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))}
    (H : CarriesAt L L' F w p' p hp n a b) : CarriesAt L' L G (revIso w G h) p p' hq n b a := by
  rw [carriesAt_iff] at H ⊢
  intro y j' j h₁ h₂
  have e₁ : p' y = G (p y) := congrArg (fun f : Y ⟶ X' => f y) hq.symm
  have e₂ : F (p' y) = p y := congrArg (fun f : Y ⟶ X => f y) hp
  have := H y j j' (by rw [e₂]; exact h₂) (by rw [e₁]; exact h₁)
  rw [gw_revIso w h p y j' j h₁ h₂, hq, this, inv_zpow, inv_mul_cancel_left]

end Bundle

section Grp

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}

theorem specOf_id' : GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) = 𝟙 _ := Spec.map_id _

instance isIso_F (p : PullIdent (RingHom.id R) D D') : IsIso p.F := by
  have : IsIso (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) := by rw [specOf_id']; infer_instance
  exact MorphismProperty.of_isPullback (P := .isomorphisms _) p.cart.flip this

abbrev Finv (p : PullIdent (RingHom.id R) D D') : D.P.A.left ⟶ D'.P.A.left := inv p.F

theorem Finv_F (p : PullIdent (RingHom.id R) D D') : Finv p ≫ p.F = 𝟙 _ := IsIso.inv_hom_id _

theorem cart' (p : PullIdent (RingHom.id R) D D') :
    IsPullback (Finv p) D.P.A.hom D'.P.A.hom (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) := by
  have : IsIso (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) := by rw [specOf_id']; infer_instance
  refine IsPullback.of_horiz_isIso ⟨?_⟩
  have w := p.cart.w
  rw [specOf_id', Category.comp_id] at w
  rw [IsIso.inv_comp_eq, specOf_id', Category.comp_id, w]

theorem F_one' (p : PullIdent (RingHom.id R) D D') :
    eSec D.P.A ≫ Finv p = GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D'.P.A := by
  have e := p.F_one
  rw [specOf_id', Category.id_comp] at e
  rw [specOf_id', Category.id_comp, IsIso.comp_inv_eq, e]

theorem F_mul' (p : PullIdent (RingHom.id R) D D') : (μ[D.P.A]).left ≫ Finv p =
    pullback.map D.P.A.hom D.P.A.hom D'.P.A.hom D'.P.A.hom (Finv p) (Finv p) (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R))
      (cart' p).w.symm (cart' p).w.symm ≫ (μ[D'.P.A]).left := by
  rw [IsIso.comp_inv_eq, Category.assoc, p.F_mul, ← Category.assoc]
  have key : pullback.map D.P.A.hom D.P.A.hom D'.P.A.hom D'.P.A.hom (Finv p) (Finv p)
      (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) (cart' p).w.symm (cart' p).w.symm ≫
      pullback.map D'.P.A.hom D'.P.A.hom D.P.A.hom D.P.A.hom p.F p.F (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R))
        p.cart.w.symm p.cart.w.symm = 𝟙 _ := by
    apply pullback.hom_ext
    · erw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, Category.assoc, Finv_F, Category.comp_id]
    · erw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.assoc, Finv_F, Category.comp_id]
  rw [key]
  exact (Category.id_comp _).symm

theorem c_eq' (p : PullIdent (RingHom.id R) D D') (χ : D.X) :
    (D.c χ).left ≫ Finv p = GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ (D'.c (p.xe.symm χ)).left := by
  have e := p.c_eq (p.xe.symm χ)
  rw [AddEquiv.apply_symm_apply, specOf_id', Category.id_comp] at e
  rw [specOf_id', Category.id_comp, IsIso.comp_inv_eq, e]

abbrev wInv (p : PullIdent (RingHom.id R) D D') : LB.Iso D.P.L (D'.P.L.pull (Finv p)) :=
  revIso p.w (Finv p) (Finv_F p)

theorem wInv_isGen (p : PullIdent (RingHom.id R) D D') : (wInv p).IsGen := revIso_isGen p.w p.w_gen _

theorem w_rig' (p : PullIdent (RingHom.id R) D D') :
    CarriesAt D'.P.L D.P.L (Finv p) (wInv p) (eSec D.P.A) (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D'.P.A)
      (F_one' p) 1 D.rig (LB.pullGen D'.P.L _ _ D'.rig (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R))) := by
  have es : GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D.P.A = eSec D.P.A := by
    rw [specOf_id', Category.id_comp]
  have es' : GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D'.P.A = eSec D.P.A ≫ Finv p := (F_one' p).symm
  have hq : (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D.P.A) ≫ Finv p = eSec D'.P.A := by
    rw [es, F_one' p, specOf_id', Category.id_comp]
  have H := carriesAt_rev p.w (Finv_F p) p.F_one hq 1 p.w_rig
  have h1 : 𝟙 (Spec (CommRingCat.of R)) ≫ GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) = 𝟙 (Spec (CommRingCat.of R)) := by
    rw [specOf_id', Category.id_comp]
  rw [carriesAt_iff] at H ⊢
  intro y j j' h₁ h₂
  have m₁ : Finv p ((GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D.P.A) y) ∈ D'.P.L.U j := by rw [es]; exact h₁
  have m₂ : (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R) ≫ eSec D.P.A) y ∈ D.P.L.U j' := by rw [es]; exact h₂
  have e := H y j j' m₁ m₂
  have a₁ := gm_pullGen D'.P.L _ _ D'.rig (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) (𝟙 (Spec (CommRingCat.of R))) y
    (fun _ => j) (Set.mem_iInter.2 fun _ => (congrArg (fun f => f y ∈ D'.P.L.U j) es').mpr h₁)
  have a₂ := gm_pullGen D.P.L _ _ D.rig (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) (𝟙 (Spec (CommRingCat.of R))) y
    (fun _ => j') (Set.mem_iInter.2 fun _ => m₂)
  rw [h1] at a₁ a₂
  exact a₁.trans (e.trans (congrArg₂ (· * ·) (by rw [es]) a₂))

end Grp

end GlobalTheory.PullDegSymm
end
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef


theorem _root_.GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension : ∀ (k F E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Field E] [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E] [FiniteDimensional F E], IsFF k F →
  ∀ ρ : Place k E → Place k F, IsRes ρ → ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → admitted (pullAd ρ g) ∧ deg (pullAd ρ g) = Module.finrank F E * deg g ∧ (∀ w : Fin n → F, w ≠ 0 → degLine (pullAd ρ g) (fun i => algebraMap F E (w i)) = Module.finrank F E * degLine g w) ∧ ∀ b : ℝ, LinesLE g b → LinesLE (pullAd ρ g) (b * Module.finrank F E) := by
  first | exact @GlobalTheory.Nef.PullAd.adm_pullAd_and_deg_mul_finrank | exact GlobalTheory.Nef.PullAd.adm_pullAd_and_deg_mul_finrank | (intros; apply GlobalTheory.Nef.PullAd.adm_pullAd_and_deg_mul_finrank <;> assumption)
end
