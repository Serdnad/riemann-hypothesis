module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

theorem GlobalTheory.WeierstrassCurve.isAbelianScheme_schemeOver :
    ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R), IsUnit W.Δ →
      ∀ [GrpObj (schemeOver W)], IsCommMonObj (schemeOver W) → IsAbelianScheme (schemeOver W) := by
  intro R _ W hΔ _ hc
  have hs := smoothOfRelativeDimension_toSpec_of_isUnit W hΔ
  exact ⟨hc, SmoothOfRelativeDimension.smooth 1 (toSpec W), isProper_toSpec W,
    geometricallyConnected_toSpec W⟩
end

section

open NumberField IsDedekindDomain Formalism.L2.LamCM WithZero
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

section

variable {K : Type} [Field K] [NumberField K]

theorem det_of_smul_rows {n : ℕ} (s : Fin n → 𝓞 K) (x : Fin n → Fin n → K) :
    (Matrix.of fun i => s i • x i).det = (∏ i, s i) • (Matrix.of x).det := by
  have h : (Matrix.of fun i => s i • x i) =
      Matrix.of fun i j => algebraMap (𝓞 K) K (s i) * (Matrix.of x) i j := by
    ext i j
    simp [Algebra.smul_def]
  rw [h, Matrix.det_mul_column, Algebra.smul_def, map_prod]


omit [NumberField K] in
theorem prod_notMem_asIdeal {n : ℕ} (p : HeightOneSpectrum (𝓞 K)) (s : Fin n → 𝓞 K)
    (hs : ∀ i, s i ∉ p.asIdeal) : ∏ i, s i ∉ p.asIdeal := by
  haveI := p.isPrime
  exact prod_mem (S := p.asIdeal.primeCompl) fun i _ => hs i

theorem valuation_smul_of_notMem (p : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ p.asIdeal) (c : K) :
    p.valuation K (s • c) = p.valuation K c := by
  have h1 : p.valuation K (algebraMap (𝓞 K) K s) = 1 := by
    refine le_antisymm (p.valuation_le_one s) (not_lt.1 fun hlt => hs ?_)
    exact (p.valuation_lt_one_iff_mem s).1 hlt
  rw [Algebra.smul_def, map_mul, h1, one_mul]

theorem valuation_smul_le (p : HeightOneSpectrum (𝓞 K)) (s : 𝓞 K) (c : K) :
    p.valuation K (s • c) ≤ p.valuation K c := by
  rw [Algebra.smul_def, map_mul]
  exact mul_le_of_le_one_left' (p.valuation_le_one s)

end

theorem exists_detIdeal_isLocGen : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
    (Λ : Submodule (𝓞 K) (Fin n → K)), Λ.FG → Submodule.span K (Λ : Set (Fin n → K)) = ⊤ →
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧
      ∀ (p : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin n) (Fin n) K),
        (∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • M i ∈ Λ) →
        (∀ c ∈ Λ, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i)) →
        IsLocGen p M.det I := by
  intro K _ _ n Λ hfg hspan
  let L : MLat K n := MLat.mk Λ (fun _ => 0)
  have hcoe : (L.detIdeal : Submodule (𝓞 K) K) = L.detSub :=
    A2.detIdeal_coe L (A2.detSub_isFractional L hfg)
  have hmem : ∀ y : K, y ∈ L.detIdeal ↔ y ∈ L.detSub := fun y => by
    rw [← hcoe]; rfl
  have hI : L.detIdeal ≠ 0 := by
    obtain ⟨x, hx, hd⟩ := A2.exists_det_ne Λ hspan
    intro h0
    have h := (hmem _).2 (A2.det_mem L x hx)
    rw [h0] at h
    exact hd ((FractionalIdeal.mem_zero_iff _).1 h)
  refine ⟨L.detIdeal, hI, fun p M h1 h2 => ?_⟩
  refine (isLocGen_iff_valuation_eq p _ _).2 (le_antisymm ?_ ?_)
  · choose s hs hsM using h1
    refine (valuation_le_iff_exists_smul_mem p hI _).2 ⟨∏ i, s i, prod_notMem_asIdeal p s hs, ?_⟩
    have h := A2.det_mem L (fun i => s i • M i) hsM
    rw [det_of_smul_rows s (fun i => M i)] at h
    exact (hmem _).2 h
  · obtain ⟨y, hy, hv⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI p
    rw [← hv]
    have hy' := (hmem y).1 hy
    clear hv hy
    induction hy' using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨x, hx, rfl⟩ := hd
      choose s hs hsx using fun i => h2 (x i) (hx i)
      let L' : MLat K n := MLat.mk (Submodule.span (𝓞 K) (Set.range fun i => M i)) (fun _ => 0)
      have h := A2.det_mem L' (fun i => s i • x i) hsx
      rw [A2.detSub_free L' (fun i => M i) rfl, det_of_smul_rows, Submodule.mem_span_singleton] at h
      obtain ⟨r, hr⟩ := h
      rw [← valuation_smul_of_notMem p (prod_notMem_asIdeal p s hs), ← hr]
      exact valuation_smul_le p r _
    | zero => simp
    | add a b _ _ ha hb => exact (Valuation.map_add _ a b).trans (max_le ha hb)
    | smul r a _ ha => exact (valuation_smul_le p r a).trans ha

end GlobalTheory.LamF
end

section

open NumberField IsDedekindDomain Formalism.L2.LamCM
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

theorem exists_fractionalIdeal_isLocGen_of_valuation : ∀ (K : Type) [Field K] [NumberField K]
    (oa : HeightOneSpectrum (𝓞 K) → ℤ), (Function.support oa).Finite →
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧
      ∀ (p : HeightOneSpectrum (𝓞 K)) (a : K), p.valuation K a = WithZero.exp (-oa p) → IsLocGen p a I := by
  intro K _ _ oa hfin
  refine ⟨∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ oa v, ?_, fun p a ha => ?_⟩
  · refine finprod_induction (fun L : FractionalIdeal (𝓞 K)⁰ K => L ≠ 0) one_ne_zero
      (fun _ _ h h' => mul_ne_zero h h') fun v => ?_
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
  · rw [isLocGen_iff_valuation_eq, FractionalIdeal.count_finprod K p oa, ha]
    exact hfin

end GlobalTheory.LamF
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SameZeroScheme

theorem resG_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((f.appLE U V h).hom a) = (f.appLE U W (h'.trans h)).hom a := by
  change (f.appLE U V h ≫ Y.presheaf.map (homOfLE h').op).hom a = _
  rw [Scheme.Hom.appLE_map]

theorem appLE_resG {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (h' : U ≤ U') (h'' : V ≤ f ⁻¹ᵁ U') (a : Γ(X, U')) :
    (f.appLE U V h).hom (resG X h' a) = (f.appLE U' V h'').hom a := by
  change (X.presheaf.map (homOfLE h').op ≫ f.appLE U V h).hom a = _
  rw [Scheme.Hom.map_appLE]

theorem appLE_appLE {X Y T : Scheme.{0}} (t : T ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ t ⁻¹ᵁ V) (h'' : ⊤ ≤ (t ≫ f) ⁻¹ᵁ U) (a : Γ(X, U)) :
    (t.appLE V ⊤ h').hom ((f.appLE U V h).hom a) = ((t ≫ f).appLE U ⊤ h'').hom a := by
  change (f.appLE U V h ≫ t.appLE V ⊤ h').hom a = _
  rw [Scheme.Hom.appLE_comp_appLE]

theorem appLE_compat {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (f : Y ⟶ X) (i j : L.ι) {W : Y.Opens}
    (hi : W ≤ f ⁻¹ᵁ L.U i) (hj : W ≤ f ⁻¹ᵁ L.U j) (hij : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U j)) :
    (f.appLE (L.U i) W hi).hom (θ.f i) =
      (res hij (pullU f (L.U i ⊓ L.U j) (L.g i j)) : Γ(Y, W)ˣ) * (f.appLE (L.U j) W hj).hom (θ.f j) := by
  have e := congrArg (f.appLE (L.U i ⊓ L.U j) W hij).hom (θ.compat i j)
  rw [map_mul] at e
  exact (appLE_resG f hij inf_le_left hi _).symm.trans
    (e.trans (congrArg₂ (· * ·) rfl (appLE_resG f hij inf_le_right hj _)))

theorem unit_eq_of_mul {R : Type*} [CommRing R] {a a' b b' : R} {c c' g₀ g₁ : Rˣ}
    (ha : a ∈ nonZeroDivisors R) (h : b = c * a) (h' : b' = c' * a') (hb : b = g₀ * b')
    (haa : a = g₁ * a') : c = g₀ ^ (1 : ℤ) * g₁ ^ (-1 : ℤ) * c' := by
  apply Units.ext
  apply (mul_cancel_right_mem_nonZeroDivisors ha).1
  rw [← h, hb, h', zpow_one, zpow_neg_one, haa]
  have := g₁.inv_mul
  push_cast
  linear_combination (-(g₀ * c' * a' : R)) * this

theorem exists_isGen_linComb : ∀ (X Y : Scheme.{0}) (L : LB X) (θ : L.Sec) (φ ψ : Y ⟶ X), L.IsLB → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ L.U i), (φ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (i : L.ι) (V : Y.Opens) (h : V ≤ ψ ⁻¹ᵁ L.U i), (ψ.appLE (L.U i) V h).hom (θ.f i) ∈ nonZeroDivisors Γ(Y, V)) → (∀ (T : Scheme.{0}) (t : T ⟶ Y) (i j : L.ι) (h : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ L.U i) (h' : ⊤ ≤ (t ≫ ψ) ⁻¹ᵁ L.U j), ((t ≫ φ).appLE (L.U i) ⊤ h).hom (θ.f i) = 0 ↔ ((t ≫ ψ).appLE (L.U j) ⊤ h').hom (θ.f j) = 0) → ∃ t : LB.Gen (LB.LinComb L (K := Fin 2) ![φ, ψ] ![1, -1]), t.IsGen := by
  intro X Y L θ φ ψ _ _ hψ H
  have h0 : ∀ j : Fin 2 → L.ι, L.wchart ![φ, ψ] j ≤ φ ⁻¹ᵁ L.U (j 0) :=
    fun j => LB.wchart_le L ![φ, ψ] j 0
  have h1 : ∀ j : Fin 2 → L.ι, L.wchart ![φ, ψ] j ≤ ψ ⁻¹ᵁ L.U (j 1) :=
    fun j => LB.wchart_le L ![φ, ψ] j 1
  have hc : ∀ j : Fin 2 → L.ι, ∃ c : Γ(Y, L.wchart ![φ, ψ] j)ˣ,
      (φ.appLE _ _ (h0 j)).hom (θ.f (j 0)) = c * (ψ.appLE _ _ (h1 j)).hom (θ.f (j 1)) := by
    intro j
    apply exists_unit_mul
    · intro V' h
      rw [resG_appLE]
      exact hψ _ _ _
    · intro T t h
      have k0 : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ L.U (j 0) := fun x hx => h0 j (h hx)
      have k1 : ⊤ ≤ (t ≫ ψ) ⁻¹ᵁ L.U (j 1) := fun x hx => h1 j (h hx)
      rw [appLE_appLE t φ _ h k0, appLE_appLE t ψ _ h k1]
      exact (H T t _ _ k0 k1).symm
  choose c hc using hc
  refine ⟨⟨c⟩, fun i j => ?_⟩
  let W : Y.Opens := L.wchart ![φ, ψ] i ⊓ L.wchart ![φ, ψ] j
  have wi : W ≤ L.wchart ![φ, ψ] i := inf_le_left
  have wj : W ≤ L.wchart ![φ, ψ] j := inf_le_right
  have ei := congrArg (resG Y wi) (hc i)
  have ej := congrArg (resG Y wj) (hc j)
  rw [map_mul, resG_appLE, resG_appLE] at ei ej
  have p0 : W ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)) := le_inf (wi.trans (h0 i)) (wj.trans (h0 j))
  have p1 : W ≤ ψ ⁻¹ᵁ (L.U (i 1) ⊓ L.U (j 1)) := le_inf (wi.trans (h1 i)) (wj.trans (h1 j))
  have key := unit_eq_of_mul (c := res wi (c i)) (c' := res wj (c j)) (hψ _ _ _) ei ej
    (appLE_compat θ φ (i 0) (j 0) _ _ p0) (appLE_compat θ ψ (i 1) (j 1) _ _ p1)
  refine key.trans ?_
  congr 1
  exact (Fin.prod_univ_two (fun k : Fin 2 => (res (le_inf (wi.trans (LB.wchart_le L ![φ, ψ] i k))
    (wj.trans (LB.wchart_le L ![φ, ψ] j k)) : W ≤ (![φ, ψ] k) ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)))
    (pullU (![φ, ψ] k) (L.U (i k) ⊓ L.U (j k)) (L.g (i k) (j k)))) ^ ((![1, -1] : Fin 2 → ℤ) k))).symm

end GlobalTheory.SameZeroScheme
end
