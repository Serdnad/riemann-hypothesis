module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle122
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle063
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqZeroOfSmulEqZero
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle002
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle125
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle126
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceProjectionExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle127
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle008
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ImmBlock

theorem aeval_mul_of_isHomogeneous {σ R : Type*} [Fintype σ] [CommRing R] {alg : Algebra ℤ R}
    {F : MvPolynomial σ ℤ} {n : ℕ}
    (hF : F.IsHomogeneous n) (a : σ → R) (t : R) :
    MvPolynomial.aeval (fun i => a i * t) F = MvPolynomial.aeval a F * t ^ n := by
  classical
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hd)
    have h2 : Finsupp.degree d = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact h
    rw [← h2, Finsupp.degree_apply]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, _root_.mul_assoc]

theorem aeval_ringHom {σ A B : Type*} [CommRing A] [CommRing B] {algA : Algebra ℤ A} {algB : Algebra ℤ B}
    (φ : A →+* B) (a : σ → A) (P : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (fun i => φ (a i)) P = φ (MvPolynomial.aeval a P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.aeval_C, eq_intCast, map_intCast]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X]

theorem differentiable_aeval {σ κ : Type*} [Fintype κ] (g : σ → κ) (P : MvPolynomial σ ℤ) :
    Differentiable ℂ (fun u : κ → ℂ => MvPolynomial.aeval (fun i => u (g i)) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using differentiable_const _
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (differentiable_apply _)

theorem form_mem {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (k₀ k : K) (n : ℕ) (F G : MvPolynomial (J k₀) ℤ) (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous n) (c d : J k)
    (h : MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) F * y ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) G * y ⟨k, d⟩) :
    MvPolynomial.rename (Sigma.mk k₀) F * MvPolynomial.X ⟨k, c⟩ -
      MvPolynomial.rename (Sigma.mk k₀) G * MvPolynomial.X ⟨k, d⟩ ∈ mCoordIdeal y := by
  have hh := congrArg (MvPolynomial.C : Ω → MvPolynomial K Ω) h
  simp only [map_mul] at hh
  rw [mCoordIdeal, RingHom.mem_ker]
  simp only [mConeMap, map_sub, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_X, Function.comp_def]
  rw [aeval_mul_of_isHomogeneous hF (fun i : J k₀ => (MvPolynomial.C (y ⟨k₀, i⟩) : MvPolynomial K Ω)) (MvPolynomial.X k₀),
    aeval_mul_of_isHomogeneous hG (fun i : J k₀ => (MvPolynomial.C (y ⟨k₀, i⟩) : MvPolynomial K Ω)) (MvPolynomial.X k₀),
    aeval_ringHom MvPolynomial.C (fun i : J k₀ => y ⟨k₀, i⟩) F,
    aeval_ringHom MvPolynomial.C (fun i : J k₀ => y ⟨k₀, i⟩) G]
  linear_combination (MvPolynomial.X k₀ ^ n * MvPolynomial.X k) * hh

theorem differentiableAt_quot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a b : E → ℂ} {v : E}
    (ha : DifferentiableAt ℂ a v) (hb : DifferentiableAt ℂ b v) (h : b v ≠ 0) :
    DifferentiableAt ℂ (fun w => a w / b w) v := by
  simp only [div_eq_mul_inv]
  exact ha.mul (hb.inv h)

theorem ker_bot_of_factor {E F₁ F₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F₁]
    [NormedSpace ℂ F₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] {f : E → F₁} {a : E → F₂} {Ψ : F₁ → F₂} {v₀ : E}
    (hf : DifferentiableAt ℂ f v₀) (hΨ : DifferentiableAt ℂ Ψ (f v₀)) (h : a =ᶠ[nhds v₀] Ψ ∘ f)
    (hk : (fderiv ℂ a v₀).ker = ⊥) : (fderiv ℂ f v₀).ker = ⊥ := by
  rw [h.fderiv_eq, fderiv_comp v₀ hΨ hf] at hk
  rw [eq_bot_iff]
  intro u hu
  have hu' : fderiv ℂ f v₀ u = 0 := hu
  have : u ∈ ((fderiv ℂ Ψ (f v₀)).comp (fderiv ℂ f v₀)).ker := by
    change (fderiv ℂ Ψ (f v₀)) (fderiv ℂ f v₀ u) = 0
    rw [hu', map_zero]
  rwa [hk] at this

theorem immersion_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (e : ℕ) (M : Type) [TopologicalSpace M] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e M) (U : M → Set M) (lam : M → M → (Σ k, J k) → ℂ), Cmp.IsEmbedded A (mCoordIdeal y) U lam → ∀ (κ : Type) [Fintype κ] (ix : κ ≃ J k₀) (x : M) (p : κ), lam x x ⟨k₀, ix p⟩ ≠ 0 → ∀ j, x ∈ (A.chart j).source → DifferentiableAt ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x) ∧ (fderiv ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x)).ker = ⊥ := by
  intro X Ω _ _ ξ K _ J _ y k₀ hTie hEmb e M _ A U lam hE κ _ ix x p hp j hj
  classical
  have hev : ∀ (z : (Σ k, J k) → ℂ) (f : MRing J),
      MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.aeval z f := fun z f => by
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    congr 1
  set G : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun v => lam x ((A.chart j).symm v) with hGdef
  set v₀ : Fin e → ℂ := A.chart j x with hv₀
  have hG0 : G v₀ = lam x x := by
    simp only [hGdef, hv₀]
    rw [(A.chart j).left_inv hj]
  have hS : v₀ ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U x := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    change (A.chart j).symm (A.chart j x) ∈ U x
    rw [(A.chart j).left_inv hj]
    exact hE.mem_U x
  have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U x) :=
    (A.chart j).isOpen_inter_preimage_symm (hE.isOpen x)
  have hAn : ∀ q, DifferentiableAt ℂ (fun v => G v q) v₀ := fun q =>
    (hE.holo x q j v₀ hS).differentiableAt
  have hCo : ∀ q, ContinuousAt (fun v => G v q) v₀ := fun q => (hAn q).continuousAt
  have hw : lam x x ∈ mcPts (mCoordIdeal y) := hE.mem x x (hE.mem_U x)
  have hwpts : lam x x ∈ Small.ptsOver ℂ (mCoordIdeal y) :=
    ⟨hw.1, fun f hf => by rw [← hev]; exact hw.2 f hf⟩
  choose r hr using hw.1
  set p' : (k : K) → J k := Function.update r k₀ (ix p) with hp'def
  have hp'0 : p' k₀ = ix p := by simp [hp'def]
  have hp' : ∀ k, lam x x ⟨k, p' k⟩ ≠ 0 := by
    intro k
    by_cases h : k = k₀
    · subst h
      rw [hp'0]
      exact hp
    · rw [hp'def, Function.update_of_ne h]
      exact hr k
  have hblk := fun k => GlobalTheory.T.small_points_coord_ratio_bound X Ω ξ K J y k₀ hTie hEmb ℂ (lam x x) hwpts (ix p) k (p' k) hp (hp' k)
  choose n F hFh hFr hFn using hblk

  set f : (Fin e → ℂ) → κ → ℂ := fun v i => G v ⟨k₀, ix i⟩ / G v ⟨k₀, ix p⟩ with hfdef
  have ht0 : G v₀ ⟨k₀, ix p⟩ ≠ 0 := by rw [hG0]; exact hp
  have hfd : DifferentiableAt ℂ f v₀ :=
    by
    refine differentiableAt_pi.2 fun i => ?_
    have h := differentiableAt_quot (hAn ⟨k₀, ix i⟩) (hAn ⟨k₀, ix p⟩) ht0
    exact h

  set ev : MvPolynomial (J k₀) ℤ → (κ → ℂ) → ℂ :=
    fun P u => MvPolynomial.aeval (fun i' : J k₀ => u (ix.symm i')) P with hevdef
  have hevd : ∀ P, Differentiable ℂ (ev P) := fun P => differentiable_aeval (fun i' => ix.symm i') P
  have hscale : ∀ v k (d : J k), ev (F k d) (f v) =
      MvPolynomial.aeval (fun i' : J k₀ => G v ⟨k₀, i'⟩) (F k d) * ((G v ⟨k₀, ix p⟩)⁻¹) ^ n k := by
    intro v k d
    rw [← aeval_mul_of_isHomogeneous (hFh k d)]
    simp only [hevdef, hfdef, Equiv.apply_symm_apply, div_eq_mul_inv]
  have hden0 : ∀ k, ev (F k (p' k)) (f v₀) ≠ 0 := by
    intro k
    rw [hscale, hG0]
    exact mul_ne_zero (hFn k) (pow_ne_zero _ (inv_ne_zero hp))
  set Ψ : (κ → ℂ) → (Σ k, J k) → ℂ := fun u q => ev (F q.1 q.2) u / ev (F q.1 (p' q.1)) u with hΨdef
  have hΨd : DifferentiableAt ℂ Ψ (f v₀) :=
    by
    refine differentiableAt_pi.2 fun q => ?_
    have h := differentiableAt_quot (hevd (F q.1 q.2) (f v₀)) (hevd (F q.1 (p' q.1)) (f v₀)) (hden0 q.1)
    exact h

  have e1 : ∀ᶠ v in nhds v₀, G v ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [hSo.mem_nhds hS] with v hv
    exact hE.mem x _ hv.2
  have e2 : ∀ᶠ v in nhds v₀, ∀ k, G v ⟨k, p' k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k =>
      (hCo ⟨k, p' k⟩).eventually_ne (by rw [hG0]; exact hp' k)
  have e3 : ∀ᶠ v in nhds v₀, ∀ k, ev (F k (p' k)) (f v) ≠ 0 :=
    Filter.eventually_all.2 fun k =>
      (((hevd _).continuous.continuousAt).comp hfd.continuousAt).eventually_ne (hden0 k)
  have e4 : ∀ᶠ v in nhds v₀, G v ⟨k₀, ix p⟩ ≠ 0 := (hCo _).eventually_ne ht0
  have hfac : (fun v => affCoord p' (G v)) =ᶠ[nhds v₀] Ψ ∘ f := by
    filter_upwards [e1, e2, e3, e4] with v h1 h2 h3 h4
    funext q
    obtain ⟨k, d⟩ := q
    have hmem := form_mem y k₀ k (n k) (F k d) (F k (p' k)) (hFh k d) (hFh k (p' k)) (p' k) d (hFr k d)
    have h0 := h1.2 _ hmem
    rw [hev] at h0
    simp only [map_sub, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_X, Function.comp_def] at h0
    have hrel : ev (F k d) (f v) * G v ⟨k, p' k⟩ = ev (F k (p' k)) (f v) * G v ⟨k, d⟩ := by
      rw [hscale, hscale]
      linear_combination ((G v ⟨k₀, ix p⟩)⁻¹) ^ n k * h0
    change G v ⟨k, d⟩ / G v ⟨k, p' k⟩ = ev (F k d) (f v) / ev (F k (p' k)) (f v)
    rw [div_eq_div_iff (h2 k) (h3 k)]
    linear_combination -hrel
  have hk : (fderiv ℂ (fun v => affCoord p' (G v)) v₀).ker = ⊥ :=
    hE.immersion x p' hp' j hj
  exact ⟨hfd, ker_bot_of_factor hfd hΨd hfac hk⟩

end GlobalTheory.CompanionTheory.Ar.ImmBlock
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SplitEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem isPreimmersion_fst (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
  have b₁ : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  exact MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip b₁

theorem mem_of_dense_of_isOpen {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    [T0Space X] {U : Set X} (hU : IsOpen U) (hd : Dense U) {x : X} (hx : ∀ z, z ⤳ x → z = x) : x ∈ U := by
  have hfin : (irreducibleComponents X).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hgen : ∀ C ∈ irreducibleComponents X, x ∈ C → C = closure {x} := by
    intro C hC hxC
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have e := hx _ (hg.specializes hxC)
    rw [← e]
    exact hg.def.symm
  let T : Set X := ⋃ C ∈ irreducibleComponents X \ {closure {x}}, C
  have hT : IsClosed T := Set.Finite.isClosed_biUnion (hfin.subset Set.diff_subset)
    fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  have hxT : x ∈ Tᶜ := by
    intro h
    obtain ⟨C, ⟨hC, hne⟩, hxC⟩ := Set.mem_iUnion₂.1 h
    exact hne (hgen C hC hxC)
  obtain ⟨w, hwT, hwU⟩ := hd.inter_open_nonempty _ hT.isOpen_compl ⟨x, hxT⟩
  have hwC : w ∈ closure {x} := by
    by_contra hn
    refine hwT (Set.mem_iUnion₂.2 ⟨irreducibleComponent w,
      ⟨irreducibleComponent_mem_irreducibleComponents w, fun e => hn ?_⟩, mem_irreducibleComponent⟩)
    rw [← (show irreducibleComponent w = closure {x} from e)]
    exact mem_irreducibleComponent
  exact (specializes_iff_mem_closure.2 hwC).mem_open hU hwU

theorem injective_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : Function.Injective Y.j := by
  have := isPreimmersion_fst Y
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  exact Y.j.isEmbedding.injective

theorem genPt_comp {X X' : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (g : X ⟶ X') :
    genPt (ξ ≫ g) = g (genPt ξ) :=
  Scheme.Hom.comp_apply ξ g (IsLocalRing.closedPoint Ω : Spec (CommRingCat.of Ω))

theorem mem_range_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X) (cst : c.F →+* Ω) (hmax : ∀ y, y ⤳ genPt ξ → y = genPt ξ)
    (hs : ξ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F))) : genPt ξ ∈ Set.range Y.j := by
  have hpr := projProper _ _ _ Y.proj
  have sq : ξ ≫ Y.s = spMap cst ≫ spMap (algebraMap (𝓞 c.F) c.F) := by rw [hs, spMap_comp']
  let P := pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F))
  let ξ₁ : Spec (CommRingCat.of Ω) ⟶ P := pullback.lift ξ (spMap cst) sq
  have hf : ξ₁ ≫ pullback.fst _ _ = ξ := pullback.lift_fst _ _ _
  let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
  let x₁ : P := ξ₁ pt
  have h1 : pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F)) x₁ = genPt ξ := by
    have e := Scheme.Hom.comp_apply ξ₁ (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) pt
    rw [hf] at e
    exact e.symm
  have a₁ := isPreimmersion_fst Y
  have hx₁ : ∀ z : P, z ⤳ x₁ → z = x₁ := by
    intro z hz
    apply (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective
    rw [h1]
    exact hmax _ (h1 ▸ hz.map (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).continuous)
  have : LocallyOfFiniteType (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have : QuasiCompact (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := inferInstance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap (algebraMap (𝓞 c.F) c.F)))
  have : IsNoetherian P := {}
  have := Y.jQ_open
  obtain ⟨v', hv'⟩ := mem_of_dense_of_isOpen Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hx₁
  exact ⟨v', by rw [Model.j, Scheme.Hom.comp_apply, hv', h1]⟩

theorem splitComps_of_fnAlgClosed (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (hc : Formalism.L2.Pj.FnAlgClosed (Xo := Xo) (c := c)) : SplitComps Y := by
  intro Ω _ ξ cst hξ hs a ha
  have hmax := CptInh.nogen ξ hξ
  obtain ⟨w₀, hw₀⟩ := mem_range_j Y ξ cst hmax hs
  have hwmax : ∀ y, y ⤳ w₀ → y = w₀ := by
    intro y hy
    have h1 : Y.j y ⤳ genPt ξ := hw₀ ▸ hy.map Y.j.continuous
    exact injective_j Y ((hmax _ h1).trans hw₀.symm)
  let Z : Formalism.L2.Pj.Comp Xo c := ⟨irreducibleComponent w₀, irreducibleComponent_mem_irreducibleComponents w₀⟩
  have hZ : Formalism.L2.Pj.genPt Z = w₀ := by
    have hC := irreducibleComponent_mem_irreducibleComponents w₀
    have hg := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    exact hwmax _ (hg.specializes mem_irreducibleComponent)
  have e : genPt (Formalism.L2.Pj.genSp Z ≫ Y.j) = genPt ξ := by
    refine (genPt_comp (Ω := Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.genSp Z) Y.j).trans ?_
    rw [← hw₀, ← hZ]
    exact congrArg Y.j (Scheme.fromSpecResidueField_apply _ _)
  obtain ⟨i, hi⟩ := TowerOfTest.factor ξ hξ (Formalism.L2.Pj.genSp Z ≫ Y.j) e
  have hcomp : i.comp cst = algebraMap c.F (Formalism.L2.Pj.kap Z) := by
    have hsY : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
    have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
      (Spec.map_preimage _).symm
    have h2 : spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) ≫ spMap (algebraMap (𝓞 c.F) c.F) =
        spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← h1, ← hs]
      refine (Category.assoc _ _ _).trans ?_
      refine Eq.trans (congrArg (Formalism.L2.Pj.genSp Z ≫ ·) hsY.symm) ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ Y.s) hi).trans (Category.assoc _ _ _)
    have e0 : (i.comp cst).comp (algebraMap (𝓞 c.F) c.F) =
        (algebraMap c.F (Formalism.L2.Pj.kap Z)).comp (algebraMap (𝓞 c.F) c.F) := by
      apply TowerOfTest.spec_inj
      have : spMap ((i.comp cst).comp (algebraMap (𝓞 c.F) c.F)) =
          spMap i ≫ spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
        rw [RingHom.comp_assoc, spMap_comp']
      exact this.trans (h2.symm.trans (spMap_comp' _ _).symm)
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0
  have hb : IsAlgebraic c.F (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z) (i a)) := by
    obtain ⟨p, hp0, hp⟩ := ha
    refine ⟨p.map (Int.castRingHom c.F), (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2 hp0, ?_⟩
    have h3 := Polynomial.hom_eval₂ p (algebraMap ℤ Ω) ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i) a
    rw [← Polynomial.aeval_def, hp, map_zero] at h3
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    refine Eq.trans ?_ h3.symm
    exact congrArg (fun φ => Polynomial.eval₂ φ _ p) (Subsingleton.elim _ _)
  obtain ⟨k, hk⟩ := hc Z _ hb
  refine ⟨k, i.injective ?_⟩
  have h2 : algebraMap c.F (Formalism.L2.Pj.kap Z) k = i a := by
    apply (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).injective
    rw [← hk, ← IsScalarTower.algebraMap_apply]
  rw [← h2, ← hcomp]
  rfl

end GlobalTheory.CompanionTheory.Ar.SplitEx
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg


theorem _root_.GlobalTheory.T.nonzero_section_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∀ b : Sp R, b.asIdeal = ⊥ → ∃ y : G.left, G.hom y = b ∧ y ∈ Out.nonzeroLocus (M := M) t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Gen.exists_generic_mem_nonzeroLocus <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg


theorem _root_.GlobalTheory.T.section_module_divisible_at_prime : ∀ (R : Type) [CommRing R] [IsDomain R] (X : Scheme.{0}) (p : X ⟶ Sp R) [Smooth p] (M : LB X) (b : Sp R), b.asIdeal.IsMaximal → ∀ u : SecMod p M, (∀ y : X, p y = b → y ∉ Out.nonzeroLocus (M := M) u) → ∀ c e : R, e ≠ 0 → (∀ π ∈ b.asIdeal, e ∣ c * π) → ∃ u' : SecMod p M, e • u' = c • u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv.exists_smul_eq_smul | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv.exists_smul_eq_smul | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.FibDiv.exists_smul_eq_smul <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.KeyGen GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg


theorem _root_.GlobalTheory.T.section_module_bounded_denominator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom] [QuasiCompact G.hom] (M : LB G.left), M.IsLB → ∀ t : SecMod G.hom M, t ≠ 0 → ∃ d₀ : R, d₀ ≠ 0 ∧ ∀ (x d : R) (u : SecMod G.hom M), d ≠ 0 → d • u = x • t → d ∣ d₀ * x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom.bounded_denominators | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom.bounded_denominators | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDeg.Denom.bounded_denominators <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.arith_variety_prime_hodge_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), ∀ (s : CMType H ⊕ CMType H), (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = 𝔐.emb s a) → (∃ x ∈ differentIdeal ℤ (𝓞 E), ∃ o : O, algebraMap O Ω o * 𝔐.emb s x = 1) → (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → ∀ a : Fin (labelRk D s) → Ω, a ∈ coordLat O y (𝔐.HT p s) (b s) c' ↔ ∀ u ∈ P.Dh.om', u (∑ k, a k • b s k) ∈ CR O y c' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.mem_coordLat_iff_forall_om_mem_chartRing | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.mem_coordLat_iff_forall_om_mem_chartRing | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.mem_coordLat_iff_forall_om_mem_chartRing <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.T.arith_variety_prime_hodge_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ (∀ (q : Cpt 𝔐.ξ), InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → ∀ x ∈ CR O y c', x ∈ regAt 𝔐.ξ q) ∧ ∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_relay | exact GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.arith_variety_prime_hodge_relay <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chart_om_eigQuot_projective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c'), IsNoetherianRing (CR O y c') → (∀ 𝔮 : Ideal (CR O y c'), 𝔮.IsPrime → ∃ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) ∧ ∀ x : Ω, x ∈ regAt 𝔐.ξ q ↔ ∃ u v : CR O y c', v ∉ 𝔮 ∧ x * (v : Ω) = (u : Ω)) → (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → HT.omP 𝔐 p q = Submodule.span (regAt 𝔐.ξ q) (P.Dh.om' : Set (Module.Dual Ω 𝔐.Li))) → Module.Projective (CR O y c') P.Dh.om' ∧ ∀ t : CMType H ⊕ CMType H, ∀ σ : E →+* Ω, (∀ a : 𝓞 E, σ (a : E) = 𝔐.emb t a) → Module.Projective (CR O y c') (P.Dh.omHT σ) :=
  @PositivityTheory.Xgn.sequence_projection_exists

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.PropZ_proved : GlobalTheory.CompanionTheory.Ar.Flat.PropZ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds | exact GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PropZ_holds <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes

theorem _root_.GlobalTheory.T.exists_standard_smooth_localization : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0), ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth | exact GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth | (intros; apply GlobalTheory.CompanionTheory.Ar.SegreChart.exists_away_standardSmooth <;> assumption)
end
