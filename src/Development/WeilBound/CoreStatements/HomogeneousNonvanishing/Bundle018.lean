module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle234
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle032
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle296
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.NonvanishingDense
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.OAlgoverAlg
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ZH GlobalTheory.ZH.RatModel GlobalTheory.CompHt

namespace PositivityTheory.UnitarySelfGeneration.UnitProductCombination

theorem mul_eq_one_of_comb {K V : Type} [Field K] [AddCommGroup V] [Module K V] {N n : ℕ}
    (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (c : Matrix (Fin n) (Fin N) K)
    (h : ∀ j, b j = ∑ k, c k j • ∑ i, g i k • b i) : g * c = 1 := by
  ext i j
  have e := congrArg (fun v => b.repr v i) (h j)

  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
  Pi.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
  Finset.mem_univ, if_true] at e
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [mul_comm (g i _), ← e, eq_comm]

theorem sum_eq {K : Type} [Field K] (σ : K →+* ℂ) {N n : ℕ} {g : Matrix (Fin N) (Fin n) K}
    {c : Matrix (Fin n) (Fin N) K} (h : g * c = 1) (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) (a : Fin N) :
    ∑ k, (∑ m, σ (c k m) * A m a) * ∑ j, σ (g j k) * x j = ∑ m, A m a * x m := by
  have e : ∀ j m, ∑ k, σ (g j k) * σ (c k m) = if j = m then 1 else 0 := fun j m => by
    have := congrArg σ (congrFun (congrFun h j) m)

    rw [Matrix.mul_apply, map_sum, Matrix.one_apply, apply_ite σ, map_one, map_zero] at this
    simpa only [map_mul] using this
  calc ∑ k, (∑ m, σ (c k m) * A m a) * ∑ j, σ (g j k) * x j
      = ∑ j, ∑ m, (∑ k, σ (g j k) * σ (c k m)) * (A m a * x j) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by simp [e]

theorem isometric_fs {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (M : RatModel (𝓞 K) Ω) (L : HermLB M.s)
    (ev : V →ₗ[K] Ω) {W : Submodule (𝓞 K) V} (s : W → L.B.Sec) {e : L.B.ι → Ω}
    (hv : ∀ w : W, M.HasVal e (s w) (ev w)) (hW : Submodule.span K (W : Set V) = ⊤) {N n : ℕ}
    (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W) (hgw : ∀ k, (gw k : V) = ∑ j, g j k • b j)
    (hcb : ∀ j, b j = ∑ k, c k j • (gw k : V))
    (hφ : ∀ (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts M.s (σ.comp (algebraMap (𝓞 K) K))),
      (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ i y =
        Real.log (∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2))
    (hs : ⨆ k, nonzeroLocus (s (gw k)) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (hdet hcc)
    (hMt : ∀ (σ : K →+* ℂ) (x : Fin N → ℂ),
      ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2)
    (t : ℝ) :
    ((HermLB.fs M.s L.isLB (fun k => s (gw k)) hs Mt hdet hcc).shift (fun _ => t) (fun _ => rfl)).Isometric
      (L.shift (fun _ => t) (fun _ => rfl)) := by
  have hgc := mul_eq_one_of_comb b g c fun j => by simpa only [hgw] using hcb j
  refine HermLB.isometric_of_eqOn fun σ' l y hl => ?_
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = σ' := ⟨_, GlobalTheory.TrueGeo.OfLattice.extEmb_comp σ'⟩
  replace hl : y ∈ ptsIn M.s _ (L.B.U l) := hl
  have hz := mem_ptsIn.1 hl
  obtain ⟨x, hx⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.exists_coord y.2 ev (e l) b hW fun v hvW => by
    rw [← hv ⟨v, hvW⟩ l ⟨_, hz⟩]
    exact valF_mem_O hz _
  have hr : Set.range y.1 ⊆ L.B.U l := (GlobalTheory.ZH.top_le_preimage_iff _ _).1 hl
  have hsk : ∀ k, valR y.1 (L.B.U l) ((s (gw k)).f l) = ∑ j, σ (g j k) * x j := fun k => by
    refine ((val_eq hr (hv (gw k) l ⟨_, hz⟩)).symm.trans (hx _)).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgw, b.repr_sum_self]
  refine congrArg (· + 2 * t) ((hφ σ l y).trans (Eq.trans ?_
    (Weight.fsBasis_φ L.isLB (fun k => s (gw k)) hs _ (hdet _) l y).symm))
  simp only [hsk, hMt, sum_eq σ hgc]
  rw [GlobalTheory.Adelic.archSize, Real.sq_sqrt (by positivity)]

end PositivityTheory.UnitarySelfGeneration.UnitProductCombination
end

section

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

theorem ao_fderiv {I I' : Type} [Fintype I] [Fintype I'] {n : ℕ} (e : I' ≃ I) (f : (Fin n → ℂ) → I → ℂ)
    (x : Fin n → ℂ) (h : (fderiv ℂ f x).ker = ⊥) : (fderiv ℂ (fun z i => f z (e i)) x).ker = ⊥ := by
  have := (LinearEquiv.funCongrLeft ℂ ℂ e).toContinuousLinearEquiv.comp_fderiv (f := f) (x := x)
  rw [eq_bot_iff] at h ⊢
  intro v hv
  refine h ?_
  have hv' : fderiv ℂ ((LinearEquiv.funCongrLeft ℂ ℂ e).toContinuousLinearEquiv ∘ f) x v = 0 := hv
  rw [this] at hv'
  exact (LinearEquiv.funCongrLeft ℂ ℂ e).toContinuousLinearEquiv.map_eq_zero_iff.1 hv'

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem o_algover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (x : Sp RM.Ω ⟶ Xo.XF c), Or.𝔐.ξ ≫ Or.𝔐.f = x ≫ Y.j → Mono (spMap β) → (∀ x : Sys.X, ∃ (U : Set Sys.X) (lam : Sys.X → Fin (Fx.m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, Sys.A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • Fx.pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ (Sys.A.chart j).source → (fderiv ℂ (fun z i => lam ((Sys.A.chart j).symm z) i / lam ((Sys.A.chart j).symm z) p) (Sys.A.chart j x)).ker = ⊥) → AlgOver (Or.Re.comap some) := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or x hx hβ hloc
  choose U lam hU hmem hholo hpt himm using hloc
  have hP : IsMultiHomogIdeal (mCoordIdeal RM.y) := RM.arith.2.1.2.1
  have hl : ∀ x, Or.Re.R.lift x x ∈ mcPts (mCoordIdeal RM.y) := fun x => Or.Re.R.mem x x (Or.Re.R.mem_U x)
  have honto : Function.Surjective Or.Re.π := by
    have hc : IsClosed (Set.range Or.Re.π) := (isCompact_range Or.Re.holo.1).isClosed
    have hd : Dense (Or.Re.br)ᶜ := interior_eq_empty_iff_dense_compl.1 Or.Re.degree.2.1
    have hs : (Or.Re.br)ᶜ ⊆ Set.range Or.Re.π := fun x hx =>
      Set.nonempty_of_ncard_ne_zero (s := Or.Re.π ⁻¹' {x}) (by
        rw [Or.Re.degree.2.2.2.2.1 x hx]; exact Or.Re.deg_pos.ne')
    rw [← Set.range_eq_univ, ← hc.closure_eq]
    exact (hd.mono hs).closure_eq

  have hπ : ∀ x' x, Or.Re.π x' ∈ U x → ∃ a : ℂ, a ≠ 0 ∧
      ∀ i, lam x (Or.Re.π x') i = a * Or.Re.R.lift x' x' ⟨Or.k₀, Or.ix i⟩ := fun x' x h => by
    obtain ⟨a, ha⟩ := Or.π_pt x'
    obtain ⟨a₀, h0, e⟩ := hpt x _ h
    have ha0 : a ≠ 0 := by
      rintro rfl
      obtain ⟨i, hi⟩ := (hl x').1 Or.k₀
      obtain ⟨i, rfl⟩ := Or.ix.surjective i
      exact hi (by simpa using congrFun ha i)
    refine ⟨a₀ / a, div_ne_zero h0 ha0, fun i => ?_⟩
    have := congrFun ha i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [e, this, Pi.smul_apply, smul_eq_mul]
    field_simp
  obtain ⟨b, d, hbd, hb, hint⟩ := GlobalTheory.T.hodge_cpt_multihomog_form E H D l Xo c O β Y S RM.Ω RM.K RM.ι RM.y Or.𝔐 x hx hβ
  letI := Or.g.toAlgebra
  have : FiniteDimensional Fx.Ωf RM.Ω := Module.finite_of_finrank_pos (by
    rw [Or.g_deg, ← Or.Re_deg]; exact Or.Re.deg_pos)
  obtain ⟨n, s, hs, hsQ, hs0⟩ := AlgOv.norm_form Or.k₀ Or.ix Fx.yf Or.y_eq Fx.generate hbd hb
  have hQ := AlgOv.imageZ_blk Or.k₀ Or.ix RM.y
  refine ⟨Unit, inferInstance, fun _ => Fin (Fx.m + 1), inferInstance, fun _ => Or.k₀, AlgOv.blk Or.k₀ Or.ix, U,
    fun x y p => lam x y p.2, s, fun _ => n, ⟨fun _ _ _ => rfl, ?_, fun _ => rfl, ?_⟩,
    ⟨hU, hmem, fun x p => hholo x p.2, ?_, ?_, ?_, ?_, ?_⟩, ?_, hs, fun h => hsQ (hQ ▸ h), ?_⟩
  · rintro ⟨_, i⟩ ⟨_, j⟩ h
    have : Or.ix i = Or.ix j := eq_of_heq (Sigma.mk.inj h).2
    rw [Or.ix.injective this]
  · rintro ⟨k, i⟩ ⟨_, rfl⟩
    exact ⟨⟨(), Or.ix.symm i⟩, by simp [AlgOv.blk]⟩
  · intro x y hy
    obtain ⟨x', rfl⟩ := honto y
    obtain ⟨a, ha, e⟩ := hπ x' x hy
    have hw := AlgOv.scale_mem hP (hl x') ha
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · obtain ⟨i, hi⟩ := hw.1 Or.k₀
      obtain ⟨i, rfl⟩ := Or.ix.surjective i
      exact ⟨i, fun h => hi ((e i).symm.trans h)⟩
    · have := hw.2 _ hf
      rw [AlgOv.evC_eq] at this ⊢
      refine Eq.trans ?_ ((aeval_rename _ _ f).symm.trans this)
      congr 2
      exact funext fun p => e p.2
  · intro x x' y hy
    obtain ⟨a, ha, e⟩ := hpt x y hy.1
    obtain ⟨a', ha', e'⟩ := hpt x' y hy.2
    refine ⟨fun _ => a / a', fun _ => div_ne_zero ha ha', funext fun p => ?_⟩
    simp only [e, e', Pi.smul_apply, smul_eq_mul]
    field_simp
  · intro z hz
    obtain ⟨w, hw, a, ha, e⟩ := AlgOv.blk_onto Or.k₀ Or.ix
      (fun k => (hl (honto Or.Re.nonempty_base.some).choose).1 k |>.imp fun i hi =>
        AlgOv.coord_ne (hl _) hi) (hQ ▸ hz)
    obtain ⟨x', t, ht, e'⟩ := r_onto RM.K RM.ι _ _ _ Or.Re.R RM.arith w hw
    obtain ⟨a', ha', e''⟩ := hπ x' _ (hmem _)
    refine ⟨Or.Re.π x', fun _ => a' * t Or.k₀ / a, fun _ => div_ne_zero (mul_ne_zero ha' (ht _)) ha,
      funext fun p => ?_⟩
    have h1 : Or.Re.R.lift x' x' ⟨Or.k₀, Or.ix p.2⟩ = t Or.k₀ * w (AlgOv.blk Or.k₀ Or.ix p) := congrFun e' _
    show lam _ _ p.2 = _ * z p
    rw [e'', h1, e p]
    field_simp
  · rintro x x' ⟨t, ht, e⟩
    obtain ⟨a, ha, e1⟩ := hpt x x (hmem x)
    obtain ⟨a', ha', e2⟩ := hpt x' x' (hmem x')
    refine Fx.pt_inj x x' (t () * a' / a) (funext fun i => ?_)
    have : lam x x i = t () * lam x' x' i := congrFun e ⟨(), i⟩
    simp only [e1, e2, Pi.smul_apply, smul_eq_mul] at this ⊢
    field_simp
    linear_combination this
  · intro x p hp j hj
    exact ao_fderiv (Equiv.uniqueSigma fun _ : Unit => Fin (Fx.m + 1)) _ _ (himm x (p ()) (hp ()) j hj)
  · intro x'
    obtain ⟨a, ha, e⟩ := hπ x' _ (hmem _)
    exact ⟨fun _ => a, fun _ => ha, funext fun p => e p.2⟩
  · intro x hxb
    obtain ⟨x', rfl⟩ := honto x
    obtain ⟨a, ha, e⟩ := hπ x' _ (hmem _)
    have hb0 : aeval (Or.Re.R.lift x' x') b = 0 := by
      by_contra h
      obtain ⟨z, hz1, hz2⟩ := hint _ (hl x') (fun h' => h ((AlgOv.evC_eq _ _).symm.trans h'))
      exact (Or.interior x' z hz1).1 hz2 hxb
    refine (AlgOv.evC_eq _ _).trans ?_
    have h1 := aeval_blockScale hs (fun _ => a) (Or.Re.R.lift x' x' ∘ AlgOv.blk Or.k₀ Or.ix)
    rw [hs0 _ (hl x') hb0, mul_zero] at h1
    refine Eq.trans ?_ h1
    congr 2
    exact funext fun p => e p.2

end PositivityTheory.UnitarySelfGeneration
end
