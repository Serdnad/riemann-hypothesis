module

import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle024
public import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalToGlobal.IndefiniteReal.MemSpanOfSmulMem
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle021
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle055
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory.CoordsOfMemAdjoin

open IntermediateField

theorem exists_coords_of_mem_adjoin {F : Type*} [Field F] [Algebra ℚ F] {s : F} {c : ℚ}
    (hs : s ^ 2 = algebraMap ℚ F c) {x : F} (hx : x ∈ ℚ⟮s⟯) :
    ∃ a b : ℚ, x = algebraMap ℚ F a + algebraMap ℚ F b * s := by
  apply GlobalTheory.CompanionTheory.QuadFin.exists_eq_add_mul_of_mem_adjoin <;> assumption

theorem exists_rat_coords {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) {x : H.E} (hx : x ∈ H.K) :
    ∃ a b : ℚ, x = (a : H.E) + (b : H.E) * H.sqrtMinusD := by
  have hb : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq
  have hs : H.sqrtMinusD ^ 2 = algebraMap ℚ H.E (-(H.d : ℚ)) := by
    rw [map_neg, map_natCast]
    exact hb
  obtain ⟨a, b, h⟩ := exists_coords_of_mem_adjoin hs hx
  exact ⟨a, b, by simpa only [eq_ratCast] using h⟩

end GlobalTheory.CoordsOfMemAdjoin
end

section

namespace GlobalTheory.NonzeroSmulMemIntegralSpan

theorem exists_ne_zero_smul_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {M : Submodule (NumberField.RingOfIntegers K) V} {x : V}
    (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : NumberField.RingOfIntegers K, d ≠ 0 ∧ d • x ∈ M := by
  apply Formalism.IndefR.LatticeTransfer.Lat.exists_smul_mem <;> assumption

end GlobalTheory.NonzeroSmulMemIntegralSpan
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.tameInertia_fixed_dvd_valuation_order : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ (k : ℕ) (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F), IsUnit (k : O) →
      IsLocalHom φ → (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ x ∈ O, O.valuation (σ x - x) < 1) → π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) →
      IsPrimitiveRoot (σ π / π) k →
      ∀ (d : F) (z : (FractionRing W)ˣ), σ d = d → O.valuation d ^ k = O.valuation (algebraMap (FractionRing W) F z) →
        (k : ℤ) ∣ (GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z := by
  first | exact @GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord | exact GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord | (intros; apply GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.FrobSemisimple

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem minpoly_eval_zero_ne_zero {f : End ℂ V} (hf : IsUnit f) : (minpoly ℂ f).eval 0 ≠ 0 := by
  intro h0
  have h1 : f.HasEigenvalue 0 := End.hasEigenvalue_iff_isRoot.mpr h0
  exact spectrum.zero_notMem ℂ hf (End.hasEigenvalue_iff_mem_spectrum.mp h1)

theorem isSemisimple_of_pow {g : End ℂ V} (hg : IsUnit g) {m : ℕ} (hm : 0 < m)
    (hs : (g ^ m).IsSemisimple) : g.IsSemisimple := by
  have hsep : (minpoly ℂ (g ^ m)).Separable :=
    PerfectField.separable_iff_squarefree.mpr hs.minpoly_squarefree
  have h0 := minpoly_eval_zero_ne_zero (hg.pow m)
  set p := minpoly ℂ (g ^ m) with hp
  refine End.isSemisimple_of_squarefree_aeval_eq_zero (p := expand ℂ m p)
    (Separable.squarefree ?_) ?_
  · rw [Separable, derivative_expand]
    refine IsCoprime.mul_right (IsCoprime.map hsep (expand ℂ m).toRingHom)
      (IsCoprime.mul_right ?_ (IsCoprime.pow_right ?_))
    · have : IsUnit ((m : ℕ) : ℂ[X]) := by
        rw [← C_eq_natCast]
        exact isUnit_C.mpr (Ne.isUnit (Nat.cast_ne_zero.mpr hm.ne'))
      exact (isCoprime_mul_unit_left_right this _ 1).mpr isCoprime_one_right |>.of_mul_right_left
    · refine ((irreducible_X.coprime_iff_not_dvd).mpr ?_).symm
      rw [X_dvd_iff, coeff_zero_eq_eval_zero, expand_eval, zero_pow hm.ne']
      exact h0
  · rw [expand_aeval]
    exact minpoly.aeval ℂ _

end GlobalTheory.WeilDeligne.FrobSemisimple

namespace GlobalTheory.WeilDeligne

open NumberField IsDedekindDomain Polynomial Module in
private theorem isSemisimple_of_mul_eq_one' {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {f g : End ℂ V} (hf : f.IsSemisimple) (hgf : g * f = 1) :
    g.IsSemisimple := by
  apply _root_.GlobalTheory.WeilDeligne.isSemisimple_of_iSup_eigenspace
  have htop : ⨆ α, f.eigenspace α = ⊤ :=
    hf.iSup_maxGenEigenspace_eq_top_iff.1 (Module.End.iSup_maxGenEigenspace_eq_top f)
  rw [eq_top_iff, ← htop]
  refine iSup_le fun α => le_trans ?_ (le_iSup _ α⁻¹)
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have h1 : v = α • g v := by
    have := congrArg g hv
    rwa [← Module.End.mul_apply, hgf, Module.End.one_apply, map_smul] at this
  by_cases hα : α = 0
  · subst hα
    rw [zero_smul] at h1
    simp [h1]
  · conv_rhs => rw [h1]
    rw [smul_smul, inv_mul_cancel₀ hα, one_smul]

open NumberField IsDedekindDomain Polynomial Module in
private theorem isSemisimple_of_isUnit_of_pow_isSemisimple {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {f : End ℂ V} (hf : IsUnit f) {m : ℕ} (hm : 0 < m)
    (hfm : (f ^ m).IsSemisimple) : f.IsSemisimple := by
  have hint : IsIntegral ℂ (f ^ m) := Algebra.IsIntegral.isIntegral _
  have hX : ¬ X ∣ minpoly ℂ (f ^ m) := by
    rintro ⟨q, hq⟩
    have h0 : aeval (f ^ m) q = 0 := by
      have h1 := minpoly.aeval ℂ (f ^ m)
      rw [hq, map_mul, aeval_X] at h1
      exact (hf.pow m).mul_right_eq_zero.1 h1
    have hq0 : q ≠ 0 := by
      rintro rfl
      exact minpoly.ne_zero hint (by simpa using hq)
    have hdeg := natDegree_le_of_dvd (minpoly.dvd ℂ (f ^ m) h0) hq0
    rw [hq, natDegree_mul X_ne_zero hq0, natDegree_X] at hdeg
    omega
  have hsep : (minpoly ℂ (f ^ m)).Separable :=
    PerfectField.separable_iff_squarefree.2 hfm.minpoly_squarefree
  have hXe : ¬ X ∣ expand ℂ m (minpoly ℂ (f ^ m)) := by
    rw [X_dvd_iff, coeff_expand hm]
    rw [X_dvd_iff] at hX
    simpa using hX
  have hunit : IsUnit ((m : ℂ[X])) := by
    rw [← map_natCast C]
    exact isUnit_C.2 (Ne.isUnit (by exact_mod_cast hm.ne'))
  have hP : (expand ℂ m (minpoly ℂ (f ^ m))).Separable := by
    rw [separable_def, derivative_expand]
    refine IsCoprime.mul_right
      (((separable_def _).1 hsep).map (expand ℂ m).toRingHom) (IsCoprime.mul_right ?_ ?_)
    · exact isCoprime_one_right.of_isCoprime_of_dvd_right (hunit.dvd)
    · exact IsCoprime.pow_right ((Irreducible.coprime_iff_not_dvd irreducible_X).2 hXe).symm
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hP.squarefree
  rw [expand_aeval]
  exact minpoly.aeval ℂ (f ^ m)


open NumberField IsDedekindDomain Polynomial Module in
theorem _root_.GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type)
      [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (_root_.GlobalTheory.WeilDeligne.Weil h) V),
      _root_.GlobalTheory.WeilDeligne.IsSmooth ρ → ∀ φ : _root_.GlobalTheory.WeilDeligne.Weil h, _root_.GlobalTheory.WeilDeligne.deg φ = 1 →
      End.IsSemisimple (ρ φ) → ∀ σ : _root_.GlobalTheory.WeilDeligne.Weil h, End.IsSemisimple (ρ σ) := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ ρ hρ φ hφ hss σ
  have hunit : IsUnit (ρ σ) := (Group.isUnit σ).map ρ
  obtain ⟨τ, hτdeg, hτ⟩ : ∃ τ : _root_.GlobalTheory.WeilDeligne.Weil h,
      _root_.GlobalTheory.WeilDeligne.deg τ = _root_.GlobalTheory.WeilDeligne.deg σ ∧ End.IsSemisimple (ρ τ) := by
    rcases le_or_gt 0 (_root_.GlobalTheory.WeilDeligne.deg σ) with hd | hd
    · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hd
      refine ⟨φ ^ k, by rw [_root_.GlobalTheory.WeilDeligne.deg_pow, hφ, hk]; ring, ?_⟩
      rw [map_pow]
      exact hss.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) k)
    · obtain ⟨k, hk⟩ := Int.exists_eq_neg_ofNat hd.le
      have hinv : End.IsSemisimple (ρ φ⁻¹) :=
        isSemisimple_of_mul_eq_one' hss (by rw [← map_mul, inv_mul_cancel, map_one])
      refine ⟨φ⁻¹ ^ k, ?_, ?_⟩
      · rw [_root_.GlobalTheory.WeilDeligne.deg_pow, ← zpow_neg_one, _root_.GlobalTheory.WeilDeligne.deg_zpow, hφ, hk]
        ring
      · rw [map_pow]
        exact hinv.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) k)
  obtain ⟨m, hm, hpow⟩ :=
    _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ σ τ hτdeg.symm
  apply isSemisimple_of_isUnit_of_pow_isSemisimple hunit hm
  rw [hpow]
  exact hτ.of_mem_adjoin_singleton (pow_mem (Algebra.self_mem_adjoin_singleton ℂ _) m)

end GlobalTheory.WeilDeligne
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_pow_frob_commute {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {h : IsPlaceOver A w} {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ, Commute (ρ (frob (h := h)) ^ m) (ρ σ) := by
  have h1 : ∀ τ : Weil h, ∃ m : ℕ, 0 < m ∧ Commute (ρ (frob (h := h)) ^ m) (ρ τ) := by
    intro τ
    obtain ⟨m, hm, he⟩ := exists_pow_eq_pow_of_deg_eq E Ω A w h V ρ hρ (frob (h := h))
      (τ * frob (h := h) * τ⁻¹) (by simp [deg_mul, deg_inv])
    refine ⟨m, hm, ?_⟩
    rw [← map_pow, ← map_pow, conj_pow] at he
    show _ * _ = _ * _
    rw [← map_pow]
    conv_lhs => rw [he]
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have h2 : ∀ S : Set (End ℂ V), S.Finite → (∀ x ∈ S, ∃ τ, ρ τ = x) →
      ∃ m : ℕ, 0 < m ∧ ∀ x ∈ S, Commute (ρ (frob (h := h)) ^ m) x := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨1, one_pos, by simp⟩
    | @insert x S _ _ ih =>
      intro hx
      obtain ⟨m, hm, hc⟩ := ih fun y hy => hx y (Set.mem_insert_of_mem _ hy)
      obtain ⟨τ, rfl⟩ := hx x (Set.mem_insert _ _)
      obtain ⟨n, hn, hc'⟩ := h1 τ
      refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
      rintro y (rfl | hy)
      · rw [mul_comm, pow_mul]; exact hc'.pow_left m
      · rw [pow_mul]; exact (hc y hy).pow_left n
  obtain ⟨m, hm, hc⟩ := h2 _ hρ.finite_range (by rintro _ ⟨σ, rfl⟩; exact ⟨_, rfl⟩)
  refine ⟨m, hm, fun σ => ?_⟩
  have h0 : deg ((frob (h := h) ^ deg σ)⁻¹ * σ) = 0 := by
    simp [deg_mul, deg_inv, deg_zpow, deg_frob]
  have h3 : Commute (ρ (frob (h := h)) ^ m) (ρ ((frob (h := h) ^ deg σ)⁻¹ * σ)) :=
    hc _ ⟨⟨_, deg_eq_zero_iff.mp h0⟩, rfl⟩
  have h4 : Commute (ρ (frob (h := h)) ^ m) (ρ (frob (h := h) ^ deg σ)) :=
    (((Commute.refl (frob (h := h))).zpow_right _).map ρ).pow_left m
  have := h4.mul_right h3
  rwa [← map_mul, mul_inv_cancel_left] at this

open NumberField IsDedekindDomain Polynomial Module in
private lemma exists_polynomial_eigenspace_smul_lemma {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (f : ℂ → ℂ) :
    ∃ p : ℂ[X], ∀ (α : ℂ) (v : V), v ∈ T.eigenspace α → aeval T p v = f α • v := by
  classical
  have hfin : Set.Finite {μ | T.HasEigenvalue μ} := Module.End.finite_hasEigenvalue T
  refine ⟨Lagrange.interpolate hfin.toFinset id f, fun α v hv => ?_⟩
  by_cases hv0 : v = 0
  · simp [hv0]
  have hev : T.HasEigenvector α v := ⟨hv, hv0⟩
  rw [Module.End.aeval_apply_of_hasEigenvector hev]
  have hnode := Lagrange.eval_interpolate_at_node (s := hfin.toFinset) (v := id) f
    (Set.injOn_id _) (i := α) (by simpa using Module.End.hasEigenvalue_of_hasEigenvector hev)
  simp only [id] at hnode
  rw [hnode]

open NumberField IsDedekindDomain Polynomial Module in
private lemma eq_of_eq_on_eigenspaces_lemma_2 {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (hT : T.IsSemisimple) {g g' : Module.End ℂ V}
    (h : ∀ (α : ℂ) (v : V), v ∈ T.eigenspace α → g v = g' v) : g = g' := by
  have hle : ⨆ α, T.eigenspace α ≤ LinearMap.ker (g - g') :=
    iSup_le fun α v hv => by simp [sub_eq_zero, h α v hv]
  rw [hT.iSup_eigenspace_eq_top] at hle
  ext v
  simpa [sub_eq_zero] using hle (Submodule.mem_top : v ∈ ⊤)

open NumberField IsDedekindDomain Polynomial Module in
private lemma mem_eigenspace_pow_lemma_3 {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) {α : ℂ} {v : V} (hv : v ∈ T.eigenspace α) (m : ℕ) :
    v ∈ (T ^ m).eigenspace (α ^ m) := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, hv, map_smul, ih, smul_smul, pow_succ, mul_comm]

open NumberField IsDedekindDomain Polynomial Module in
private lemma commute_aeval_of_commute_lemma_4 {V : Type} [AddCommGroup V] [Module ℂ V]
    {S T : Module.End ℂ V} (hST : Commute S T) (p : ℂ[X]) : Commute S (aeval T p) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [map_add (f := _)]; exact hp.add_right hr
  | monomial n x => rw [aeval_monomial]; exact (Algebra.commute_algebraMap_right x S).mul_right (hST.pow_right n)


open NumberField IsDedekindDomain Polynomial Module in
theorem _root_.GlobalTheory.WeilDeligne.WDRep.iso_of_N_eq_smul : ∀ (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a b : _root_.GlobalTheory.WeilDeligne.WDRep h V) (c : ℂ), c ≠ 0 → a.ρ = b.ρ →
    b.N = c • a.N → a.Iso b := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a b c hc hρ hN
  classical
  set φ := _root_.GlobalTheory.WeilDeligne.frob (h := h) with hφ
  set Φ : Module.End ℂ V := a.ρ φ with hΦdef
  have hΦ : Φ.IsSemisimple := a.semisimple φ
  have hq : (1 : ℝ) < (_root_.Formalism.ConjugateSelfDual.normV w : ℝ) := by exact_mod_cast _root_.GlobalTheory.WeilDeligne.one_lt_normV w
  set s : ℂ := Complex.log c / (Real.log (_root_.Formalism.ConjugateSelfDual.normV w : ℝ) : ℂ) with hsdef
  have hlogq : (Real.log (_root_.Formalism.ConjugateSelfDual.normV w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hq).ne'
  have hs : Complex.exp (s * Real.log (_root_.Formalism.ConjugateSelfDual.normV w : ℝ)) = c := by
    rw [hsdef, div_mul_cancel₀ _ hlogq, Complex.exp_log hc]
  set lam : ℂ → ℂ := fun α => Complex.exp (s * Real.log ‖α‖) with hlamdef
  have hlam : ∀ α : ℂ, α ≠ 0 → lam ((_root_.Formalism.ConjugateSelfDual.normV w : ℂ) * α) = c * lam α := by
    intro α hα
    simp only [hlamdef, norm_mul, Complex.norm_natCast]
    rw [Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hα)]
    rw [Complex.ofReal_add, mul_add, Complex.exp_add, hs]
  have hΦinj : ∀ v : V, Φ v = 0 → v = 0 := by
    intro v hv
    have : a.ρ φ⁻¹ (Φ v) = v := by
      rw [hΦdef, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [← this, hv, map_zero]
  obtain ⟨p, hp⟩ := exists_polynomial_eigenspace_smul_lemma Φ lam
  obtain ⟨p', hp'⟩ := exists_polynomial_eigenspace_smul_lemma Φ (fun α => (lam α)⁻¹)
  have hgg' : aeval Φ p * aeval Φ p' = 1 := eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
    rw [Module.End.mul_apply, hp' α v hv, map_smul, hp α v hv, smul_smul,
      inv_mul_cancel₀ (Complex.exp_ne_zero _), one_smul, Module.End.one_apply]
  have hg'g : aeval Φ p' * aeval Φ p = 1 := eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
    rw [Module.End.mul_apply, hp α v hv, map_smul, hp' α v hv, smul_smul,
      mul_inv_cancel₀ (Complex.exp_ne_zero _), one_smul, Module.End.one_apply]
  refine ⟨LinearEquiv.ofLinear (aeval Φ p) (aeval Φ p') hgg' hg'g, ?_, ?_⟩
  · intro σ v
    rw [← hρ]
    change aeval Φ p (a.ρ σ v) = a.ρ σ (aeval Φ p v)
    obtain ⟨m, hm, hpow⟩ := _root_.GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq E Ω A w h V a.ρ
      a.smooth (σ * φ * σ⁻¹) φ
      (by rw [_root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_mul, _root_.GlobalTheory.WeilDeligne.deg_inv]; ring)
    rw [← map_pow, conj_pow, map_mul, map_mul, map_pow] at hpow
    have hcomm : Commute (a.ρ σ) (Φ ^ m) := by
      calc a.ρ σ * Φ ^ m = a.ρ σ * Φ ^ m * (a.ρ σ⁻¹ * a.ρ σ) := by
            rw [← map_mul, inv_mul_cancel, map_one, mul_one]
        _ = Φ ^ m * a.ρ σ := by rw [← mul_assoc, hpow]
    obtain ⟨pm, hpm⟩ := exists_polynomial_eigenspace_smul_lemma (Φ ^ m)
      (fun μ => Complex.exp (s * Real.log ‖μ‖ / m))
    have hgm : aeval Φ p = aeval (Φ ^ m) pm := eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
      rw [hp α v hv, hpm (α ^ m) v (mem_eigenspace_pow_lemma_3 Φ hv m)]
      congr 1
      simp only [hlamdef, norm_pow, Real.log_pow]
      congr 1
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    rw [hgm]
    exact (LinearMap.congr_fun (commute_aeval_of_commute_lemma_4 hcomm pm) v).symm
  · intro v
    rw [hN]
    change aeval Φ p (a.N v) =
      c • a.N (aeval Φ p v)
    have key : aeval Φ p * a.N =
        c • (a.N * aeval Φ p) :=
      eq_of_eq_on_eigenspaces_lemma_2 Φ hΦ fun α v hv => by
        rw [Module.End.mul_apply, LinearMap.smul_apply, Module.End.mul_apply, hp α v hv, map_smul]
        by_cases hα : α = 0
        · have hv0 : v = 0 := hΦinj v (by
            rw [Module.End.mem_eigenspace_iff] at hv
            rw [hv, hα, zero_smul])
          simp [hv0]
        · rw [hp _ _ (a.map_N_eigenspace
            (_root_.GlobalTheory.WeilDeligne.deg_frob) hv), hlam α hα, smul_smul]
    exact LinearMap.congr_fun key v

end GlobalTheory.WeilDeligne
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V), IsSmooth ρ → ∀ σ τ : Weil h, deg σ = deg τ → ∃ m : ℕ, 0 < m ∧ ρ σ ^ m = ρ τ ^ m := by
  first | exact @GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq | exact GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq | (intros; apply GlobalTheory.WeilDeligne.exists_pow_eq_pow_of_deg_eq <;> assumption)
end

section

open CategoryTheory Polynomial GlobalTheory.NormalDescent

theorem _root_.GlobalTheory.T.reversedCharpolyCoeff_map_of_isPushout : ∀ {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B'),
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ') →
    Function.Injective α → ∀ (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ),
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by
  first | exact @GlobalTheory.NormalDescent.normCoeff_map_of_isPushout | exact GlobalTheory.NormalDescent.normCoeff_map_of_isPushout | (intros; apply GlobalTheory.NormalDescent.normCoeff_map_of_isPushout <;> assumption)
end

section

open CategoryTheory Polynomial GlobalTheory.NormalDescent

theorem _root_.GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (b : B), (∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = ⊥) → ∀ p : Ideal A, p.IsPrime →
    (∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∉ Q) → ∃ k, 1 ≤ k ∧ normCoeff φ hφ b k ∉ p := by
  first | exact @GlobalTheory.NormalDescent.exists_normCoeff_not_mem | exact GlobalTheory.NormalDescent.exists_normCoeff_not_mem | (intros; apply GlobalTheory.NormalDescent.exists_normCoeff_not_mem <;> assumption)
end

section

open Matrix GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.exists_torusWeight_maximizing_weighted_sum : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ) (μ₀ : Fin n → ℤ), IsWt Φ μ₀ → ∃ μ : Fin n → ℤ, IsWt Φ μ ∧ ∀ ν : Fin n → ℤ, IsWt Φ ν → ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * ν i ≤ ∑ i : Fin n, ((n : ℤ) - ((i : ℕ) : ℤ)) * μ i := by
  first | exact @GlobalTheory.AlgWtHW.MaxWeight.exists_max_weight | exact GlobalTheory.AlgWtHW.MaxWeight.exists_max_weight | (intros; apply GlobalTheory.AlgWtHW.MaxWeight.exists_max_weight <;> assumption)
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.mvPolynomial_eval_zero_of_vanishing_rational_skewHermitian : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), (∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 → MvPolynomial.eval (upt (ratPt S)) Q = 0) → ∀ Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, (∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) → MvPolynomial.eval (upt Y) Q = 0 := by
  first | exact @GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew | exact GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew | (intros; apply GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew <;> assumption)
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.polyRep_mulVec_mem_of_cofinite_scalar_shift : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (S : Submodule ℂ (ι → ℂ)) (v : ι → ℂ) (B : GL (Fin n) ℂ) (F : Set ℂ), F.Finite → (∀ s ∉ F, ∀ C : GL (Fin n) ℂ, C.val = B.val + s • (1 : Matrix (Fin n) (Fin n) ℂ) → Φ C *ᵥ v ∈ S) → Φ B *ᵥ v ∈ S := by
  first | exact @GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift | exact GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift | (intros; apply GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift <;> assumption)
end

section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

theorem _root_.GlobalTheory.T.dominanceOrderLE_of_mem_spanWeightVectorsDominatedBy : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (μ lam : Fin n → ℤ) (w : ι → ℂ), IsWtVec Φ μ w → w ≠ 0 → w ∈ Sle Φ lam → DomLE μ lam := by
  first | exact @GlobalTheory.AlgWtHW.DomLEOfSle.domLE_of_mem_Sle | exact GlobalTheory.AlgWtHW.DomLEOfSle.domLE_of_mem_Sle | (intros; apply GlobalTheory.AlgWtHW.DomLEOfSle.domLE_of_mem_Sle <;> assumption)
end
