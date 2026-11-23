module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle090
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle091
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle109
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle155
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle153
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle145
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond

@[expose] public section

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

noncomputable section
namespace GlobalTheory.CompanionTheory.TubeFourier

theorem continuous_pt (x : ℝ × ℝ) : Continuous fun y : ℝ × ℝ => pt x y := by
  have h : (fun y : ℝ × ℝ => pt x y) =
      fun y => ((x.1 : ℂ) + (y.1 : ℂ) * Complex.I, (x.2 : ℂ) + (y.2 : ℂ) * Complex.I) := by
    funext y
    simp [pt, Complex.ext_iff]
  rw [h]
  fun_prop

theorem pt_re_im (l : ℂ × ℂ) : pt (l.1.re, l.2.re) (l.1.im, l.2.im) = l := by
  exact Prod.ext (Complex.eta _) (Complex.eta _)

private lemma pt_mem_tube_iff {x y : ℝ × ℝ} {S : Set (ℝ × ℝ)} : pt x y ∈ tube S ↔ x ∈ S := by
  simp [tube, pt]

theorem tubeChain : TubeChain := by
  intro X _ _ _ T _ _ m Ω F hΩ hV hmid
  set G : Fin (m + 1) → T → ℂ × ℂ → X := fun i g => gauss (F i · g) with hGdef
  have hGT : ∀ i g, GaussTube (G i g) (Ω i) := fun i g => gaussTube_of_tubeGood (hΩ i).2.2 g
  have hind : ∀ i g, ∀ x ∈ Ω i, ∀ x' ∈ Ω i, ∀ t, phi (G i g) x t = phi (G i g) x' t :=
    fun i g => GlobalTheory.T.tube_transform_independent_of_base X (Ω i) (G i g) (hΩ i).1 (hΩ i).2.1 (hGT i g)
  have hstep : ∀ i : Fin m, ∀ g, ∀ x ∈ Ω i.castSucc, ∀ x' ∈ Ω i.succ, ∀ t,
      phi (G i.castSucc g) x t = phi (G i.succ g) x' t := by
    intro i g x hx x' hx' t
    obtain ⟨V, -, ⟨v, hv⟩, hVsub, hVeq⟩ := hV i
    rw [hind _ g x hx v (hVsub hv).1, hind _ g x' hx' v (hVsub hv).2]
    unfold phi
    congr 1
    funext y
    congr 1
    simp only [G, gauss]
    rw [hVeq (pt v y) (pt_mem_tube_iff.2 hv) g]
  have hQ : ∀ g t, ∀ k : Fin (m + 1), ∀ x ∈ Ω 0, ∀ x' ∈ Ω k,
      phi (G 0 g) x t = phi (G k g) x' t := by
    intro g t k
    induction k using Fin.induction with
    | zero => exact fun x hx x' hx' => hind 0 g x hx x' hx' t
    | succ i ih =>
      intro x hx x' hx'
      obtain ⟨V, -, ⟨v, hv⟩, hVsub, -⟩ := hV i
      rw [ih x hx v (hVsub hv).1]
      exact hstep i g v (hVsub hv).1 x' hx' t
  have hne0 : (Ω 0).Nonempty := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      obtain ⟨i, j, a, ha, b, hb, -⟩ := hmid 0
      obtain rfl : i = 0 := Fin.ext (Nat.lt_one_iff.1 i.isLt)
      exact ⟨a, ha⟩
    · obtain ⟨V, -, ⟨v, hv⟩, hVsub, -⟩ := hV ⟨0, hm⟩
      have h0 : (Fin.castSucc (⟨0, hm⟩ : Fin m)) = 0 := by
        ext
        simp
      exact ⟨v, h0 ▸ (hVsub hv).1⟩
  obtain ⟨x0, hx0⟩ := hne0
  set φ : ℝ × ℝ → T → X := fun t g => phi (G 0 g) x0 t with hφdef
  have hall : ∀ i g, ∀ x ∈ Ω i, ∀ t, phi (G i g) x t = φ t g :=
    fun i g x hx t => (hQ g t i x0 hx0 x hx).symm
  have hGcont : ∀ i, ∀ x ∈ Ω i, Continuous (fun p : (ℝ × ℝ) × T => G i p.2 (pt x p.1)) := by
    intro i x hx
    have hp : Continuous fun p : (ℝ × ℝ) × T => pt x p.1 := (continuous_pt x).comp continuous_fst
    have h1 : Continuous (fun p : (ℝ × ℝ) × T => F i (pt x p.1) p.2) := by
      refine (hΩ i).2.2.cont.comp_continuous (hp.prodMk continuous_snd) ?_
      intro p
      exact ⟨pt_mem_tube_iff.2 hx, Set.mem_univ _⟩
    have he : Continuous fun p : (ℝ × ℝ) × T =>
        Complex.exp ((pt x p.1).1 ^ 2 + (pt x p.1).2 ^ 2) :=
      Complex.continuous_exp.comp (((continuous_fst.comp hp).pow 2).add ((continuous_snd.comp hp).pow 2))
    exact he.smul h1
  have hGbd : ∀ i, ∀ x ∈ Ω i, ∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ y : ℝ × ℝ,
      ‖G i g' (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2)) := by
    intro i x hx g
    obtain ⟨U, hU, M, hM⟩ := gauss_bound (hΩ i).2.2 (Set.singleton_subset_iff.2 hx)
      isCompact_singleton g
    refine ⟨U, hU, M, fun g' hg' y => ?_⟩
    have := hM g' hg' (pt x y) (pt_mem_tube_iff.2 rfl)
    simpa [pt] using this
  have hφcont : Continuous (fun p : (ℝ × ℝ) × T => φ p.1 p.2) :=
    GlobalTheory.T.gaussian_tube_transform_continuous X T (G 0) x0 (hGcont 0 x0 hx0) (fun g => hGbd 0 x0 hx0 g)
  have hφt : ∀ g : T, Continuous fun t => φ t g := fun g =>
    hφcont.comp (show Continuous (fun t : ℝ × ℝ => (t, g)) by fun_prop)
  have hdecay : ExpDecay φ := by
    refine GlobalTheory.T.exponential_decay_by_midpoints X T φ {a | ∃ i, a ∈ Ω i} ?_ ?_
    · rintro a ⟨i, ha⟩ g
      obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 ((hΩ i).1.mem_nhds ha)
      obtain ⟨U, hU, M, hM⟩ := gauss_bound (hΩ i).2.2 hsub (isCompact_closedBall a r) g
      refine ⟨r, hr, U, hU, M * Real.pi, fun x hx1 hx2 g' hg' t => ?_⟩
      have hxC : x ∈ Metric.closedBall a r := by
        rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_le_iff]
        exact ⟨hx1, hx2⟩
      rw [← hall i g' x (hsub hxC) t]
      refine GlobalTheory.T.gaussian_tube_transform_bound X (G i g') x M (fun y => ?_) t
      have := hM g' hg' (pt x y) (pt_mem_tube_iff.2 hxC)
      simpa [pt] using this
    · intro x
      obtain ⟨i, j, a, ha, b, hb, hx⟩ := hmid x
      exact ⟨a, ⟨i, ha⟩, b, ⟨j, hb⟩, hx⟩
  refine ⟨fun l g => inv (fun t => φ t g) l, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro g p v
    exact (GlobalTheory.T.inverse_transform_holomorphic_lines X T φ hdecay hφt g p v).differentiableOn
  · exact (GlobalTheory.T.inverse_transform_continuous X T φ hdecay hφcont).continuousOn
  · intro C _ hC g
    obtain ⟨U, hU, M, hM⟩ := GlobalTheory.T.inverse_transform_locally_bounded X T φ hdecay hφt C hC g
    exact ⟨U, hU, M, fun l hl g' hg' => hM l hl g' hg'⟩
  · intro i l hl g
    obtain ⟨x, hxdef⟩ : ∃ x : ℝ × ℝ, x = (l.1.re, l.2.re) := ⟨_, rfl⟩
    obtain ⟨y, hydef⟩ : ∃ y : ℝ × ℝ, y = (l.1.im, l.2.im) := ⟨_, rfl⟩
    have hx : x ∈ Ω i := hxdef ▸ hl
    have hphi : phi (G i g) x = fun t => φ t g := funext fun t => hall i g x hx t
    have hc1 : Continuous fun y' : ℝ × ℝ => G i g (pt x y') := by
      have h := (hGcont i x hx).comp (show Continuous (fun y' : ℝ × ℝ => (y', g)) by fun_prop)
      simpa only [Function.comp_def] using h
    obtain ⟨U, hU, M, hM⟩ := hGbd i x hx g
    obtain ⟨ε, hε, U', hU', M', hM'⟩ := hdecay x g
    have key := GlobalTheory.T.inverse_transform_recovers_function X (G i g) x hc1 ⟨M, fun y' => hM g (mem_of_mem_nhds hU) y'⟩
      (by rw [hphi]; exact hφt g)
      ⟨ε, hε, M', fun t => by
        rw [hall i g x hx t]
        exact hM' x (by simp [hε.le]) (by simp [hε.le]) g (mem_of_mem_nhds hU') t⟩ y
    rw [hphi, hxdef, hydef, pt_re_im] at key
    simpa [G, gauss] using key

end GlobalTheory.CompanionTheory.TubeFourier
end
end

section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso ReciprocityTheory.Neutral.Bridge

namespace GlobalTheory.CompanionTheory.PTIso.ShaTransfer

theorem nonempty_equiv_of_mem_iff {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) (p : Submodule R A) (q : Submodule R B)
    (h : ∀ x, x ∈ p ↔ e x ∈ q) : Nonempty (p ≃ₗ[R] q) := by
  refine ⟨LinearEquiv.ofSubmodules e p q ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x).1 hx
  · intro hy
    exact ⟨e.symm y, (h _).2 (by simpa using hy), by simp⟩

theorem dualData_transfer {R A B A' B' : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (eA : A' ≃ₗ[R] A) (eB : B' ≃ₗ[R] B)
    (h : Finite A' ∧ Finite B' ∧ Nonempty (B' ≃ₗ[R] Module.Dual R A') ∧
      Nat.card A' = Nat.card B') :
    Finite A ∧ Finite B ∧ Nonempty (B ≃ₗ[R] Module.Dual R A) ∧ Nat.card A = Nat.card B := by
  obtain ⟨hA, hB, ⟨f⟩, hc⟩ := h
  refine ⟨Finite.of_equiv _ eA.toEquiv, Finite.of_equiv _ eB.toEquiv,
    ⟨(eB.symm.trans f).trans eA.symm.dualMap⟩, ?_⟩
  rw [← Nat.card_congr eA.toEquiv, ← Nat.card_congr eB.toEquiv, hc]

section Rep

variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
  {I I' : Type} {D : I → Type} {D' : I' → Type}
  [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
  [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
  (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))
  (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i))
  {N : Type} [AddCommGroup N] [Module R N] [TopologicalSpace N] [DiscreteTopology N]
  (σ : Representation R Γ N) (σ' : Representation R Γ' N)
  (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i))

theorem local_compat (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (i : I) :
    ∀ d m, (σ'.comp (φ' (eI i))) (eD i d) m = (σ.comp (φ i)) d m := by
  intro d m
  show σ' (φ' (eI i) (eD i d)) m = σ (φ i d) m
  rw [hD, hσ]

theorem res_h1_iso_h1 (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (i : I) (x : H1 σ') :
    resH1 σ (φ i) (hφ i) (equivH1OfIso eG σ' σ hσ x) =
      equivH1OfIso (eD i) (σ'.comp (φ' (eI i))) (σ.comp (φ i)) (local_compat φ φ' σ σ' eG eI eD hD hσ i)
        (resH1 σ' (φ' (eI i)) (hφ' (eI i)) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext d
    show f.1 (eG (φ i d)) = f.1 (φ' (eI i) (eD i d))
    rw [hD]

theorem res_h2_iso_h2 (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (i : I) (x : H2 σ') :
    resH2 σ (φ i) (hφ i) (equivH2OfIso eG σ' σ hσ x) =
      equivH2OfIso (eD i) (σ'.comp (φ' (eI i))) (σ.comp (φ i)) (local_compat φ φ' σ σ' eG eI eD hD hσ i)
        (resH2 σ' (φ' (eI i)) (hφ' (eI i)) x) := by
  induction x using Submodule.Quotient.induction_on with
  | H f =>
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext d
    show f.1 (eG (φ i d.1), eG (φ i d.2)) = f.1 (φ' (eI i) (eD i d.1), φ' (eI i) (eD i d.2))
    rw [hD, hD]

theorem mem_Sha1_iff_equiv_mem (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (x : H1 σ') :
    x ∈ Sha1 σ' φ' hφ' ↔ equivH1OfIso eG σ' σ hσ x ∈ Sha1 σ φ hφ := by
  simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i
    rw [res_h1_iso_h1 φ hφ φ' hφ' σ σ' eG eI eD hD hσ, h, map_zero]
  · intro h i'
    obtain ⟨i, rfl⟩ := eI.surjective i'
    have hi := h i
    rw [res_h1_iso_h1 φ hφ φ' hφ' σ σ' eG eI eD hD hσ] at hi
    exact (LinearEquiv.map_eq_zero_iff _).1 hi

theorem mem_Sha2_iff_equiv_mem (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) (x : H2 σ') :
    x ∈ Sha2 σ' φ' hφ' ↔ equivH2OfIso eG σ' σ hσ x ∈ Sha2 σ φ hφ := by
  simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i
    rw [res_h2_iso_h2 φ hφ φ' hφ' σ σ' eG eI eD hD hσ, h, map_zero]
  · intro h i'
    obtain ⟨i, rfl⟩ := eI.surjective i'
    have hi := h i
    rw [res_h2_iso_h2 φ hφ φ' hφ' σ σ' eG eI eD hD hσ] at hi
    exact (LinearEquiv.map_eq_zero_iff _).1 hi

theorem nonempty_sha1_equiv (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) :
    Nonempty (Sha1 σ' φ' hφ' ≃ₗ[R] Sha1 σ φ hφ) :=
  nonempty_equiv_of_mem_iff (equivH1OfIso eG σ' σ hσ) _ _
    (mem_Sha1_iff_equiv_mem φ hφ φ' hφ' σ σ' eG eI eD hD hσ)

theorem nonempty_sha2_equiv (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hσ : ∀ g m, σ' (eG g) m = σ g m) :
    Nonempty (Sha2 σ' φ' hφ' ≃ₗ[R] Sha2 σ φ hφ) :=
  nonempty_equiv_of_mem_iff (equivH2OfIso eG σ' σ hσ) _ _
    (mem_Sha2_iff_equiv_mem φ hφ φ' hφ' σ σ' eG eI eD hD hσ)

end Rep

theorem twDual_compat_of_iso {R Γ Γ' M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [Group Γ'] [TopologicalSpace Γ'] [AddCommGroup M] [Module R M]
    (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ) (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (eG : Γ ≃ₜ* Γ') (hχ : ∀ g, χ' (eG g) = χ g) (hρ : ∀ g m, ρ' (eG g) m = ρ g m) :
    ∀ g ψ, twDual χ' ρ' (eG g) ψ = twDual χ ρ g ψ := by
  intro g ψ
  refine DFunLike.ext _ _ fun m => ?_
  rw [twDual_apply, twDual_apply, hχ, ← map_inv, hρ]

theorem shaG_transfer {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
    {I I' : Type} [Fintype I] [Fintype I'] {D : I → Type} {D' : I' → Type}
    [∀ i, Group (D i)] [∀ i, TopologicalSpace (D i)]
    [∀ i, Group (D' i)] [∀ i, TopologicalSpace (D' i)]
    (φ : ∀ i, D i →* Γ) (hφ : ∀ i, Continuous (φ i))
    (φ' : ∀ i, D' i →* Γ') (hφ' : ∀ i, Continuous (φ' i))
    (χ : Γ →* Rˣ) (χ' : Γ' →* Rˣ)
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (ρ' : Representation R Γ' M)
    (eG : Γ ≃ₜ* Γ') (eI : I ≃ I') (eD : ∀ i, D i ≃ₜ* D' (eI i))
    (hD : ∀ i d, φ' (eI i) (eD i d) = eG (φ i d))
    (hχ : ∀ g, χ' (eG g) = χ g) (hρ : ∀ g m, ρ' (eG g) m = ρ g m)
    (h : ShaG φ' hφ' χ' ρ') : ShaG φ hφ χ ρ := by
  have hT := twDual_compat_of_iso χ χ' ρ ρ' eG hχ hρ
  obtain ⟨a1⟩ := nonempty_sha1_equiv φ hφ φ' hφ' ρ ρ' eG eI eD hD hρ
  obtain ⟨a2⟩ := nonempty_sha2_equiv φ hφ φ' hφ' ρ ρ' eG eI eD hD hρ
  obtain ⟨b1⟩ := nonempty_sha1_equiv φ hφ φ' hφ' (twDual χ ρ) (twDual χ' ρ') eG eI eD hD hT
  obtain ⟨b2⟩ := nonempty_sha2_equiv φ hφ φ' hφ' (twDual χ ρ) (twDual χ' ρ') eG eI eD hD hT
  exact ⟨dualData_transfer b1 a2 h.1, dualData_transfer a1 b2 h.2⟩

end GlobalTheory.CompanionTheory.PTIso.ShaTransfer
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

section Abstract
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem rep_add {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' z'' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c c' : CH.H (sq a b) j}
    (h : ∀ s, z'' s - (z s + z' s) ∈ b.S _) (hc : Rep a b z c) (hc' : Rep a b z' c') :
    Rep a b z'' (c + c') := by
  obtain ⟨f, hf, rfl, e⟩ := hc
  obtain ⟨f', hf', rfl, e'⟩ := hc'
  refine ⟨f + f', by rw [map_add (f := _), hf, hf', add_zero], rfl, fun s => ?_⟩
  change (show sqM a b _ from f s).1 + (show sqM a b _ from f' s).1 = _
  rw [e s, e' s, ← map_add (f := _)]
  refine Ideal.Quotient.eq.2 ?_
  have := (b.S _).neg_mem (h s)
  rwa [neg_sub] at this

theorem rep_neg {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j}
    (h : ∀ s, z' s - (-z s) ∈ b.S _) (hc : Rep a b z c) : Rep a b z' (-c) := by
  obtain ⟨f, hf, rfl, e⟩ := hc
  refine ⟨-f, by rw [map_neg, hf, neg_zero], rfl, fun s => ?_⟩
  change -(show sqM a b _ from f s).1 = _
  rw [e s, ← map_neg]
  refine Ideal.Quotient.eq.2 ?_
  have := (b.S _).neg_mem (h s)
  rwa [neg_sub] at this

theorem sum_wz_sub {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    {ι : Type} [Fintype ι] (I : ι → Fin j → Fin d) (s : ComposableArrows C j)
    (y y' : ι → Φ.A.obj (s.obj (Fin.last j))) (h : ∀ i, y i - y' i ∈ Φ.J.S _) :
    ∑ i, wz u (I i) s * y i - ∑ i, wz u (I i) s * y' i ∈ (Fil ((j : ℤ) + 1)).S _ := by
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← mul_sub]
  have h1 : y i - y' i ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    rw [Nat.cast_one, hF.one]
    exact h i
  have := hF.mul j 1 _ (wz_mem hF u hu (I i) s) h1
  rwa [Nat.cast_add, Nat.cast_one] at this

end Abstract

section Forms
variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lft_add_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f g : Γ(X, W)) :
    lft W T (f + g) - (lft W T f + lft W T g) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add (f := _), lft_spec T h, lft_spec T h, lft_spec T h, map_add (f := _), sub_self]

theorem lft_neg_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f : Γ(X, W)) :
    lft W T (-f) - (-lft W T f) ∈ T.J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_neg, lft_spec T h, lft_spec T h, map_neg, sub_self]

theorem lift_cocycle {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (i : Fin d)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' := by
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hu i _ (hP _ T'.property), ev_nat φ.hom (hP _ T.property) (hP _ T'.property),
    ← hu i _ (hP _ T.property)]
  exact sub_eq_zero.2 rfl

end Forms

theorem stAdd : StAdd := by
  intro O _ X q W d t u hu P hP r x x' c c' hc hc'
  have hF : IsFil (sP P) (sFil P) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hcoc := fun i {T T' : P.FullSubcategory} (φ : T ⟶ T') => lift_cocycle hu P hP i φ
  constructor
  · refine rep_add (fun s => ?_) hc hc'
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj ((x + x') I)))
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) +
        (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x' I)))
      (fun I => lft_add_sub _ (hP _ (s.obj (Fin.last r)).property) _ _)
    simpa only [mul_add, Finset.sum_add_distrib] using this
  · refine rep_neg (fun s => ?_) hc
    have := sum_wz_sub hF (fun i T => u i T.obj) hcoc (fun I : Idx r d => I.1) s
      (fun I => (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj ((-x) I)))
      (fun I => -(show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)))
      (fun I => lft_neg_sub _ (hP _ (s.obj (Fin.last r)).property) _)
    simpa only [mul_neg, Finset.sum_neg_distrib] using this

end GlobalTheory.CompanionTheory.GrForm
end
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrForm.AffCover

theorem iInf_basicOpen {X : Scheme.{0}} {V : X.Opens} : ∀ (n : ℕ) (g : Fin (n + 1) → Γ(X, V)),
    (⨅ a, X.basicOpen (g a)) = X.basicOpen (∏ k, g k) := by
  intro n
  induction n with
  | zero =>
    intro g
    simp
  | succ n ih =>
    intro g
    rw [Fin.prod_univ_succ, Scheme.basicOpen_mul, ← ih (fun k => g k.succ)]
    exact le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun a => iInf_le _ a.succ))
      (le_iInf fun a => Fin.cases inf_le_left (fun b => inf_le_right.trans (iInf_le _ b)) a)

theorem stCover : GlobalTheory.CompanionTheory.GrForm.StCover := by
  intro O _ X q _ V hV
  classical
  have loc : ∀ x : V, ∃ (f : Γ(X, V)) (d : ℕ), x.1 ∈ X.basicOpen f ∧ Nonempty (Coord q (X.basicOpen f) d) := by
    intro x
    have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ V le_top).hom :=
      RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hV le_top)
    obtain ⟨f, hf, hst⟩ := GlobalTheory.CompanionTheory.CovEx.exists_basicOpen RingHom.IsStandardSmooth
      RingHom.isStandardSmooth_respectsIso q hV h x.2
    obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
    exact ⟨f, n, hf, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hV f g hg he⟩
  choose f d hx hc using loc
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).2) (fun x hxV => Set.mem_iUnion.2 ⟨⟨x, hxV⟩, hx _⟩)
  refine ⟨t, inferInstance, fun a => X.basicOpen (f a.1), fun a => d a.1, fun a => (hc a.1).some, ?_, ?_⟩
  · refine le_antisymm (iSup_le fun a => X.basicOpen_le _) fun x hxV => ?_
    obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht hxV)
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.1 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩
  · intro n i
    have e : capO (fun a : t => X.basicOpen (f a.1)) i = X.basicOpen (∏ k, f (i k).1) :=
      iInf_basicOpen n (fun k => f (i k).1)
    rw [e]
    exact hV.basicOpen _

end GlobalTheory.CompanionTheory.GrForm.AffCover
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.coords_of_etale_basic_open : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens}, IsAffineOpen W → ∀ (g : Γ(X, W)) {d : ℕ} (s : Fin d → Γ(X, W)), letI := (strV q W).toAlgebra; (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g)) (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k)) : MvPolynomial (Fin d) K →+* Localization.Away g).Etale → ∃ c : Coord q (X.basicOpen g) d, ∀ k, c.t k = resO (X.basicOpen_le g) (s k) := by
  first | exact @GlobalTheory.CompanionTheory.GeoCoord.exists_coord_basicOpen | exact GlobalTheory.CompanionTheory.GeoCoord.exists_coord_basicOpen | (intros; apply GlobalTheory.CompanionTheory.GeoCoord.exists_coord_basicOpen <;> assumption)
end
