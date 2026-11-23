module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle122
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle150
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle456
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle453
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle002
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle458
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Formalism.ConjugateSelfDual.Bundle001
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.LocGL

theorem exists_isL_of_unitary_twists (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (hS : GlobalTheory.Published.StandardCosocleGL)
    (hP : ∀ (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y)
    (𝔫 : Multiset (Segment k))
    (h𝔫 : ∀ Δ ∈ 𝔫, ∃ (δ : IrrGL (k := k)) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)) : ∃ y : IrrGL (k := k), IsL 𝔫 y.rep := by
  classical
  have h' : ∀ Δ ∈ 𝔫, ∃ (t : ℝ) (δ : IrrGL (k := k)) (Γ : Segment k), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ) := fun Δ h =>
    let ⟨δ, Γ, t, h⟩ := h𝔫 Δ h
    ⟨t, δ, Γ, h⟩
  choose! t ht using h'
  let r : Segment k → Segment k → Prop := fun a b => t b ≤ t a
  haveI : IsTrans (Segment k) r := ⟨fun a b c h1 h2 => le_trans h2 h1⟩
  haveI : Std.Total r := ⟨fun a b => le_total _ _⟩
  obtain ⟨l, hl, hs⟩ : ∃ l : List (Segment k), (l : Multiset (Segment k)) = 𝔫 ∧ l.Pairwise r :=
    ⟨𝔫.toList.insertionSort r,
      (Multiset.coe_eq_coe.2 (List.perm_insertionSort r _)).trans (Multiset.coe_toList 𝔫),
      List.pairwise_insertionSort r _⟩
  have hm : ∀ i : Fin l.length, l.get i ∈ 𝔫 := fun i => by
    rw [← hl]; exact List.get_mem l i
  choose δ Γ hL hU hE using fun i : Fin l.length => ht _ (hm i)
  have hF : LFactors 𝔫 (fun i : Fin l.length => (δ i).nu (t (l.get i))) := by
    refine ⟨fun i => (Γ i).nu (t (l.get i)), ⟨?_, fun i j hij h => ?_⟩, fun i => ?_⟩
    · rw [← hl, ← funext hE]
      simp
    · have h1 : t (l.get j) ≤ t (l.get i) := List.pairwise_iff_get.1 hs i j hij
      have := hP _ _ _ _ (hL i) (hU i) (hL j) (hU j) _ _ h
      linarith
    · exact ((hL i).tw _ (isSmoothChar_absPow _)).of_equiv ((δ i).twEquiv _ _)
  obtain ⟨π, hπ⟩ := hS k 𝔫 _ _ _ rfl hF
  exact ⟨IrrGL.of π.ρ π.smooth π.irr, _, _, rfl, hF, hπ.of_equiv (IrrGL.equivOf _ _ _) (.refl _)⟩

end GlobalTheory.LocGL
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.CentralSupport

theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a)) (g : ∀ a, Γ a) (c : α → ℂ)
    (h : ∀ a v, ρ a (g a) v = c a • v) (y : ⨂[ℂ] a, X a) : piTensor ρ g y = (∏ a, c a) • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, smul_comm, piTensor_tprod]
    congr 1
    simp only [h]
    exact MultilinearMap.map_smul_univ _ _ _

theorem sum_card_mul_modExp {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] :
    ∑ a, (Fintype.card (m a) : ℤ) * modExp m a = 0 := by
  simp only [modExp, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_filter]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prod_absPow {α : Type} (S : Finset α) (c : α → ℂ) : ∏ a ∈ S, absPow k (c a) = absPow k (∑ a ∈ S, c a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, absPow_add]

theorem absPow_pow (s : ℂ) (N : ℕ) (z : kˣ) : absPow k s (z ^ N) = absPow k (N * s) z := by
  ext
  rw [map_pow, Units.val_pow_eq_pow_val, val_absPow, val_absPow, Complex.cpow_nat_mul]

theorem deltaHalf_scalar {α : Type} [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (z : kˣ) : deltaHalf k m (fun a => GeneralLinearGroup.scalar (m a) z) = 1 := by
  have hd : ∀ a, GeneralLinearGroup.det (GeneralLinearGroup.scalar (m a) z) = z ^ Fintype.card (m a) := fun a => by
    ext; simp [GeneralLinearGroup.scalar]
  rw [deltaHalf_apply]
  simp only [hd, absPow_pow]
  rw [← MonoidHom.finsetProd_apply, prod_absPow]
  have h0 : ∑ a, ((Fintype.card (m a) : ℕ) : ℂ) * ((modExp m a : ℂ) / 2) = 0 := by
    have := congrArg (fun t : ℤ => (t : ℂ) / 2) (sum_card_mul_modExp m)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero, zero_div, Finset.sum_div] at this
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [h0, absPow_zero, MonoidHom.one_apply]

theorem hasCentralChar_multiProd_prod {α n : Type} [Fintype α] [LinearOrder α] [Fintype n] [DecidableEq n]
    {c : α → Type} [∀ a, Fintype (c a)] [∀ a, DecidableEq (c a)] (e : (Σ a, c a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (c a) k) (X a)) (ω : α → kˣ →* ℂˣ)
    (hω : ∀ a, HasCentralChar (σ a) (ω a)) : HasCentralChar (multiProd e σ) (∏ a, ω a) := by
  intro z f
  have h1 : leviEmb k e (fun a => GeneralLinearGroup.scalar (c a) z) = GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := e.surjective j
    by_cases hb : b = b'
    · subst hb
      rw [leviEmb_apply_same]
      simp [GeneralLinearGroup.scalar, diagonal_apply]
    · rw [leviEmb_apply_ne _ _ _ hb]
      simp [GeneralLinearGroup.scalar, diagonal_apply, hb]
  have h4 := parInd_law e (piTensor σ) f
    ⟨_, leviEmb_mem_parab k e (fun a => GeneralLinearGroup.scalar (c a) z)⟩
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have h5 := h4 x
  rw [leviProj_leviEmb, deltaHalf_scalar, piTensor_scalar σ _ (fun a => (ω a z : ℂ)) (fun a => hω a z)] at h5
  have hc : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = ((∏ a, ω a) z : ℂ) • f.1.1 x
  rw [hc, ← h1, MonoidHom.finsetProd_apply, Units.coe_prod]
  simpa using h5

theorem centralChar_eq_prod_support : BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (s : Multiset (IrrGL (k := k)))
    (ω : kˣ →* ℂˣ), HasSupport x.rep s → HasCentralChar x.rep ω → ∃ f : IrrGL (k := k) → kˣ →* ℂˣ,
      (∀ y ∈ s, HasCentralChar y.rep (f y)) ∧ ∀ z, ω z = (s.map fun y => f y z).prod := by
  intro _ k _ _ _ _ _ x s ω hs hω
  choose f _ hf using fun y : IrrGL (k := k) => LocGL.exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
  refine ⟨f, fun y _ => hf y, fun z => ?_⟩
  obtain ⟨h, x', rfl, hi, -, e, hsub⟩ := hs
  have hcen := hasCentralChar_multiProd_prod e (fun a => (x' a).rep) (fun a => f (x' a)) (fun a => hf (x' a))
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have h1 := Model.scalar_of_isSubquotient hsub (hcen z) v
  rw [hω] at h1
  have h2 := smul_left_injective ℂ hv h1
  rw [Multiset.map_map]
  change ω z = ∏ a, f (x' a) z
  apply Units.ext
  rw [h2, MonoidHom.finsetProd_apply]

end GlobalTheory.CentralSupport
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.admissible_parameters_family_const : ∀ {eps : ℝ} (Fm : FamP eps), ∃ C x0 : ℝ, 1 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ParametersPolynomiallyBounded (Fm.L x i) C (Fm.params x hx i) := by
  first | exact @GlobalTheory.NLink.admissible_parameters_design_family | exact GlobalTheory.NLink.admissible_parameters_design_family | (intros; apply GlobalTheory.NLink.admissible_parameters_design_family <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.FilInv

open GlobalTheory.DRFil

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem graded_const (TT : LocTied l P AI) (K : FinExt l) (n : ℤ)
    (e : P.R.BdR) (he : e ∈ (P.PD K).Fil n)
    (hg : ∀ g, (P.PD K).actdR g e - e ∈ (P.PD K).Fil (n + 1)) :
    ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil n ∧
      e - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil (n + 1) := by
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI TT
  by_cases hn : n = 0
  · subst hn
    rw [zero_add] at hg ⊢
    obtain ⟨y, hy, ey⟩ := GlobalTheory.MemLoc.invariants_finExt l K (Θ.θ e) (fun g hg' => by
      have h := (theta_sub_iff Θ K ((P.PD K).Fil_G _ _ _ he) he).1 (hg ⟨g, hg'⟩)
      rwa [P.PD_actdR, Θ.θ_act _ _ ((fil_iff _ _ _ _).1 he), GlobalTheory.MemLoc.locAinf_actC] at h)
    refine ⟨⟨y, hy⟩, alg_mem_fil_zero K _, ?_⟩
    rw [theta_sub_iff Θ K he (alg_mem_fil_zero K _), ← ey]
    exact (Θ.θ_Om y).symm
  · obtain ⟨κ, -, -, h0, h⟩ := graded_invariants TT Θ K n e he hg
    rw [h0 hn] at h
    exact ⟨0, by rw [map_zero]; exact Submodule.zero_mem _, by rwa [map_zero]⟩

theorem const_of_invariant_mod : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a b : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil a → (∀ g, (P.PD K).actdR g x - x ∈ (P.PD K).Fil b) → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧ x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil b := by
  intro l _ P AI TT K a b x hx hg
  have hFa : Antitone fun a => (P.PD K).Fil a :=
    antitone_int_of_succ_le fun a => (P.PD K).Fil_anti a
  have h0 : ∀ m, m ≤ a → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧
      x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil m := fun m hm =>
    ⟨0, by rw [map_zero]; exact Submodule.zero_mem _, by rw [map_zero, sub_zero]; exact hFa hm hx⟩
  rcases le_total b a with hba | hab
  · exact h0 b hba
  have key : ∀ m, a ≤ m → m ≤ b → ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil a ∧
      x - algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil m := by
    intro m hm
    induction m, hm using Int.leInduction with
    | base => exact fun _ => h0 a le_rfl
    | succ m hm ih =>
      intro hmb
      obtain ⟨c, hc, hxc⟩ := ih (by omega)
      obtain ⟨d, hd, hxd⟩ := graded_const TT K m _ hxc (fun g => by
        rw [map_sub, AlgEquiv.commutes, sub_sub_sub_cancel_right]
        exact hFa hmb (hg g))
      refine ⟨c + d, ?_, ?_⟩
      · rw [map_add (f := _)]
        exact Submodule.add_mem _ hc (hFa hm hd)
      · rwa [map_add, ← sub_sub]
  exact key b hab le_rfl

end GlobalTheory.FilInv
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

theorem _root_.GlobalTheory.T.deRham_comparison_isFiltered : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ (a : ℤ), ∀ y ∈ FilV (P.PD K) (LL := ↥LL.1) (V := V) a, ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ ∧ d i ∈ FilV (P.PD K) (LL := ↥LL.1) (V := V) (k i) ∧ b i ∈ (P.PD K).Fil (a - k i)) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  first | exact @GlobalTheory.DRFil.deRham_filtered | exact GlobalTheory.DRFil.deRham_filtered | (intros; apply GlobalTheory.DRFil.deRham_filtered <;> assumption)
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.AllLaws

theorem laws : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; Laws (HW l) (F l) h := by
  intro D HW F l _ K s LL h W E
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact ⟨GlobalTheory.T.wachLevelExpansionLaws_of_rootsOfUnity D HW l K s LL h, GlobalTheory.T.wach_etale_map_frobenius_galois_equivariant D HW F l K s LL h,
    GlobalTheory.TrivCrys.isCrys_lat_of_trivial W.one W.one_triv⟩

end GlobalTheory.NL.AllLaws
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.InvariantsKO

open IsDiscreteValuationRing

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

noncomputable def divBy (a : O) : O →ₗ[O] KmodO O :=
  (Submodule.mkQ _).comp ((LinearMap.mulLeft O ((algebraMap O (FractionRing O) a)⁻¹)).comp
    (Algebra.linearMap O (FractionRing O)))

theorem divBy_apply (a y : O) : divBy a y =
    Submodule.Quotient.mk ((algebraMap O (FractionRing O) a)⁻¹ * algebraMap O (FractionRing O) y) := rfl

theorem ker_divBy {a : O} (ha : a ≠ 0) : LinearMap.ker (divBy a) = Ideal.span {a} := by
  have h0 : algebraMap O (FractionRing O) a ≠ 0 := by simpa using ha
  ext y
  rw [LinearMap.mem_ker, divBy_apply, Ideal.mem_span_singleton]
  refine (Submodule.Quotient.mk_eq_zero _).trans ⟨?_, ?_⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, IsFractionRing.injective O (FractionRing O) ?_⟩
    have hb' : algebraMap O (FractionRing O) b =
      (algebraMap O (FractionRing O) a)⁻¹ * algebraMap O (FractionRing O) y := hb
    rw [map_mul, hb', mul_inv_cancel_left₀ h0]
  · rintro ⟨b, rfl⟩
    refine ⟨b, ?_⟩
    change algebraMap O (FractionRing O) b =
      (algebraMap O (FractionRing O) a)⁻¹ * algebraMap O (FractionRing O) (a * b)
    rw [map_mul, inv_mul_cancel_left₀ h0]

theorem mem_range_divBy {a : O} (ha : a ≠ 0) (x : KmodO O) (hx : a • x = 0) :
    x ∈ LinearMap.range (divBy a) := by
  have h0 : algebraMap O (FractionRing O) a ≠ 0 := by simpa using ha
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, ?_⟩
  rw [divBy_apply]
  congr 1
  have hy' : algebraMap O (FractionRing O) y = algebraMap O (FractionRing O) a * z := by
    rw [← Algebra.smul_def]; exact hy
  rw [hy', inv_mul_cancel_left₀ h0]

theorem length_le_of_smul_eq_zero {a : O} (ha : a ≠ 0) (P : Submodule O (KmodO O))
    (hP : ∀ x ∈ P, a • x = 0) : Module.length O P ≤ addVal O a := by
  have hle : P ≤ LinearMap.range (divBy a) := fun x hx => mem_range_divBy ha x (hP x hx)
  let f : P →ₗ[O] O ⧸ Ideal.span {a} :=
    (Submodule.quotEquivOfEq _ _ (ker_divBy ha)).toLinearMap.comp
      ((LinearMap.quotKerEquivRange (divBy a)).symm.toLinearMap.comp (Submodule.inclusion hle))
  have hf : Function.Injective f := by
    intro x y hxy
    have := (Submodule.quotEquivOfEq _ _ (ker_divBy ha)).injective hxy
    have := (LinearMap.quotKerEquivRange (divBy a)).symm.injective this
    exact Submodule.inclusion_injective hle this
  calc Module.length O P ≤ Module.length O (O ⧸ Ideal.span {a}) := Module.length_le_of_injective f hf
    _ = addVal O a := Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span a

theorem lenUnit_le_of_smul_eq_zero (l : ℕ) {a : O} (ha : a ≠ 0) (P : Submodule O (KmodO O))
    (hP : ∀ x ∈ P, a • x = 0) : lenUnit (O := O) l P ≤ lenUnit (O := O) l (O ⧸ Ideal.span {a}) := by
  unfold lenUnit
  have hne : Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
    rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]
    exact fun h => ha (addVal_eq_top_iff.mp h)
  have h1 : (Module.length O P).toNat ≤ (Module.length O (O ⧸ Ideal.span {a})).toNat :=
    ENat.toNat_le_toNat ((length_le_of_smul_eq_zero ha P hP).trans_eq
      (Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span a).symm) hne
  gcongr

end DVR

end GlobalTheory.InvariantsKO

namespace GlobalTheory.InvariantsKO

open IsDiscreteValuationRing

theorem lenUnit_invariants_le (D : D7) (i : D.nd.Loc) (hls : D.nd.l i ∉ D.host.small)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ) (hn : 0 < n) :
    lenUnit (O := D.nd.O i) (D.nd.l i)
        ↥(Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w))) ≤
      ((1 + padicValNat (D.nd.l i) n : ℕ) : ℚ) := by
  haveI := D.nd.lPrime i
  have hl2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hls
  obtain ⟨g, hgI, hg⟩ := GlobalTheory.PtCore.EpsAll.exists_generator (GlobalTheory.EpsInertia.epsAll D i) w hw
  have hgD : g ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := Ine_le_Dec _ hgI
  set b : (D.nd.O i)ˣ := Formalism.MainNotions.N.Glob.epsO D.nd i g with hbdef
  have hb : (b : D.nd.O i) = algebraMap ℤ_[D.nd.l i] (D.nd.O i)
      (1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ 1 * ((1 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i])) := by
    rw [Units.val_one, mul_one, ← UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i hls, ← hg]
    rfl
  set a : D.nd.O i := (b : D.nd.O i) ^ n - 1 with hadef
  have hva : addVal (D.nd.O i) a =
      ((1 + padicValNat (D.nd.l i) n : ℕ) : ℕ∞) * addVal (D.nd.O i) ((D.nd.l i : ℕ) : D.nd.O i) := by
    rw [hadef, hb]
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.addVal_pow_sub_one (O := D.nd.O i) (D.nd.l i) (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_ne_zero D.nd i)
      (Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.l_not_unit D.nd i) 1 le_rfl (fun h => absurd h hl2) 1 n hn
  have ha0 : a ≠ 0 := by
    intro h
    have ht : addVal (D.nd.O i) a = ⊤ := by rw [h]; simp
    rw [hva] at ht
    obtain ⟨e, he0, he⟩ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.exists_eO D.nd i
    rw [he] at ht
    exact absurd ht (by rw [← Nat.cast_mul]; exact ENat.coe_ne_top _)
  have hkill : ∀ x ∈ Representation.invariants ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w)),
      a • x = 0 := by
    intro x hx
    have hfix := (Representation.mem_invariants _ x).mp hx ⟨g, hgD⟩
    have hfix' : ((b ^ n)⁻¹ : (D.nd.O i)ˣ) • x = x := by
      have e1 : ((Formalism.MainNotions.N.Glob.KOtw D.nd i (n : ℤ)).comp (decS D.nd w)) ⟨g, hgD⟩ x =
          (((b ^ (-(n : ℤ)) : (D.nd.O i)ˣ)) : D.nd.O i) • x := by
        rfl
      rw [e1] at hfix
      rw [Units.smul_def, ← zpow_natCast, ← zpow_neg]
      exact hfix
    rw [hadef, sub_smul, one_smul]
    conv_lhs => rw [← hfix']
    rw [Units.smul_def, smul_smul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_smul, ← Units.smul_def, hfix', sub_self]
  calc lenUnit (O := D.nd.O i) (D.nd.l i) _
      ≤ lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {a}) :=
        lenUnit_le_of_smul_eq_zero (D.nd.l i) ha0 _ hkill
    _ = _ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.lenUnit_span D.nd i hva

end GlobalTheory.InvariantsKO

namespace GlobalTheory.InvariantsKO

theorem unbotD_le {m : WithBot ℚ} {c : ℚ} (h : m ≤ (c : WithBot ℚ)) (hc : 0 ≤ c) : m.unbotD 0 ≤ c := by
  cases m with
  | bot => simpa using hc
  | coe a => simpa using h

theorem one_add_padicValNat_le (l : ℕ) [Fact l.Prime] {n t : ℕ} (hn : 0 < n) (hnt : n < t) :
    1 + padicValNat l n ≤ 2 * t := by
  have h1 : l ^ padicValNat l n ≤ n := Nat.le_of_dvd hn (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have h2 : 2 ^ padicValNat l n ≤ l ^ padicValNat l n :=
    Nat.pow_le_pow_left (Fact.out : l.Prime).two_le _
  have h3 : padicValNat l n < 2 ^ padicValNat l n := Nat.lt_two_pow_self
  omega

theorem main : ∀ (D : D7) (i : D.nd.Loc) (col : Finset (HeightOneSpectrum (𝓞 D.host.E))), D.nd.l i ∉ D.host.small →
    D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → (∀ u ∈ col, u ∈ placesOver D.host.E (D.nd.l i)) →
    ((h0 D.nd i col : ℚ) : ℝ) ≤ 2 * D.R.t := by
  intro D i col hl2 _ _ hcol
  haveI := D.nd.lPrime i
  have key : h0 D.nd i col ≤ 2 * (D.R.t : ℚ) := by
    unfold h0
    refine unbotD_le ?_ (by positivity)
    apply Finset.max_le
    intro y hy
    obtain ⟨⟨w, n⟩, hp, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hw, hn⟩ := Finset.mem_product.mp hp
    obtain ⟨hn0, hnt⟩ := Finset.mem_Ioo.mp hn
    refine WithBot.coe_le_coe.mpr ((lenUnit_invariants_le D i hl2 w (hcol w hw) n hn0).trans ?_)
    exact_mod_cast one_add_padicValNat_le (D.nd.l i) hn0 hnt
  exact_mod_cast key

end GlobalTheory.InvariantsKO
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

theorem _root_.GlobalTheory.T.longOrbits_rowColength_inertLocalisation : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (C₂ : ℝ) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i), WachCoordinates.Conclusion2 D C₂ → 1 ≤ C₂ → EmbeddingTypeJumps.ParametersPolynomiallyBounded L → 11 ≤ D.nd.l i → LocalRepresentationBoundCondition L HW C₂ i r ρ π → TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc (lenRowB L C₂ (D.nd.l i)) := by
  first | exact @GlobalTheory.RowBLong.main | exact GlobalTheory.RowBLong.main | (intros; apply GlobalTheory.RowBLong.main <;> assumption)
end
