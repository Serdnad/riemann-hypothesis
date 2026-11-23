module

public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle016
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsBlockMapInitialVertex
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle011
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsValueAtZpow
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle117
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle015
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle097
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder ContDiff

namespace PositivityTheory.Xgp.c_bm_exists_boundary

open MvPolynomial Filter Topology

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem contDiff_nd (a : K → ℕ) : ContDiff ℝ ∞ (nd (J := J) a) := by
  unfold nd
  refine contDiff_prod fun k _ => ?_
  refine (ContDiff.sum fun i _ => ?_).pow _
  exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) _)

variable {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)

theorem smoothOn_pot {V : Set X} {ι' : Type} [Fintype ι'] (f : ι' → X → ℂ) (hf : ∀ j, A.HoloOn V (f j))
    (g : X → (Σ k, J k) → ℂ) (hg : ∀ p, A.HoloOn V (fun y => g y p)) (a : ι' → K → ℕ)
    (hnd : ∀ y ∈ V, ∀ j, 0 < nd (a j) (g y)) (hpos : ∀ y ∈ V, 0 < ∑ j, ‖f j y‖ ^ 2 / nd (a j) (g y)) (c : ℝ) :
    A.SmoothOn V (fun y => c - (1 / 2) * Real.log (∑ j, ‖f j y‖ ^ 2 / nd (a j) (g y))) := by
  intro ch t ht
  apply ContDiffAt.contDiffWithinAt
  have h1 : ∀ j, ContDiffAt ℝ ∞ (fun s => ‖f j ((A.chart ch).symm s)‖ ^ 2) t := fun j =>
    (contDiff_norm_sq ℝ).contDiffAt.comp t (((hf j ch t ht).contDiffAt).restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ ∞ (fun s => g ((A.chart ch).symm s)) t :=
    contDiffAt_pi.2 fun p => ((hg p ch t ht).contDiffAt).restrict_scalars ℝ
  have h3 : ∀ j, ContDiffAt ℝ ∞ (fun s => nd (a j) (g ((A.chart ch).symm s))) t := fun j =>
    (contDiff_nd (a j)).contDiffAt.comp t h2
  have hsum : ContDiffAt ℝ ∞ (fun s => ∑ j, ‖f j ((A.chart ch).symm s)‖ ^ 2 / nd (a j) (g ((A.chart ch).symm s))) t :=
    ContDiffAt.sum fun j _ => (h1 j).div (h3 j) (ne_of_gt (hnd _ ht.2 j))
  exact contDiffAt_const.sub (contDiffAt_const.mul (hsum.log (ne_of_gt (hpos _ ht.2))))

end PositivityTheory.Xgp.c_bm_exists_boundary
end

section

open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

open GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal GlobalTheory.CompanionTheory.Ar.PB.WSq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem exists_lift_gen {A F E : Type} [CommRing A] [Field F] [Field E] (a : A →+* F) (b : A →+* E)
    (hk : RingHom.ker a = RingHom.ker b) (gen : ∀ c, ∃ f g, c = a f / a g) : ∃ ψ : F →+* E, ∀ f, ψ (a f) = b f := by
  letI : Algebra (A ⧸ RingHom.ker a) F := (RingHom.kerLift a).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker a) F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective a)
  haveI : IsFractionRing (A ⧸ RingHom.ker a) F := IsFractionRing.of_field _ _ fun c => by
    obtain ⟨f, g, e⟩ := gen c
    exact ⟨Ideal.Quotient.mk _ f, Ideal.Quotient.mk _ g, e⟩
  let b' : A ⧸ RingHom.ker a →+* E := Ideal.Quotient.lift _ b fun f hf => by rwa [hk] at hf
  have hb' : Function.Injective b' := RingHom.lift_injective_of_ker_le_ideal _ _ hk.ge
  exact ⟨IsFractionRing.lift hb', fun f => IsFractionRing.lift_algebraMap hb' (Ideal.Quotient.mk _ f)⟩

def fibEquiv (ι : K → Type) (k₀ : K) :
    (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) ≃ ι k₀ where
  toFun
    | ⟨⟨some k, h⟩, _⟩ => absurd ⟨k, rfl⟩ h
    | ⟨⟨none, _⟩, m⟩ => m
  invFun m := ⟨⟨none, by rintro ⟨k, hk⟩; cases hk⟩, m⟩
  left_inv := by
    rintro ⟨⟨_ | k, h⟩, m⟩
    · rfl
    · exact absurd ⟨k, rfl⟩ h
  right_inv _ := rfl

theorem fibreBlock_subsingleton (k k' : FibreBlock (some : K → Option K)) : k = k' := by
  rcases k with ⟨_ | k, hk⟩
  · rcases k' with ⟨_ | k', hk'⟩
    · rfl
    · exact absurd ⟨k', rfl⟩ hk'
  · exact absurd ⟨k, rfl⟩ hk

theorem isMultiHomog_lin {F : Type} [Field F] (k₀ : K)
    (μ : (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) → F) :
    IsMultiHomog (∑ q, C (μ q) * X q : MRingOver F (fibreIdx (iW ι k₀) some)) fun _ => 1 := by
  intro s hs k
  obtain ⟨q, -, hq⟩ := Finset.mem_biUnion.1 (support_sum hs)
  rw [C_mul_X_eq_monomial] at hq
  have hs' := support_monomial_subset hq
  rw [Finset.mem_singleton] at hs'
  subst hs'
  obtain ⟨qk, qi⟩ := q
  obtain rfl : qk = k := fibreBlock_subsingleton _ _
  simp [Finsupp.single_apply]

variable {y : (Σ k, ι k) → Φ} {k₀ : K} {B : ι k₀ → Φ}

theorem cone_homog {E : Type} [Field E] (i₀ : MvPolynomial K Φ →+* E) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) : i₀ (mConeMap y g) = (∏ k, i₀ (X k) ^ d k) * i₀ (C (aeval y g)) := by
  have e : i₀.comp (mConeMap y).toRingHom =
      (aeval (fun p : Σ k, ι k => i₀ (X p.1) * ((i₀.comp C) ∘ y) p) : MRing ι →ₐ[ℤ] E).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) fun p => by simp [mConeMap, mul_comm]
  have := RingHom.congr_fun e g
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
  rw [this, aeval_scale' (fun k => i₀ (X k)) _ hg, CPts.aeval_comp_ringHom]
  rfl

theorem exists_positive_period_line {E : Type} [Field E] (i₀ : MvPolynomial K Φ →+* E) (hi : Function.Injective i₀)
    {cf : Φ} {e : K → ℤ} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e y c)
    (G : GenFibre (v₀ k₀) (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X))) :
    ∃ T : Set (MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K))),
      (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T := by
  let a : MRing ι →+* G.Φ := (aeval G.x : MRing ι →ₐ[ℤ] G.Φ).toRingHom
  have hka : RingHom.ker a = mCoordIdeal y := G.ker_x.trans (image_pen _ _ _ _ _)
  obtain ⟨ψ, hψ⟩ := exists_lift_gen a (i₀.comp (mConeMap y).toRingHom)
    (by rw [hka, RingHom.ker_comp_of_injective _ hi]; rfl)
    (fun c => by obtain ⟨f, g, -, e⟩ := G.gen c; exact ⟨f, g, e⟩)
  have lift : ∀ s v, HasVal y y s v → ∃ s', ψ s' = i₀ (C s) := by
    rintro s v ⟨d, g, h, hg, hh, h0, e, -⟩
    refine ⟨a g / a h, ?_⟩
    rw [map_div₀, hψ, hψ]
    show i₀ (mConeMap y g) / i₀ (mConeMap y h) = _
    have hp : (∏ k, i₀ (X k) ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ =>
      pow_ne_zero _ ((map_ne_zero_iff _ hi).2 (X_ne_zero _))
    have h1 : i₀ (C (aeval y h)) ≠ 0 := (map_ne_zero_iff _ hi).2 (by rwa [Ne, C_eq_zero])
    rw [cone_homog i₀ hg, cone_homog i₀ hh, mul_div_mul_left _ _ hp, e, map_mul, map_mul,
      mul_div_cancel_right₀ _ h1]
  choose p hp using fun m => lift _ _ (Fr.hp m)
  choose r hr using fun m => lift _ _ (Fr.hr m)
  choose α hα using fun m => lift _ _ (Fr.hα m)
  choose β hβ using fun m => lift _ _ (Fr.hβ m)
  let eF := fibEquiv ι k₀
  let ℓ : (Σ k : FibreBlock (some : K → Option K), fibreIdx (iW ι k₀) some k) → Fin 2 → G.Φ :=
    fun q => ![p (eF q), r (eF q)]
  have hν : ∀ a b : Fin 2, ∑ q, ![fun q => α (eF q), fun q => β (eF q)] a q * ℓ q b = if a = b then 1 else 0 := by
    have key : ∀ (u w : ι k₀ → G.Φ) (u' w' : ι k₀ → Φ) (s : G.Φ) (s' : Φ), (∀ m, ψ (u m) = i₀ (C (u' m))) →
        (∀ m, ψ (w m) = i₀ (C (w' m))) → ψ s = i₀ (C s') → ∑ m, u' m * w' m = s' →
        ∑ q, u (eF q) * w (eF q) = s := fun u w u' w' s s' hu hw hs h => by
      rw [Equiv.sum_comp eF fun m => u m * w m]
      apply ψ.injective
      rw [hs, ← h]

      simp only [map_sum, map_mul, hu, hw]
    intro a b
    fin_cases a <;> fin_cases b
    · exact key α p _ _ 1 1 hα hp (by simp) Fr.αp
    · exact key α r _ _ 0 0 hα hr (by simp) Fr.αr
    · exact key β p _ _ 0 0 hβ hp (by simp) Fr.βp
    · exact key β r _ _ 1 1 hβ hr (by simp) Fr.βr
  refine ⟨linKerForms ℓ, ?_, ?_⟩
  · rintro f ⟨μ, -, rfl⟩
    exact isMultiHomog_lin k₀ μ
  rw [← ker_linSubst ℓ _ hν]
  let W' : MRing (iW ι k₀) →+* MvPolynomial (Fin 2) E := (MvPolynomial.map i₀).comp (planeMap y k₀ Fr.p Fr.r)
  let x' : MRing (iW ι k₀) →+* G.Φ' := (aeval G.x' : MRing (iW ι k₀) →ₐ[ℤ] G.Φ').toRingHom
  have hker : RingHom.ker x' = RingHom.ker W' := by
    rw [RingHom.ker_comp_of_injective _ (MvPolynomial.map_injective _ hi), ← Fr.ker_eq, ← ideal_pen_plane]
    exact G.genericFibre_ker_target
  have r1 : ∀ f, x' (rename (v₀ k₀) f) = algebraMap G.Φ G.Φ' (a f) := fun f => by
    have e : x'.comp (rename (v₀ k₀) : MRing ι →ₐ[ℤ] MRing (iW ι k₀)).toRingHom = (algebraMap G.Φ G.Φ').comp a :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun q => by simpa [x', a] using G.compat q
    exact RingHom.congr_fun e f
  have r2 : ∀ f, W' (rename (v₀ k₀) f) = C (ψ (a f)) := fun f => by
    rw [hψ]
    have e : W'.comp (rename (v₀ k₀) : MRing ι →ₐ[ℤ] MRing (iW ι k₀)).toRingHom =
        (C : E →+* _).comp (i₀.comp (mConeMap y).toRingHom) :=
      MvPolynomial.ringHom_ext (fun r => by simp) fun q => by simp [W', planeMap, ext2, v₀, mConeMap]
    exact RingHom.congr_fun e f
  have main : ∀ f : MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K)), ∃ (Dn : MRing ι) (f' : MRing (iW ι k₀)),
      a Dn ≠ 0 ∧ x' f' = algebraMap G.Φ G.Φ' (a Dn) *
        aeval (fun q : Σ k : FibreBlock (some : K → Option K), iW ι k₀ k.1 => G.x' ⟨q.1.1, q.2⟩) f ∧
      W' f' = C (ψ (a Dn)) * MvPolynomial.map ψ (linSubst ℓ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C s =>
      obtain ⟨f, g, hg, e⟩ := G.gen s
      have e' : a f = a g * s := by rw [e]; exact (mul_div_cancel₀ _ hg).symm
      refine ⟨g, rename (v₀ k₀) f, hg, ?_, ?_⟩
      · rw [r1, e', map_mul, aeval_C]
      · rw [r2, e', map_mul, map_mul, algHom_C, algebraMap_eq, map_C]
    | add f g hf hg =>
      obtain ⟨D₁, f₁, h₁, a₁, b₁⟩ := hf
      obtain ⟨D₂, f₂, h₂, a₂, b₂⟩ := hg
      refine ⟨D₁ * D₂, f₁ * rename (v₀ k₀) D₂ + f₂ * rename (v₀ k₀) D₁, by rw [map_mul]; exact mul_ne_zero h₁ h₂,
        ?_, ?_⟩
      · simp only [map_add (f := _), map_mul, r1, a₁, a₂]; ring
      · simp only [map_add (f := _), map_mul, r2, b₁, b₂]; ring
    | mul_X f q hf =>
      obtain ⟨D₁, f₁, h₁, a₁, b₁⟩ := hf
      refine ⟨D₁, f₁ * X ⟨q.1.1, q.2⟩, h₁, ?_, ?_⟩
      · rw [map_mul, map_mul, a₁, aeval_X, mul_assoc]
        congr 2
        exact aeval_X _ _
      · rw [map_mul, map_mul, map_mul, b₁, mul_assoc]
        congr 2
        obtain ⟨m, rfl⟩ := eF.symm.surjective q
        have : W' (X ⟨none, m⟩) = C (i₀ (C (Fr.p m))) * X 0 + C (i₀ (C (Fr.r m))) * X 1 := by
          simp [W', planeMap, ext2]
        refine this.trans ?_
        simp [linSubst, ℓ, Fin.sum_univ_two, hp, hr]
  ext f
  obtain ⟨Dn, f', h0, h1, h2⟩ := main f
  have h3 : x' f' = 0 ↔ W' f' = 0 := SetLike.ext_iff.1 hker f'
  rw [h1, h2, mul_eq_zero, mul_eq_zero, or_iff_right ((map_ne_zero _).2 h0),
    or_iff_right (by rw [C_eq_zero]; exact (map_ne_zero _).2 h0),
    map_eq_zero_iff _ (MvPolynomial.map_injective _ ψ.injective)] at h3
  exact h3

theorem line_pen {cf : Φ} {e : K → ℤ} {c : ∀ k, ι k} (Fr : PenFrame y k₀ B cf e y c)
    (G : GenFibre (v₀ k₀) (mCoordIdeal (penCo y k₀ (fun m => y ⟨k₀, m⟩) B RatFunc.X))) :
    ∃ T : Set (MRingOver G.Φ (fibreIdx (iW ι k₀) (some : K → Option K))),
      (∀ f ∈ T, IsMultiHomog f fun _ => 1) ∧ fibreIdeal (some : K → Option K) G = Ideal.span T :=
  exists_positive_period_line (algebraMap _ (FractionRing (MvPolynomial K Φ))) (IsFractionRing.injective _ _) Fr G

end PositivityTheory.Xgp.W
end
end

section

open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_hom

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {M : FlagModel y Ψ N j}
variable {Gr : FrameData ι Ψ N M.Ω M.blk → Ψ → ((Σ k, baseIdx ι M.blk k) → ℂ) → Matrix (Fin N) (Fin N) ℂ → Prop}

theorem sum_dy (p : Ψ × Fin N) (L : K → ℝ) :
    ∑ k, (M.dy p k : ℝ) * L k = (M.blk p).elim 0 L - ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * L k'.1 := by
  have e1 : ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * L k'.1 =
      ∑ k, if h : ∀ p', M.blk p' ≠ some k then (M.b p ⟨k, h⟩ : ℝ) * L k else 0 :=
    Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
      (fun k hk => dif_neg fun h => hk ⟨⟨k, h⟩, rfl⟩) (fun k => by rw [dif_pos k.2])
  have e2 : (M.blk p).elim 0 L = ∑ k, if M.blk p = some k then L k else 0 := by
    cases M.blk p with
    | none => simp
    | some k => simp
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold FlagModel.dy
  by_cases h : ∀ p', M.blk p' ≠ some k
  · rw [dif_pos h, dif_pos h, if_neg (h p)]; simp
  · rw [dif_neg h, dif_neg h]; split_ifs <;> simp

theorem Rel.smul
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (htor : ∀ F τ w G (c : NonPluckerBlocks M.blk → ℂ), (∀ k, c k ≠ 0) → Gr F τ w G → Gr F τ (torusSmul c w) G)
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r : ℝ} (h1 : Rel M Gr p z r) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    Rel M Gr p (torusSmul c z) (r + ∑ k, (M.dy p k : ℝ) * Real.log ‖c k‖) := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨hF, hw, gd, -, -⟩ := hgood _ _ _ _ hG
  have hG' := htor _ _ _ _ (fun k => c k.1) (fun k => hc _) hG
  have eb : basePart M.blk (torusSmul c z) = torusSmul (fun k => c k.1) (basePart M.blk z) := rfl
  have ev : ∀ s, valAt M.x s (basePart M.blk (torusSmul c z)) = valAt M.x s (basePart M.blk z) := fun s =>
    GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit _ _ _ M.x s _ _ (hgood _ _ _ _ hG').2.1
      ⟨fun k => c k.1, fun k => hc _, rfl⟩
  have el : ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk (torusSmul c z) ⟨k', F.c k'⟩‖ =
      ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * Real.log ‖c k'.1‖ +
        ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk z ⟨k', F.c k'⟩‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eb, torusSmul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc _)) (norm_ne_zero_iff.2 (ne_of_notMem (gd.1 k)))]
    ring
  refine ⟨F, G, hG', h, bh, dh, t + (M.blk p).elim 0 (fun k => Real.log ‖c k‖), ?_, ?_⟩
  · rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩
    · refine Or.inl ⟨k, c k * a, hk, mul_ne_zero (hc k) ha, fun m => ?_, ?_⟩
      · simp only [ev]
        rw [torusSmul, hz m, mul_assoc]
      · rw [hk, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc _)) (norm_ne_zero_iff.2 ha), Option.elim_some, add_comm]
    · refine Or.inr ⟨hk, ?_⟩
      rw [hk, ev, Option.elim_none, add_zero]
  · rw [el, sum_dy]
    ring

theorem Rel.conj
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (hconj : ∀ F τ w G, Gr F τ w G → Gr F τ (conjVec w) (G.map (starRingEnd ℂ)))
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r : ℝ} (h1 : Rel M Gr p z r) : Rel M Gr p (conjVec z) r := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨hF, hw, gd, -, -⟩ := hgood _ _ _ _ hG
  have hG' := hconj _ _ _ _ hG
  have hw' := (hgood _ _ _ _ hG').2.1
  have eb : basePart M.blk (conjVec z) = conjVec (basePart M.blk z) := rfl
  refine ⟨F, _, hG', h.map (starRingEnd ℂ), bh.map _, ?_, t, ?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 dh
  · rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩
    · refine Or.inl ⟨k, starRingEnd ℂ a, hk, (map_ne_zero _).2 ha, fun m => ?_, by simp⟩

      rw [conjVec, hz m, map_mul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [map_mul, eb, valAt_conj hw hw' (gd.2.1 _ I).1, minorIJ_map]
    · refine Or.inr ⟨hk, ?_⟩
      rw [eb, valAt_conj hw hw' (gd.2.2 p hk).2.1, RCLike.norm_conj]
  · rw [pot_conj]
    simp only [eb, conjVec, RCLike.norm_conj]

theorem exists_hom
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (htor : ∀ F τ w G (c : NonPluckerBlocks M.blk → ℂ), (∀ k, c k ≠ 0) → Gr F τ w G → Gr F τ (torusSmul c w) G)
    (hconj : ∀ F τ w G, Gr F τ w G → Gr F τ (conjVec w) (G.map (starRingEnd ℂ)))
    (hcomp : ∀ F F' τ w G G', Gr F τ w G → Gr F' τ w G' → ∃ Rz : Matrix (Fin N) (Fin N) ℂ,
      (∀ a b, IsValueAt M.x (((F.T τ)⁻¹ * F'.T τ) a b) w (Rz a b)) ∧ Rz.det ≠ 0 ∧ G' = Rzᴴ * G * Rz)
    (p : Ψ × Fin N) : ∃ A : HermLine ι, A.a = M.dy p ∧
      (∀ F w G, Gr F p.1 w G → M.IsInducedAt F w p G A) ∧ ∀ z, A.h (conjVec z) = A.h z := by
  let f : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    if h : ∃ r, Rel M Gr p z r then Real.exp h.choose else refNorm (M.dy p) z
  have fr : ∀ z r, Rel M Gr p z r → f z = Real.exp r := fun z r h => by
    have hex : ∃ r, Rel M Gr p z r := ⟨r, h⟩
    simp only [f, dif_pos hex]
    rw [Rel.unique hgood hcomp hex.choose_spec h]
  refine ⟨⟨M.dy p, f, fun z hz => ?_, fun c z hc => ?_⟩, rfl, fun F w G hG z hz ho hn h bh dh => ?_, fun z => ?_⟩
  · simp only [f]
    split_ifs
    exacts [Real.exp_pos _, refNorm_pos _ hz]
  · change f (torusSmul c z) = _
    by_cases h : ∃ r, Rel M Gr p z r
    · obtain ⟨r, h⟩ := h
      rw [fr _ _ h, fr _ _ (h.smul hgood htor hc), Real.exp_add, mul_comm, Real.exp_sum]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Real.log_zpow, Real.exp_log (zpow_pos (norm_pos_iff.2 (hc k)) _)]
    · have h' : ¬ ∃ r, Rel M Gr p (torusSmul c z) r := by
        rintro ⟨r, hr⟩
        have := hr.smul hgood htor (c := fun k => (c k)⁻¹) fun k => inv_ne_zero (hc k)
        have e : torusSmul (fun k => (c k)⁻¹) (torusSmul c z) = z := by
          funext q; simp [torusSmul, hc]
        rw [e] at this
        exact h ⟨_, this⟩
      simp only [f, dif_neg h, dif_neg h']
      exact refNorm_smul _ _ _
  · obtain ⟨c, hc, e⟩ := ho
    have hG' : Gr F p.1 (basePart M.blk z) G := by
      rw [e]; exact htor _ _ _ _ c hc hG
    refine ⟨fun k hk hz => ?_, fun hk => ?_⟩
    · show Real.log (f z) = _
      rw [fr z _ ⟨F, G, hG', h, bh, dh, _, Or.inl ⟨k, 1, hk, one_ne_zero, fun m => by rw [one_mul, hz m], rfl⟩, rfl⟩,
        Real.log_exp]
      simp [hn]
    · show Real.log (f z) = _
      rw [fr z _ ⟨F, G, hG', h, bh, dh, _, Or.inr ⟨hk, rfl⟩, rfl⟩, Real.log_exp]
      simp only [hn, norm_one, Real.log_one, mul_zero, Finset.sum_const_zero]
      ring
  · show f _ = f z
    by_cases h : ∃ r, Rel M Gr p z r
    · obtain ⟨r, h⟩ := h
      rw [fr _ _ h, fr _ _ (h.conj hgood hconj)]
    · have h' : ¬ ∃ r, Rel M Gr p (conjVec z) r := by
        rintro ⟨r, hr⟩
        have := hr.conj hgood hconj
        have e : conjVec (conjVec z) = z := by
          funext q; simp [conjVec]
        rw [e] at this
        exact h ⟨_, this⟩
      simp only [f, dif_neg h, dif_neg h']
      simp [refNorm, conjVec]

end PositivityTheory.Xgp.c_bm_exists_hom
end
end
