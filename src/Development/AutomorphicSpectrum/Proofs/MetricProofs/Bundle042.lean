module

import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCGradAtlas
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TendstoLocallyUniformlyOnOfNhds
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle036
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle068
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesA
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

theorem isOpen_compl_bdry {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {L : LocPot X} {s : X → X → ℂ} (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  apply PositivityTheory.Xgp.c_grad_atlas.isOpen_compl_bdry <;> assumption

theorem regular_family_C2_pullback_of_open {e e' : ℕ} {X X' : Type} [TopologicalSpace X] [TopologicalSpace X']
    (A : FinHolAtlas e X) (A' : FinHolAtlas e' X') (h : X' → X) (hh : HoloMap A' A h)
    (s : X → X → ℂ) (ph : X → ℝ) (phT : ℝ → X → ℝ) (hO : IsOpen (bdry s)ᶜ)
    (hph : A.SmoothOn (bdry s)ᶜ ph)
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), A.Smooth (phT t))
    (hC : IsRegFamilyC2 A s ph phT) :
    IsRegFamilyC2 A' (fun x y => s (h x) (h y)) (ph ∘ h) (fun t => phT t ∘ h) := by
  have key := GroundTheory.Heights₂.Heights.AnalyticLimit.C2ConvergencePullback.proof A' A h hh (bdry s)ᶜ hO phT ph
    (ph ∘ h) hph (fun _ _ => rfl) hT (fun k K hK hKs => hC k K hKs hK)
  intro j K hKs hK
  exact key j K hK hKs

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem _root_.GlobalTheory.T.inChart_iff_of_dominates' : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (i : Ω →+* G) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c₁ p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_iff_of_dominates | exact GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_iff_of_dominates | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.inChart_iff_of_dominates <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem _root_.GlobalTheory.T.lattice_pull_split_injection : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (E E₁ : Type) [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] (ι : E →ₗ[Ω] E₁) (π : E₁ →ₗ[Ω] E) (L : Lat ξ E) (r : ℕ) (c : Fin r → E) (u : Matrix (Fin r) (Fin r) G), π ∘ₗ ι = LinearMap.id → ((L.map ι).pull ξ' f (TensorProduct.mk Ω G E₁ 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G E₁ 1 (ι (c l))) → (L.pull ξ' f (TensorProduct.mk Ω G E 1).toAddMonoidHom).IsFlagVBOn Set.univ (fun k => ∑ l, u l k • TensorProduct.mk Ω G E 1 (c l)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.PullMap.isFlagVBOn_pull_of_map | exact GlobalTheory.CompanionTheory.Ar.FlagBun.PullMap.isFlagVBOn_pull_of_map | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.PullMap.isFlagVBOn_pull_of_map <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LineDefect

open MvPolynomial AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

section Alg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem map_aeval_int {σ R R' : Type} [CommRing R] [CommRing R'] (ψ : R →+* R') (a : σ → R)
    (s : MvPolynomial σ ℤ) : ψ (aeval a s) = aeval (fun p => ψ (a p)) s := by
  have := MvPolynomial.comp_aeval_apply (R := ℤ) a ψ.toIntAlgHom s
  simpa using this

theorem aeval_eq_eval₂ {σ R : Type} [CommRing R] [Algebra ℤ R] (a : σ → R) (s : MvPolynomial σ ℤ) :
    aeval a s = eval₂ (Int.castRingHom R) a s := by
  rw [aeval_def]
  congr 1
  exact Subsingleton.elim _ _

theorem prod_cross {F : Type} [Field F] (x : K → F) (hx : ∀ k, x k ≠ 0) {a b : K → ℤ} {α γ : K → ℕ}
    (hd : ∀ k, (α k : ℤ) - γ k = a k - b k) :
    (∏ k, x k ^ a k) * ∏ k, x k ^ γ k = (∏ k, x k ^ b k) * ∏ k, x k ^ α k := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hx k), ← zpow_add₀ (hx k)]
  congr 1
  linarith [hd k]

variable {Ω : Type} [Field Ω]

theorem cone_of_form {R : Type} [CommRing R] (b : (Σ k, ι k) → R) {s : MRing ι} {d : K → ℕ}
    (hs : IsMultiHomog s d) :
    aeval (fun p => (MvPolynomial.X p.1 : MvPolynomial K R) * MvPolynomial.C (b p)) s =
      (∏ k, MvPolynomial.X k ^ d k) * MvPolynomial.C (aeval b s) := by
  have h := aeval_blockScale hs (fun k => (MvPolynomial.X k : MvPolynomial K R)) fun p => MvPolynomial.C (b p)
  rw [map_aeval_int MvPolynomial.C b s]
  simp only [aeval_eq_eval₂] at h ⊢
  exact h

theorem aeval_ne_zero_of_form {y : (Σ k, ι k) → Ω} {s : MRing ι} {d : K → ℕ} (hs : IsMultiHomog s d)
    (h : s ∉ mCoordIdeal y) : aeval y s ≠ 0 := by
  intro h0
  refine h ?_
  change mConeMap y s = 0
  have e : mConeMap y s = aeval (fun p => (MvPolynomial.X p.1 : MvPolynomial K Ω) * MvPolynomial.C (y p)) s := by
    simp only [mConeMap, mul_comm]
  rw [e, cone_of_form y hs, h0, map_zero, mul_zero]

variable (S : Subring Ω) (φ : S →+* ℂ) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (w : (Σ k, ι k) → ℂ)
  (r : (Σ k, ι k) → S)

def coneS : MRing ι →ₐ[ℤ] MvPolynomial K S :=
  aeval fun p => MvPolynomial.X p.1 * MvPolynomial.C (r p)

def evS : MvPolynomial K S →+* ℂ := eval₂Hom φ fun k => w ⟨k, c k⟩

variable {S φ y c w r}

theorem coneS_eq_zero (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hr : ∀ p, (r p : Ω) * y ⟨p.1, c p.1⟩ = y p) {s : MRing ι}
    (hs : s ∈ mCoordIdeal y) : coneS S r s = 0 := by
  have hJ : Function.Injective (MvPolynomial.map (σ := K) S.subtype) :=
    MvPolynomial.map_injective _ Subtype.val_injective
  refine hJ ?_
  rw [map_zero]
  let Res : MvPolynomial K Ω →+* MvPolynomial K Ω :=
    eval₂Hom MvPolynomial.C fun k => MvPolynomial.C (y ⟨k, c k⟩)⁻¹ * MvPolynomial.X k
  have e : (MvPolynomial.map (σ := K) S.subtype).comp (coneS S r).toRingHom = Res.comp (mConeMap y).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) fun p => ?_
    have h1 : ((r p : S) : Ω) = y p * (y ⟨p.1, c p.1⟩)⁻¹ := by
      rw [← hr p, mul_inv_cancel_right₀ (hy p.1)]
    simp [coneS, mConeMap, Res, h1]
    ring
  have h0 : mConeMap y s = 0 := hs
  have := RingHom.congr_fun e s
  simpa [h0] using this

theorem evS_coneS (hw : ∀ p, w ⟨p.1, c p.1⟩ * φ (r p) = w p) (s : MRing ι) :
    evS S φ c w (coneS S r s) = evC w s := by
  have e : (evS S φ c w).comp (coneS S r).toRingHom =
      (MvPolynomial.eval w).comp (MvPolynomial.map (Int.castRingHom ℂ)) := by
    refine MvPolynomial.ringHom_ext (fun n => by simp) fun p => ?_
    simp [coneS, evS, hw p]
  exact RingHom.congr_fun e s

theorem core (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (hr : ∀ p, (r p : Ω) * y ⟨p.1, c p.1⟩ = y p)
    (hw : ∀ p, w ⟨p.1, c p.1⟩ * φ (r p) = w p) {f g u v : MRing ι} {α γ : K → ℕ} (hf : IsMultiHomog f α)
    (hg : IsMultiHomog g γ) (hG : aeval r g ≠ 0) (huv : u * f - v * g ∈ mCoordIdeal y) {s₁ s₂ : S}
    (hs : s₂ * aeval r f = s₁ * aeval r g) :
    evC w u * φ s₁ * ∏ k, w ⟨k, c k⟩ ^ α k = evC w v * φ s₂ * ∏ k, w ⟨k, c k⟩ ^ γ k := by
  have h0 := coneS_eq_zero hy hr huv
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h0
  have hcf : coneS S r f = (∏ k, MvPolynomial.X k ^ α k) * MvPolynomial.C (aeval r f) := cone_of_form r hf
  have hcg : coneS S r g = (∏ k, MvPolynomial.X k ^ γ k) * MvPolynomial.C (aeval r g) := cone_of_form r hg
  have hCG : (MvPolynomial.C (aeval r g) : MvPolynomial K S) ≠ 0 := by
    exact (map_ne_zero_iff (MvPolynomial.C : S →+* MvPolynomial K S) (MvPolynomial.C_injective K S)).2 hG
  have hcs : (MvPolynomial.C s₂ : MvPolynomial K S) * MvPolynomial.C (aeval r f) =
      MvPolynomial.C s₁ * MvPolynomial.C (aeval r g) := by
    rw [← map_mul, ← map_mul, hs]
  have key : coneS S r u * MvPolynomial.C s₁ * (∏ k, MvPolynomial.X k ^ α k) =
      coneS S r v * MvPolynomial.C s₂ * ∏ k, MvPolynomial.X k ^ γ k := by
    refine mul_left_cancel₀ hCG ?_
    rw [hcf, hcg] at h0
    linear_combination (MvPolynomial.C s₂) * h0 - (coneS S r u * ∏ k, MvPolynomial.X k ^ α k) * hcs
  have := congrArg (evS S φ c w) key
  rw [map_mul, map_mul, map_mul, map_mul, evS_coneS hw, evS_coneS hw] at this
  simpa [evS, map_prod] using this

end Alg

theorem norm_mul_h_eq : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (A B : HermLine ι) (e₀ ρ t : Ω) (f g u v : MRing ι) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, ι k) → ℂ) (ν : ℝ), IsCptGen ξ → CoordsAt ξ y z w → e₀ ≠ 0 → IsLineIso (mCoordIdeal y) A.a B.a f g → aeval y f = ρ * aeval y g → SecNorm ξ y A e₀ z w t ν → SecNorm ξ y B (ρ * e₀) z w t ν → 0 < ν → u * f - v * g ∈ mCoordIdeal y → evC w u ≠ 0 → ‖evC w v‖ * B.h w = ‖evC w u‖ * A.h w := by
  intro X Ω _ ξ K _ ι _ y A B e₀ ρ t f g u v z w ν hξ hw he hiso hρ hA hB hν huv _
  obtain ⟨⟨α, γ, hf, hg, hd⟩, hfP, hgP, -⟩ := hiso
  obtain ⟨c, hc⟩ := hA.exists_chart
  have hz := hA.specializes
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom X Ω ξ ℂ z hz hξ
  obtain ⟨a₁, ha₁, e₁⟩ := hA.2.2 c hc
  obtain ⟨a₂, ha₂, e₂⟩ := hB.2.2 c hc
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  choose q hq hq' using fun p : Σ k, ι k => (hw.2 p.1 (c p.1) (IsUnit.mk0 _ (hc p.1))).2 p.2
  choose m hm using fun p => (hφ _ _).1 (hq p)
  obtain ⟨m₁, hm₁⟩ := (hφ _ _).1 ha₁
  obtain ⟨m₂, hm₂⟩ := (hφ _ _).1 ha₂
  set r : (Σ k, ι k) → regAt ξ ⟨centre z, hz⟩ := fun p => ⟨_, m p⟩ with hrdef
  have hr : ∀ p, (r p : Ω) * y ⟨p.1, c p.1⟩ = y p := fun p => div_mul_cancel₀ _ (hy p.1)
  have hwr : ∀ p, w ⟨p.1, c p.1⟩ * φ (r p) = w p := fun p => by
    rw [hm p, mul_comm]
    exact (hq' p).symm
  have hyf : aeval y f ≠ 0 := aeval_ne_zero_of_form hf hfP
  have hyg : aeval y g ≠ 0 := aeval_ne_zero_of_form hg hgP
  have hρ0 : ρ ≠ 0 := fun h => hyf (by rw [hρ, h, zero_mul])
  have hscale : ∀ {s : MRing ι} {d : K → ℕ}, IsMultiHomog s d →
      aeval y s = (∏ k, y ⟨k, c k⟩ ^ d k) * (aeval r s : regAt ξ ⟨centre z, hz⟩) := by
    intro s d hs
    have h1 := aeval_blockScale hs (fun k => y ⟨k, c k⟩) fun p => (r p : Ω)
    have e : (fun p : Σ k, ι k => y ⟨p.1, c p.1⟩ * (r p : Ω)) = y :=
      funext fun p => (mul_comm _ _).trans (hr p)
    rw [e] at h1
    rw [h1]
    congr 1
    exact (map_aeval_int (regAt ξ ⟨centre z, hz⟩).subtype r s).symm
  have hF := hscale hf
  have hG := hscale hg
  have hQα : (∏ k, y ⟨k, c k⟩ ^ α k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have hQγ : (∏ k, y ⟨k, c k⟩ ^ γ k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have hPA : (∏ k, y ⟨k, c k⟩ ^ A.a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hPB : (∏ k, y ⟨k, c k⟩ ^ B.a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hP := prod_cross (fun k => y ⟨k, c k⟩) hy hd
  have hGne : aeval r g ≠ 0 := fun h => hyg (by rw [hG, h]; simp)
  have hs : (⟨_, m₂⟩ : regAt ξ ⟨centre z, hz⟩) * aeval r f = ⟨_, m₁⟩ * aeval r g := by
    apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul]
    change t / ((∏ k, y ⟨k, c k⟩ ^ B.a k) * (ρ * e₀)) * _ = t / ((∏ k, y ⟨k, c k⟩ ^ A.a k) * e₀) * _
    have hFG := hρ
    rw [hF, hG] at hFG
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero hPB (mul_ne_zero hρ0 he))
      (mul_ne_zero hPA he)]
    have key : ((aeval r f : regAt ξ ⟨centre z, hz⟩) : Ω) * (∏ k, y ⟨k, c k⟩ ^ A.a k) =
        ((aeval r g : regAt ξ ⟨centre z, hz⟩) : Ω) * (∏ k, y ⟨k, c k⟩ ^ B.a k) * ρ :=
      mul_right_cancel₀ hQγ (by
        linear_combination ((aeval r f : regAt ξ ⟨centre z, hz⟩) : Ω) * hP + (∏ k, y ⟨k, c k⟩ ^ B.a k) * hFG)
    linear_combination (t * e₀) * key
  have hcore := core (φ := φ) hy hr hwr hf hg hGne huv hs
  rw [hm₁, hm₂] at hcore
  have hn := congrArg norm hcore
  simp only [norm_mul, norm_prod, norm_pow] at hn
  have hNγ : (∏ k, ‖w ⟨k, c k⟩‖ ^ γ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  have hN := prod_cross (fun k => ‖w ⟨k, c k⟩‖) (fun k => norm_ne_zero_iff.2 (hc k)) hd
  refine mul_right_cancel₀ hNγ (mul_left_cancel₀ hν.ne' ?_)
  linear_combination (‖evC w v‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ γ k) * e₂ - (‖evC w u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ γ k) * e₁ -
    (∏ k, ‖w ⟨k, c k⟩‖ ^ B.a k) * hn - (‖evC w u‖ * ‖a₁‖) * hN

end GlobalTheory.CompanionTheory.Ar.LineDefect
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.line_isomorphism_defect_function : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e) (A B : HermLine ι) (f g : MRing ι), IsMultiProjPrime P → IsLineIso P A.a B.a f g → IsSmoothHerm A → IsSmoothHerm B → ∃ w : ((Σ k, ι k) → ℂ) → ℝ, IsDefectOn P (mcPts P) f g A B w ∧ (∀ z ∈ mcPts P, ∀ z', SameOrbit z z' → w z = w z') ∧ R.A.Smooth (fun x => w (R.lift x x)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.defect_exists_smooth | exact GlobalTheory.CompanionTheory.Ar.Cmp.defect_exists_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.defect_exists_smooth <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_basicOpen_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)), IsSncModel y e J → ∀ p : (k : K) → ι k, (∀ k, y ⟨k, p k⟩ ≠ 0) → ∀ t : (Σ k, ι k) → ℂ, (∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G = 0 → eval t (map (algebraMap ℚ ℂ) G) = 0) → ∃ (F : MvPolynomial (Σ k, ι k) ℚ) (S : Subalgebra ℚ Ω) (z : Fin e → S) (n : ℕ), aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F ≠ 0 ∧ eval t (map (algebraMap ℚ ℂ) F) ≠ 0 ∧ S = Algebra.adjoin ℚ (insert (aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) F)⁻¹ (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩))) ∧ Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧ ∀ q : Ideal S, q.IsPrime → ((∀ g ∈ J, ∀ s : S, (s : Ω) = aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) g → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by
  intro K _ ι _ Ω _ _ y e J h p hp t ht
  obtain ⟨m, f, a, hf, ha, hsum, hcl⟩ := h p hp
  rw [Algebra.adjoin_range_eq_range_aeval] at hf ha
  choose F hF using fun l => AlgHom.mem_range _ |>.1 (hf l)
  choose A hA using fun l => AlgHom.mem_range _ |>.1 (ha l)
  obtain rfl : f = fun l => aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (F l) :=
    funext fun l => (hF l).symm
  have hker : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (∑ l, A l * F l - 1) = 0 := by

    simp only [map_sub, map_sum, map_mul, map_one, hA]
    exact sub_eq_zero.2 hsum
  have h1 := ht _ hker

  simp only [map_sub, map_sum, map_mul, map_one] at h1
  obtain ⟨l, hl⟩ : ∃ l, eval t (map (algebraMap ℚ ℂ) (F l)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    simp [hc] at h1
  have hfl : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) (F l) ≠ 0 := fun h0 => hl (ht _ h0)
  obtain ⟨-, z, n, -, -, hspan, hq⟩ := hcl l hfl _ rfl
  exact ⟨F l, _, z, n, hfl, hl, rfl, hspan, hq⟩

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem hessC_finset_sum_mul {D : ℕ} {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hf : ∀ a, ContDiffAt ℝ 2 (f a) z) :
    hessC (fun y => ∑ a ∈ s, c a * f a y) z = ∑ a ∈ s, (c a : ℂ) • hessC (f a) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using st_hessC_eq_zero (f := fun _ => (0 : ℝ)) (y := z) 0 (Eventually.of_forall fun _ => rfl)
  | insert a s ha ih =>
    have h1 : ContDiffAt ℝ 2 (fun y => c a * f a y) z := contDiffAt_const.mul (hf a)
    have h2 : ContDiffAt ℝ 2 (fun y => ∑ b ∈ s, c b * f b y) z :=
      ContDiffAt.sum fun b _ => contDiffAt_const.mul (hf b)
    simp only [Finset.sum_insert ha]
    rw [hessC_add' _ _ z h1 h2, ih, hessC_const_mul']

theorem mdisc_sum_smul {D : ℕ} {σ : Type*} [Fintype σ] (H : σ → Matrix (Fin D) (Fin D) ℂ)
    (c : Fin D → σ → ℂ) :
    mdisc (fun i => ∑ a, c i a • H a) =
      ∑ w : Fin D → σ, (∏ i, c i (w i)) * mdisc (fun i => H (w i)) := by
  classical
  obtain ⟨M, hM⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))

  rw [← hM, M.map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [M.map_smul_univ, RingHom.id_apply, smul_eq_mul]

theorem locDens_sumPot_expand {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {σ : Type} [Fintype σ] (P : σ → LocPot X) (c : Fin e → σ → ℝ) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target)
    (hC : ∀ a, IsTwiceDifferentiableAt A (P a) ((A.chart j).symm y)) :
    locDens A (fun i => sumPot (c i) P) j y =
      ∑ w : Fin e → σ, (∏ i, c i (w i)) * locDens A (fun i => P (w i)) j y := by
  classical
  have hf : ∀ a, ContDiffAt ℝ 2
      (fun y' => (P a).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    intro a
    have := hC a j ((A.chart j).map_target hy)
    rwa [(A.chart j).right_inv hy] at this
  have hH : ∀ i, hessC (fun y' => (sumPot (c i) P).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      ∑ a, ((c i a : ℝ) : ℂ) •
        hessC (fun y' => (P a).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := fun i =>
    hessC_finset_sum_mul Finset.univ (c i) _ y hf
  simp only [locDens, maDens, hH]
  rw [mdisc_sum_smul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Complex.ofReal_prod, Complex.re_ofReal_mul]
  ring

theorem mInt_sumPot_expand (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (σ : Type) [Fintype σ] (U : Set X) (P : σ → LocPot X)
    (c : Fin e → σ → ℝ) (g : X → ℝ) (hN : IsNull A Uᶜ)
    (hC : ∀ a, ∀ x ∈ U, IsTwiceDifferentiableAt A (P a) x)
    (hI : ∀ w : Fin e → σ, MIntegrable A (fun i => P (w i)) g) :
    MIntegrable A (fun i => sumPot (c i) P) g ∧
      mInt A (fun i => sumPot (c i) P) g =
        ∑ w : Fin e → σ, (∏ i, c i (w i)) * mInt A (fun i => P (w i)) g := by
  classical
  have key : ∀ j, ∀ᵐ y, y ∈ (A.chart j).target →
      locDens A (fun i => sumPot (c i) P) j y =
        ∑ w : Fin e → σ, (∏ i, c i (w i)) * locDens A (fun i => P (w i)) j y := by
    intro j
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN j)] with y hy hyt
    have hU : (A.chart j).symm y ∈ U := by
      by_contra h
      exact hy ⟨hyt, h⟩
    exact locDens_sumPot_expand A P c j hyt fun a => hC a _ hU
  refine ⟨fun j K hK hKc => ?_, ?_⟩
  · have h1 : IntegrableOn (fun y => ∑ w : Fin e → σ, (∏ i, c i (w i)) *
        (g ((A.chart j).symm y) * locDens A (fun i => P (w i)) j y)) K :=
      integrable_finsetSum _ fun w _ => (hI w j K hK hKc).const_mul _
    refine Integrable.congr h1 ?_
    filter_upwards [ae_restrict_of_ae (key j), ae_restrict_mem hKc.measurableSet] with y hy hyK
    rw [hy (hK hyK), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring
  · have h : Nonempty (ChartPartition A) := existsPartition A
    simp only [mInt, dif_pos h, integralWith]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hw : ∀ w : Fin e → σ, IntegrableOn (fun y => (∏ i, c i (w i)) *
        (h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
          locDens A (fun i => P (w i)) j y)) (A.chart j).target := fun w =>
      (integrableOn_weight A h.some _ g (hI w) j).const_mul _
    simp only [← integral_const_mul]
    rw [← integral_finsetSum _ fun w _ => hw w]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (key j),
      ae_restrict_mem (A.chart j).open_target.measurableSet] with y hy hyt
    rw [hy hyt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section

open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_logPeriods_of_local_markings : ∀ (n a g : ℕ) (_h : a ≤ n) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : LinearMap.BilinForm ℤ Λ) (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Hf : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (U : Set (Fin n → ℂ)) (Γ₀ : Submodule ℤ (Fin g → ℂ)) (S : Γ₀ → (Fin n → ℂ) → (Fin g → ℂ)), U = {z | z ∈ ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0} → Module.finrank ℤ Λ = 2 * g → (∀ x, E x x = 0) → Function.Bijective E → (∀ z ∈ U, (Hf z).IsHermitian ∧ ∀ x : Fin g → ℂ, x ≠ 0 → 0 < (x ⬝ᵥ Hf z *ᵥ star x).re) → (∀ z₀ ∈ U, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ U ∧ ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun z => P z x) N) ∧ ∀ z ∈ N, Function.Injective (P z) ∧ (P z).range = Γ z ∧ ∀ x y, (P z x ⬝ᵥ Hf z *ᵥ star (P z y)).im = E x y) → (∀ x, DifferentiableOn ℂ (S x) (ball 0 1) ∧ S x 0 = x ∧ ∀ z ∈ U, S x z ∈ Γ z) → (∀ x y z, S (x + y) z = S x z + S y z) → (∀ s : (Fin n → ℂ) → (Fin g → ℂ), ContinuousAt s 0 → (∀ z ∈ U, s z ∈ Γ z) → s 0 ∈ Γ₀) → Submodule.span ℂ (Γ₀ : Set (Fin g → ℂ)) = ⊤ → (∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → ∀ z ∈ U, ∃ k : ℤ, (S x z ⬝ᵥ Hf z *ᵥ star (S y z)).im = N * k) → ∃ L : LogPeriods n a g Λ, L.H = Hf := by
  intro n a g h Λ _ _ _ E Γ Hf U Γ₀ S hU hr hE hEb hH hloc hS hadd hlim hspan hcount
  obtain ⟨L, hL, -⟩ := GlobalTheory.T.period_lattice_on_punctured_disc n a g h Λ E Γ Hf U Γ₀ S hU hr hE hEb hH hloc hS hadd hlim
    hspan hcount
  exact ⟨L, hL⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

theorem _root_.GlobalTheory.T.hermitian_line_shift_properties : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι) (t Λ : ℝ), (IsSmoothHerm A → IsSmoothHerm (shiftH A t)) ∧ (IsNefH P A → IsNefH P (shiftH A t)) ∧ (IsGenH P A Λ → IsGenH P (shiftH A t) (Λ * Real.exp (-t))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.shiftH_props | exact GlobalTheory.CompanionTheory.Ar.Small.shiftH_props | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.shiftH_props <;> assumption)
end
