module

public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameBorelGroupoidProperties
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle033
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AllWeightSectionsCompat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle132
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ComponentDataHeightIdentity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle296
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle155
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall

@[expose] public section

section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

namespace GlobalTheory.CompanionTheory.Ar.SameFlag

theorem eq_of_ratios {K A L M : Type} [Field K] [CommRing A] [Algebra K A] [Field L] [Algebra K L] [CommRing M]
    [IsDomain M] [Algebra K M] (ι : A →ₐ[K] L) (hι : Function.Injective ι) (ψ : A →ₐ[K] M) (φ : L →ₐ[K] M) {N : ℕ}
    (G : Fin (N + 1) → A) (h0 : ι (G 0) ≠ 0) (hψ0 : ψ (G 0) ≠ 0)
    (hrat : ∀ j, ψ (G j) * φ (ι (G 0)) = ψ (G 0) * φ (ι (G j)))
    (hgen : IntermediateField.adjoin K (Set.range fun j => ι (G j) / ι (G 0)) = ⊤) (b : A) : ψ b = φ (ι b) := by
  set g₀ : A := G 0 with hg₀
  let S : Subalgebra K L :=
    { carrier := {x | ∃ (a : A) (n : ℕ), x * ι g₀ ^ n = ι a ∧ φ x * ψ g₀ ^ n = ψ a}
      mul_mem' := by
        rintro x x' ⟨a, n, h1, h2⟩ ⟨a', n', h1', h2'⟩
        refine ⟨a * a', n + n', ?_, ?_⟩
        · rw [map_mul, ← h1, ← h1', pow_add]; ring
        · rw [map_mul, map_mul, ← h2, ← h2', pow_add]; ring
      add_mem' := by
        rintro x x' ⟨a, n, h1, h2⟩ ⟨a', n', h1', h2'⟩
        refine ⟨a * g₀ ^ n' + a' * g₀ ^ n, n + n', ?_, ?_⟩
        · rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← h1, ← h1', pow_add]; ring
        · rw [map_add (f := _), map_add (f := _), map_mul, map_mul, map_pow, map_pow, ← h2, ← h2', pow_add]; ring
      algebraMap_mem' := fun r => ⟨algebraMap K A r, 0, by simp, by simp⟩ }
  have hmem : ∀ x, x ∈ S ↔ ∃ (a : A) (n : ℕ), x * ι g₀ ^ n = ι a ∧ φ x * ψ g₀ ^ n = ψ a := fun x => Iff.rfl
  have hφ0 : φ (ι g₀) ≠ 0 := (map_ne_zero φ).2 h0
  have hρ : ∀ j, ι (G j) / ι g₀ ∈ S := by
    intro j
    refine (hmem _).2 ⟨G j, 1, by rw [pow_one, div_mul_cancel₀ _ h0], ?_⟩
    have e1 : φ (ι (G j) / ι g₀) * φ (ι g₀) = φ (ι (G j)) := by
      rw [← map_mul, div_mul_cancel₀ _ h0]
    refine mul_right_cancel₀ hφ0 ?_
    rw [pow_one, hrat j, ← e1]; ring
  have hpol : ∀ p : MvPolynomial (Fin (N + 1)) K, MvPolynomial.aeval (fun j => ι (G j) / ι g₀) p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simpa using S.algebraMap_mem a
    | add p q hp hq => simpa using S.add_mem hp hq
    | mul_X p i hp => simpa using S.mul_mem hp (hρ i)
  have hb : ι b ∈ IntermediateField.adjoin K (Set.range fun j => ι (G j) / ι g₀) := by
    rw [hgen]; exact IntermediateField.mem_top
  obtain ⟨p, q, e⟩ := (IntermediateField.mem_adjoin_range_iff K _ _).1 hb
  by_cases hq : MvPolynomial.aeval (fun j => ι (G j) / ι g₀) q = 0
  · rw [hq, div_zero] at e
    have : b = 0 := hι (by rw [e, map_zero])
    rw [this, map_zero, map_zero, map_zero]
  obtain ⟨a₁, n₁, h1, h1'⟩ := (hmem _).1 (hpol q)
  obtain ⟨a₂, n₂, h2, h2'⟩ := (hmem _).1 (hpol p)
  set B := MvPolynomial.aeval (fun j => ι (G j) / ι g₀) q with hB
  set P := MvPolynomial.aeval (fun j => ι (G j) / ι g₀) p with hP
  have hbB : ι b * B = P := by rw [e, div_mul_cancel₀ _ hq]
  have key : b * a₁ * g₀ ^ n₂ = a₂ * g₀ ^ n₁ := by
    apply hι
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, ← h1, ← h2, ← hbB]; ring
  have key' := congrArg ψ key
  rw [map_mul, map_mul, map_mul, map_pow, map_pow, ← h1', ← h2', ← hbB, map_mul] at key'
  have hne : φ B * ψ g₀ ^ n₁ * ψ g₀ ^ n₂ ≠ 0 :=
    mul_ne_zero (mul_ne_zero ((map_ne_zero φ).2 hq) (pow_ne_zero _ hψ0)) (pow_ne_zero _ hψ0)
  refine mul_right_cancel₀ hne ?_
  linear_combination key'

end GlobalTheory.CompanionTheory.Ar.SameFlag

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SameFlag

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_map (hL : GlobalTheory.Reg.EvLaws Xo c) {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S T : Type} [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hyz : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  have key : ∀ {S' : Type} [CommRing S'] [Algebra c.F S'] (p : TRing c.F) (χ : p.R →ₐ[c.F] S') (y₀ : FrPt Xo c p.R)
      (w : FrPt Xo c S'), FrMap χ y₀ w → evR Xo c f w = χ (f p y₀) := by
    intro S' _ _ p χ y₀ w hw
    have h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w := ⟨p, χ, y₀, hw⟩
    unfold evR evalAt
    rw [dite_eq_left h]
    exact hL.wd f hf S' _ p _ χ _ y₀ w h.choose_spec.choose_spec.choose_spec hw
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test S y
  rw [key q χ y₀ y hy₀, key q (φ.comp χ) y₀ z (PullbackSections.frMap_trans χ φ hy₀ hyz)]
  rfl

end Main

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem frBor_of_proportional_readings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c) (k : (U σ).Comp), Over (U σ) (e Z) k → ∀ (a : WZ E) (N : ℕ) (g : Fin (N + 1) → Rul Xo c), (∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) → BirOn h Z g → ∀ (φ : Om Z →ₐ[c.F] CAt σ) (x₀ y : ((U σ).X k).dom) (y₁ : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y₁ → FrBor t ((U σ).un k x₀) y₁ → ∀ w : ℂ, w ≠ 0 → (∀ j, rdU (U σ) (g j) k y.1 = w * toC (φ (evC h Z (g j)))) → ∃ t' : Ix Dw → (CAt σ)ˣ, FrBor t' ((U σ).un k x₀) ((U σ).un k y) := by
  intro E _ _ _ H Dw l Xo c r U h e hC σ hσ Z k hOver a N g hg hB φ x₀ y y₁ t hφ hb w hw hr
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have hS : Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  haveI hdom : IsDomain (CAt σ) := inferInstanceAs (IsDomain ℂ)
  haveI hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have hrd : ∀ f : Rul Xo c, rdU (U σ) f k y.1 = toC (evR Xo c f ((U σ).un k y)) := by
    intro f
    classical
    show (if h : y.1 ∈ ((U σ).X k).dom then toC (evR Xo c f ((U σ).un k ⟨y.1, h⟩)) else 0) = _
    rw [dite_eq_left y.2]
  obtain ⟨C, ψ, z, t', hz, hbz⟩ : ∃ (C : GlobalTheory.Reg.FChart h) (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ))
      (t' : Ix Dw → (CAt σ)ˣ), FrMap ψ C.y z ∧ FrBor t' z ((U σ).un k y) := by
    letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
    exact hA h (CAt σ) ((U σ).un k y)

  have hCZ : C.Z = Z := by
    by_contra hne
    have he := hC.e_sec Z
    have h0 : evC h C.Z (e Z) = 0 := (hC.e_val Z).2 _ hne
    have h1 : evR Xo c (e Z) C.yg = 0 := by
      rw [hL.wt 0 0 (e Z) he _ C.t _ _ (hL.test _ _) (hL.test _ _) C.bor]
      unfold evC at h0
      rw [h0, mul_zero]
    have h2 : evR Xo c (e Z) C.y = 0 := by
      rw [evR_map hL he.1 C.R.val C.gen] at h1
      exact Subtype.ext h1
    have h3 : evR Xo c (e Z) z = 0 := by rw [evR_map hL he.1 ψ hz, h2, map_zero]
    have h4 : evR Xo c (e Z) ((U σ).un k y) = 0 := by
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      rw [hL.wt 0 0 (e Z) he _ t' _ _ (hL.test _ _) (hL.test _ _) hbz, h3, mul_zero]
    have h5 := hOver y.1 y.2
    rw [hrd, h4] at h5
    exact zero_ne_one (α := ℂ) h5
  subst hCZ
  have hgA : ∀ j, g j ∈ GlobalTheory.AllWt.secZ Xo c (exZ Dw a) := fun j => by
    rw [← secZ_eq_allWt]; exact hg j
  set ex := exZ Dw a with hex

  let G : Fin (N + 1) → C.R := fun j => evR Xo c (g j) C.y
  have hιG : ∀ j, C.R.val (G j) = ((∏ i, C.t i ^ ex i : (Om C.Z)ˣ) : Om C.Z) * evC h C.Z (g j) := by
    intro j
    rw [← evR_map hL (hg j).1 C.R.val C.gen]
    exact GlobalTheory.evR_frBor_of_mem_secZ hS Xo c ex (hgA j) (Om C.Z) C.t _ _ C.bor
  obtain ⟨wc, hwc⟩ : ∃ wc : CAt σ, toC wc = w := ⟨w, rfl⟩
  have hψG : ∀ j, ((∏ i, t' i ^ ex i : (CAt σ)ˣ) : CAt σ) * ψ (G j) = wc * φ (evC h C.Z (g j)) := by
    intro j
    have h1 : evR Xo c (g j) ((U σ).un k y) = ((∏ i, t' i ^ ex i : (CAt σ)ˣ) : CAt σ) * evR Xo c (g j) z :=
      GlobalTheory.evR_frBor_of_mem_secZ hS Xo c ex (hgA j) (CAt σ) t' _ _ hbz
    have h2 : evR Xo c (g j) z = ψ (G j) := evR_map hL (hg j).1 ψ hz
    rw [← h2, ← h1]
    have h3 := hr j
    rw [hrd, ← hwc] at h3
    exact h3
  set T : (Om C.Z)ˣ := ∏ i, C.t i ^ ex i with hT
  set T' : (CAt σ)ˣ := ∏ i, t' i ^ ex i with hT'
  have hw' : wc ≠ 0 := fun h0 => hw (by rw [← hwc, h0]; rfl)
  have hE0 : φ (evC h C.Z (g 0)) ≠ 0 := (map_ne_zero_iff φ φ.toRingHom.injective).2 hB.1
  have hψ0 : ψ (G 0) ≠ 0 := by
    intro h0
    have h1 := hψG 0
    rw [h0, mul_zero] at h1
    exact mul_ne_zero hw' hE0 h1.symm
  have hι0 : C.R.val (G 0) ≠ 0 := by
    rw [hιG]
    exact mul_ne_zero T.ne_zero hB.1
  have hrat : ∀ j, ψ (G j) * φ (C.R.val (G 0)) = ψ (G 0) * φ (C.R.val (G j)) := by
    intro j
    have h1 := hψG j
    have h2 := hψG 0
    refine mul_left_cancel₀ T'.ne_zero ?_
    rw [hιG, hιG, map_mul, map_mul]
    linear_combination (φ (T : Om C.Z) * φ (evC h C.Z (g 0))) * h1 - (φ (T : Om C.Z) * φ (evC h C.Z (g j))) * h2
  have hgen : IntermediateField.adjoin c.F (Set.range fun j => C.R.val (G j) / C.R.val (G 0)) = ⊤ := by
    have e1 : (fun j => C.R.val (G j) / C.R.val (G 0)) = fun j => evC h C.Z (g j) / evC h C.Z (g 0) := by
      funext j
      rw [hιG, hιG, mul_div_mul_left _ _ T.ne_zero]
    rw [e1]
    exact hB.2
  have hψφ : ψ = φ.comp C.R.val :=
    AlgHom.ext fun b => eq_of_ratios C.R.val Subtype.val_injective ψ φ G hι0 hψ0 hrat hgen b

  obtain ⟨w₁, hw₁⟩ := hL.bc _ _ φ C.yg
  have h1 := PullbackSections.frMap_trans _ _ C.gen hw₁
  rw [← hψφ] at h1
  obtain rfl : z = w₁ := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ _ C.y).1 _ _ hz h1
  have hbc := GlobalTheory.SupGeneric.frBor_of_frMap φ C.bor hφ hw₁
  have hgp := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)
  exact ⟨_, hgp.2.1 _ _ _ _ _ (hgp.2.1 _ _ _ _ _ hb hbc) hbz⟩

end GlobalTheory.CompanionTheory.Ar.SameFlag
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.JoinPts

open MvPolynomial AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_zero_of_mem (y : (Σ k, ι k) → Ω) {g : MRing ι} (h : g ∈ mCoordIdeal y) : aeval y g = 0 := by
  have h0 : mConeMap y g = 0 := (RingHom.mem_ker).1 h
  have e : ((aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ).comp (mConeMap y) =
      aeval y := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap]
  rw [← e, AlgHom.comp_apply, h0, map_zero]

theorem aeval_map_hom {Ω' : Type} [Field Ω'] (i : Ω →+* Ω') (y : (Σ k, ι k) → Ω) (g : MRing ι) :
    aeval (fun p => i (y p)) g = i (aeval y g) := by
  have e : (aeval (fun p => i (y p)) : MRing ι →ₐ[ℤ] Ω') = (i.toIntAlgHom).comp (aeval y) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp
  rw [e]
  rfl

theorem cross_mem (y : (Σ k, ι k) → Ω) (p q p' q' : Σ k, ι k) (hp : p'.1 = p.1) (hq : q'.1 = q.1)
    (h : y p * y q' = y p' * y q) :
    (X p * X q' - X p' * X q : MRing ι) ∈ mCoordIdeal y := by
  refine (RingHom.mem_ker).2 ?_
  have e : (C (y p) * C (y q') : MvPolynomial K Ω) = C (y p') * C (y q) := by
    rw [← C_mul, ← C_mul, h]
  have hx : mConeMap y (X p * X q' - X p' * X q : MRing ι) =
      C (y p) * X p.1 * (C (y q') * X q'.1) - C (y p') * X p'.1 * (C (y q) * X q.1) := by
    simp [mConeMap]
  rw [hx, hp, hq]
  linear_combination (X p.1 * X q.1) * e

theorem exists_smul_of_cross {κ : Type} {u v : κ → ℂ} (hv : v ≠ 0) (h : ∀ a b, u a * v b = u b * v a) :
    ∃ t : ℂ, u = t • v := by
  obtain ⟨b, hb⟩ := Function.ne_iff.1 hv
  have hb' : v b ≠ 0 := hb
  refine ⟨u b / v b, funext fun a => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  exact h a b

end Forms

theorem coordsAt_smul {X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X'} {K : Type}
    {ι : K → Type} {y : (Σ k, ι k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X'} {w : (Σ k, ι k) → ℂ}
    (h : CoordsAt ξ y z w) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : CoordsAt ξ y z (fun p => c p.1 * w p) := by
  refine ⟨fun k => ?_, fun k a ha => ?_⟩
  · obtain ⟨a, ha⟩ := h.1 k
    exact ⟨a, (isUnit_iff_ne_zero.2 (hc k)).mul ha⟩
  · have ha' : IsUnit (w ⟨k, a⟩) := isUnit_iff_ne_zero.2 (right_ne_zero_of_mul ha.ne_zero)
    obtain ⟨hy, hr⟩ := h.2 k a ha'
    refine ⟨hy, fun i => ?_⟩
    obtain ⟨r, h1, h2⟩ := hr i
    refine ⟨r, h1, ?_⟩
    show c k * w ⟨k, i⟩ = r * (c k * w ⟨k, a⟩)
    rw [h2]
    ring

section Origin

attribute [-instance] GlobalTheory.CompHt.fintypePsi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {M : Top.RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}

theorem mono_coeff (c : Coeff l) : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { }
  have := IsPreimmersion.of_isLocalization (S := c.F) (nonZeroDivisors (𝓞 c.F))
  exact inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 c.F) c.F))))

theorem exists_form (o : RootOrigin Y S M Fx) :
    ∃ b : MRing M.ι, aeval M.y b ≠ 0 ∧ ∀ w ∈ mcPts M.P, aeval w b ≠ 0 →
      ∃ z : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X, CoordsAt o.𝔐.ξ M.y z w ∧ o.𝔐.Interior z := by
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨-, ⟨x, hx⟩, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c (𝓞 c.F) _ Y S M.Ω M.K M.ι M.y o.𝔐 hinj
  obtain ⟨b, d, hd, hb, hw⟩ := GlobalTheory.T.hodge_cpt_multihomog_form E H D l Xo c (𝓞 c.F) _ Y S M.Ω M.K M.ι M.y o.𝔐 x hx (mono_coeff c)
  refine ⟨b, fun h => hb (Small.LineModel.mem_of_aeval M.y hd h), fun w hw' hne => hw w hw' ?_⟩
  rw [Cmp.evC, Small.LineModel.eval_map_eq]
  exact hne

theorem exists_lift (o : RootOrigin Y S M Fx) (hJ : o.Re.J = ⊤) {w : (Σ k, M.ι k) → ℂ} (hw : w ∈ mcPts M.P)
    {z : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X} (hz : CoordsAt o.𝔐.ξ M.y z w) (hI : o.𝔐.Interior z) :
    ∃ x : o.Re.R.X, ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) w ∧ o.Re.π x ∈ Sys.open' ∧
      ∃ t : ℂ, Fx.pt (o.Re.π x) = t • fun a => w ⟨o.k₀, o.ix a⟩ := by
  have hnot : w ∉ mcPts o.Re.J := by
    rw [hJ]
    intro h
    have := h.2 1 Submodule.mem_top
    simp at this
  obtain ⟨x, hx⟩ := o.Re.R.surj w hw hnot
  obtain ⟨k, hk, hxw⟩ := id hx
  refine ⟨x, hx, ?_, ?_⟩
  · have hC : CoordsAt o.𝔐.ξ M.y z (o.Re.R.lift x x) := by
      rw [hxw]
      exact coordsAt_smul hz hk
    exact (o.interior x z hC).1 hI
  · obtain ⟨α, hα, h⟩ := TowerOriginModel.pi_pt_ne o x
    refine ⟨α⁻¹ * k o.k₀, funext fun a => ?_⟩
    have h1 := congrFun h a
    rw [hxw] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1 ⊢
    rw [mul_assoc, h1, inv_mul_cancel_left₀ hα]

end Origin

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem join_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω), i.comp o₀.g = o.g → o.Re.J = ⊤ → o₀.Re.J = ⊤ → ∃ f : MRing (Cmp.joinIdx M.ι R.ι), f ∉ mCoordIdeal (Ht.joinOf M R i) ∧ ∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), Cmp.evC w f ≠ 0 → ∃ (x : o.Re.R.X) (x' : o₀.Re.R.X) (z₁ : Spec (CommRingCat.of ℂ) ⟶ o.𝔐.X) (z₂ : Spec (CommRingCat.of ℂ) ⟶ o₀.𝔐.X), ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) (fun p => w (Cmp.joinInl M.ι R.ι p)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o₀.Re.R.lift x' x') (fun p => w (Cmp.joinInr M.ι R.ι p)) ∧ o.Re.π x = o₀.Re.π x' ∧ o.Re.π x ∈ Sys.open' ∧ CoordsAt o.𝔐.ξ M.y z₁ (fun p => w (Cmp.joinInl M.ι R.ι p)) ∧ CoordsAt o₀.𝔐.ξ R.y z₂ (fun p => w (Cmp.joinInr M.ι R.ι p)) ∧ o.𝔐.Interior z₁ ∧ o₀.𝔐.Interior z₂ := by
  intro E _ _ _ H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi hJ hJ₀
  classical
  obtain ⟨b, hb, hbw⟩ := exists_form o
  obtain ⟨b₀, hb₀, hbw₀⟩ := exists_form o₀
  have eL : (Ht.joinOf M R i) ∘ Cmp.joinInl M.ι R.ι = M.y := rfl
  have eR : (Ht.joinOf M R i) ∘ Cmp.joinInr M.ι R.ι = fun p => i (R.y p) := rfl
  refine ⟨rename (Cmp.joinInl M.ι R.ι) b * rename (Cmp.joinInr M.ι R.ι) b₀, fun h => ?_, fun w hw hf => ?_⟩
  · have h0 := aeval_eq_zero_of_mem _ h
    rw [map_mul, aeval_rename, aeval_rename, eL, eR, aeval_map_hom] at h0
    exact (mul_ne_zero hb ((map_ne_zero i).2 hb₀)) h0
  · obtain ⟨hw₁, hw₂⟩ := (GlobalTheory.T.join_model_points_project (CMType H) (D.p + D.q) M R i).2.2.1 ℂ w hw
    rw [Small.LineModel.ptsOver_complex] at hw₁ hw₂
    rw [Cmp.evC, Small.LineModel.eval_map_eq, map_mul, aeval_rename, aeval_rename] at hf
    obtain ⟨z₁, hz₁, hI₁⟩ := hbw _ hw₁ (left_ne_zero_of_mul hf)
    obtain ⟨z₂, hz₂, hI₂⟩ := hbw₀ _ hw₂ (right_ne_zero_of_mul hf)
    obtain ⟨x, hx, hxo, t, ht⟩ := exists_lift o hJ hw₁ hz₁ hI₁
    obtain ⟨x', hx', -, t', ht'⟩ := exists_lift o₀ hJ₀ hw₂ hz₂ hI₂
    refine ⟨x, x', z₁, z₂, hx, hx', ?_, hxo, hz₁, hz₂, hI₁, hI₂⟩
    have hcross : ∀ a b', w (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩) * w (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b'⟩) =
        w (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b'⟩) * w (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) := by
      intro a b'
      have hm := cross_mem (Ht.joinOf M R i) (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix a⟩)
        (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix a⟩) (Cmp.joinInl M.ι R.ι ⟨o.k₀, o.ix b'⟩)
        (Cmp.joinInr M.ι R.ι ⟨o₀.k₀, o₀.ix b'⟩) rfl rfl (by
          show M.y _ * i (R.y _) = M.y _ * i (R.y _)
          have hg : ∀ u, i (o₀.g u) = o.g u := fun u => congrArg (fun φ : Fx.Ωf →+* M.Ω => φ u) hi
          rw [o.y_eq, o.y_eq, o₀.y_eq, o₀.y_eq, hg, hg]
          ring)
      have h0 := hw.2 _ hm
      simp only [map_sub, map_mul, aeval_X] at h0
      exact sub_eq_zero.1 h0
    obtain ⟨s, hs⟩ := exists_smul_of_cross (u := Fx.pt (o.Re.π x)) (v := Fx.pt (o₀.Re.π x')) (Fx.pt_ne _)
      (fun a b' => by
        rw [ht, ht']
        simp only [Pi.smul_apply, smul_eq_mul]
        linear_combination (t * t') * hcross a b')
    exact Fx.pt_inj _ _ s hs

end GlobalTheory.CompanionTheory.Ar.JoinPts
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.CompanionTheory.Relay.compact_datum_intersection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ), (∀ p ∈ S₀ ∪ Dc.SB B, p.Prime) ∧ (∀ p ∈ S₀ ∪ Dc.SB B, 4 ≤ Or.𝔐.R p) ∧ (∀ p ∈ S₀ ∪ Dc.SB B, FullTorsion Or.𝔐.t.G Or.𝔐.ξ (p ^ Or.𝔐.R p)) ∧ ∀ s, (Or.𝔐.VS (S₀ ∪ Dc.SB B) s).IsVB (labelRk D s) (Or.𝔐.Vgen s) := by
  first | exact @LevelTowerAlt.component_data_height_identity | exact LevelTowerAlt.component_data_height_identity
end

section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
theorem _root_.GlobalTheory.T.abelianScheme_spreads_out_finiteType_subring : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (F : Finset R), IsAbelianScheme A → ∃ (S : Subring R) (B : Over (Sp S)) (_ : GrpObj B) (φ : A.left ⟶ B.left), (F : Set R) ⊆ S ∧ Algebra.FiniteType ℤ S ∧ IsAbelianScheme B ∧ IsGrpPullback A B (spMap S.subtype) φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.abelianScheme_descends_to_fg_subring | exact GlobalTheory.CompanionTheory.Ar.Approx.abelianScheme_descends_to_fg_subring | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.abelianScheme_descends_to_fg_subring <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.compact_datum_intersection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ), (∀ p ∈ S₀ ∪ Dc.SB B, p.Prime) ∧ (∀ p ∈ S₀ ∪ Dc.SB B, 4 ≤ Or.𝔐.R p) ∧ (∀ p ∈ S₀ ∪ Dc.SB B, FullTorsion Or.𝔐.t.G Or.𝔐.ξ (p ^ Or.𝔐.R p)) ∧ ∀ s, (Or.𝔐.VS (S₀ ∪ Dc.SB B) s).IsVB (labelRk D s) (Or.𝔐.Vgen s) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.compact_datum_intersection | exact GlobalTheory.CompanionTheory.Relay.compact_datum_intersection | (intros; apply GlobalTheory.CompanionTheory.Relay.compact_datum_intersection <;> assumption)

end
end
