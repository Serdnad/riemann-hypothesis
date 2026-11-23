module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle317
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle083
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle094
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle312
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.TorsionFree
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.Topology.Sheaves.Presheaf
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle004
public import ReciprocityTheory.L2DbarEstimates.LeviForms.PolarBallReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

@[expose] public section

section

open IsLocalRing

namespace GlobalTheory

namespace LocIndEtale

open Polynomial

lemma isIntegrallyClosed_of_forall_monic_root (T : Type) [CommRing T] [IsDomain T]
    (h : ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) :
    IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  rintro x ⟨p, hpm, hp⟩
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have : p = 1 := hpm.natDegree_eq_zero.mp hn
      subst this
      simp at hp
    · obtain ⟨r, hr⟩ := h p hpm (hn ▸ hpos)
      have hroot : IsRoot p r := hr
      have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hroot
      set q := p /ₘ (X - C r) with hq
      have hqm : q.Monic := by
        refine Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r) ?_
        rw [hfac]; exact hpm
      have hqdeg : q.natDegree < n := by
        rw [hq, Polynomial.natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]
        omega
      rw [← hfac, eval₂_mul] at hp
      rcases mul_eq_zero.mp hp with h1 | h1
      · refine ⟨r, ?_⟩
        simp only [eval₂_sub, eval₂_X, eval₂_C] at h1
        exact (sub_eq_zero.mp h1).symm
      · exact ih _ hqdeg q hqm h1 rfl

end LocIndEtale

theorem locIndEtale_isDomain_isIntegrallyClosed :
    ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (q : ℕ), (IsDomain T ∧ ∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → IsUnit (q : T) → 0 < q → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → IsDomain (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) ∧ IsIntegrallyClosed (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) := by
  intro T O _ _ _ _ _ _ _ _ _ n hT _ _ hind
  haveI : IsIntegrallyClosed T := LocIndEtale.isIntegrallyClosed_of_forall_monic_root T hT.2
  obtain ⟨hdom, hic⟩ := indEtale_isDomain_isIntegrallyClosed (Polynomial T) O hind

  have hinj : Function.Injective (algebraMap T O) := by
    obtain ⟨ι, _, _, _, Si, -, -, hloc⟩ := hind
    obtain ⟨A, _, _, _, P, _, ⟨e⟩⟩ := hloc (Classical.arbitrary ι)
    haveI : Module.Flat (Polynomial T) (Localization.AtPrime P) := inferInstance
    have hL : Function.Injective (algebraMap (Polynomial T) (Localization.AtPrime P)) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro f hf
      by_contra hne
      have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
        (M := Localization.AtPrime P) (mem_nonZeroDivisors_of_ne_zero hne)
      have h1 : f • (1 : Localization.AtPrime P) = f • 0 := by
        rw [Algebra.smul_def, hf, zero_mul, smul_zero]
      exact one_ne_zero (hreg h1)
    have hS : Function.Injective (algebraMap (Polynomial T) O) := by
      have : (algebraMap (Polynomial T) O) =
          (Si (Classical.arbitrary ι)).val.toRingHom.comp
            (e.toRingEquiv.toRingHom.comp (algebraMap (Polynomial T) (Localization.AtPrime P))) := by
        ext f
        · simp
        · simp
      rw [this]
      exact Subtype.val_injective.comp (e.injective.comp hL)
    rw [IsScalarTower.algebraMap_eq T (Polynomial T) O]
    exact hS.comp Polynomial.C_injective
  have hle : Algebra.algebraMapSubmonoid O (nonZeroDivisors T) ≤ nonZeroDivisors O := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero ht (hinj ?_)
    rw [h, map_zero]
  exact ⟨IsLocalization.isDomain_localization hle,
    isIntegrallyClosed_of_isLocalization _ _ hle⟩

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory

open IsLocalRing

theorem isLocalHom_algebraMap_of_moduleFinite (R T : Type) [CommRing R] [IsLocalRing R]
    [CommRing T] [IsLocalRing T] [Algebra R T] [Module.Finite R T] :
    IsLocalHom (algebraMap R T) := by
  constructor
  intro a ha
  by_contra hna
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI hmax : (Ideal.comap (algebraMap R T) (maximalIdeal T)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal T)
  have heq := IsLocalRing.eq_maximalIdeal hmax
  have hm : a ∈ Ideal.comap (algebraMap R T) (maximalIdeal T) := by
    rw [heq]; exact (mem_maximalIdeal a).2 hna
  exact (mem_maximalIdeal _).1 hm ha

theorem isSepClosed_residueField_of_moduleFinite (R T : Type) [CommRing R] [IsLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing T] [IsLocalRing T] [Algebra R T]
    [Module.Finite R T] : IsSepClosed (ResidueField T) := by
  haveI := isLocalHom_algebraMap_of_moduleFinite R T
  haveI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  haveI : Algebra.IsIntegral (ResidueField R) (ResidueField T) := inferInstance
  haveI : Algebra.IsAlgebraic (ResidueField R) (ResidueField T) := inferInstance
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField R)

theorem finite_algebra_strictly_henselian_pi : ∀ (R S : Type) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] [CommRing S] [Algebra R S] [Module.Finite R S],
    ∃ (ι : Type) (_ : Finite ι) (T : ι → Type) (_ : ∀ i, CommRing (T i))
      (_ : ∀ i, Algebra R (T i)) (_ : S ≃ₐ[R] Π i, T i) (_ : ∀ i, HenselianLocalRing (T i)),
      ∀ i, IsSepClosed (ResidueField (T i)) ∧ Module.Finite R (T i) := by
  intro R S _ _ _ _ _ _
  obtain ⟨ι, hι, T, hT, hA, e, h⟩ := ((finite_algebras_over_henselian R).1 S).1
  refine ⟨ι, hι, T, hT, hA, e, fun i ↦ (h i).1, fun i ↦ ⟨?_, (h i).2⟩⟩
  haveI := (h i).1
  haveI := (h i).2
  exact isSepClosed_residueField_of_moduleFinite R (T i)

end GlobalTheory
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.bijective_locallyConstant_comap_algClosure_tensor_of_henselian : ∀ (Λ : Type) (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] (B : Type) [CommRing B] [Algebra A B] [Algebra.IsIntegral A B], Function.Bijective (fun φ : LocallyConstant (PrimeSpectrum B) Λ => φ.comap ⟨PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] AlgebraicClosure (IsLocalRing.ResidueField A) ⊗[A] B).toRingHom, PrimeSpectrum.continuous_comap _⟩) := by
  first | exact @GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor | exact GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor | (intros; apply GlobalTheory.bijective_locallyConstant_comap_algebraicClosure_tensor <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

noncomputable section

namespace GlobalTheory.ShellMass

theorem shell_mass : ∀ (n : ℕ), 1 ≤ n → ∀ (p : V n) (O : Set (V n)) (Z : V n → V n) (lam : V n → ℝ), IsOpen O → p ∈ O → DifferentiableOn ℂ Z O → Z p = 0 → (fderiv ℂ Z p).det ≠ 0 → ContinuousOn lam O → ∀ (φ : V n → ℝ) (l τ : ℝ), ContinuousOn φ O → 0 < l → 0 < τ → ∃ ρ : ℝ, 0 < ρ ∧ ball p ρ ⊆ O ∧ ∀ b : ℝ, ∫⁻ v in ball p ρ ∩ {v | Z v ≠ 0 ∧ b - l ≤ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ∧ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ≤ b}, ENNReal.ofReal (Real.exp (-φ v) * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) ≤ ENNReal.ofReal ((1 + τ) * (Real.pi ^ n / ((n - 1).factorial : ℝ) * (l / n)) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2)) := by
  classical
  intro n hn p O Z lam hO hpO hZ hZp hdet hlam φ l τ hφ hl hτ
  have hZc : ContDiffOn ℂ ∞ Z O := by
    refine contDiffOn_piLp' (p := 2) fun i => ?_
    have hd : DifferentiableOn ℂ (fun x => Z x i) O :=
      (EuclideanSpace.proj i : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn hZ
    have ha : AnalyticOnNhd ℂ (fun x => Z x i) O := fun z hz =>
      ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.analyticAt_of_diffOn hO hd hz
    exact ha.contDiffOn hO.uniqueDiffOn
  have hZa : ContDiffAt ℂ ∞ Z p := hZc.contDiffAt (hO.mem_nhds hpO)
  set E0 := (fderiv ℂ Z p).toContinuousLinearEquivOfDetNeZero hdet
  have hs : HasStrictFDerivAt Z (E0 : V n →L[ℂ] V n) p := by
    simpa [E0] using hZa.hasStrictFDerivAt_fderiv (by norm_cast)
  set e := hs.toOpenPartialHomeomorph Z
  have he : (e : V n → V n) = Z := rfl
  have hpe : p ∈ e.source := hs.mem_toOpenPartialHomeomorph_source
  have hdetc : ContinuousOn (fun v => (fderiv ℂ Z v).det) O :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hZc.continuousOn_fderiv_of_isOpen hO (by norm_cast))
  set D : V n → ℝ := fun v => ‖(fderiv ℂ Z v).det‖ ^ 2 with hD
  have hDc : ContinuousAt D p := ((hdetc.continuousAt (hO.mem_nhds hpO)).norm).pow 2
  have hD0 : 0 < D p := pow_pos (norm_pos_iff.2 hdet) 2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set c := l / n with hcdef
  have hc : 0 < c := div_pos hl hnr
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ Real.exp (2 * η) * (c + 2 * η) < (1 + τ) * c := by
    refine Filter.Eventually.and eventually_mem_nhdsWithin (nhdsWithin_le_nhds ?_)
    have ht : Tendsto (fun η : ℝ => Real.exp (2 * η) * (c + 2 * η)) (𝓝 0)
        (𝓝 (Real.exp (2 * 0) * (c + 2 * 0))) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (continuous_const.add (continuous_const.mul continuous_id))).tendsto 0
    simp only [mul_zero, Real.exp_zero, one_mul, add_zero] at ht
    exact ht.eventually (gt_mem_nhds (by nlinarith))
  obtain ⟨η, hη, hηc⟩ := hev.exists
  have hlamc : ContinuousAt lam p := hlam.continuousAt (hO.mem_nhds hpO)
  have hgc : ContinuousAt (fun v => -φ v + (n : ℝ) * lam v) p :=
    ((hφ.continuousAt (hO.mem_nhds hpO)).neg).add (continuousAt_const.mul hlamc)
  have h1 : ∀ᶠ v in 𝓝 p, v ∈ O := hO.mem_nhds hpO
  have h2 : ∀ᶠ v in 𝓝 p, v ∈ e.source := e.open_source.mem_nhds hpe
  have h3 : ∀ᶠ v in 𝓝 p, lam v ∈ ball (lam p) η := hlamc.eventually (ball_mem_nhds _ hη)
  have h4 : ∀ᶠ v in 𝓝 p, (-φ v + (n : ℝ) * lam v) ∈ ball (-φ p + (n : ℝ) * lam p) η :=
    hgc.eventually (ball_mem_nhds _ hη)
  have h5 : ∀ᶠ v in 𝓝 p, D p * Real.exp (-η) < D v := by
    refine hDc.eventually (lt_mem_nhds ?_)
    have : Real.exp (-η) < 1 := (Real.exp_lt_exp.2 (by linarith : -η < 0)).trans_eq Real.exp_zero
    nlinarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and (h3.and (h4.and h5))))
  have hbO : ball p ρ ⊆ O := fun v hv => (hball v hv).1
  have hinj : Set.InjOn Z (ball p ρ) := by
    rw [← he]; exact e.injOn.mono fun v hv => (hball v hv).2.1
  refine ⟨ρ, hρ, hbO, ?_⟩
  intro b
  set a1 := Real.exp ((b - l) / n + lam p - η) with ha1
  set a2 := Real.exp (b / n + lam p + η) with ha2
  have ha1p : 0 < a1 := Real.exp_pos _
  have h21 : a2 / a1 = Real.exp (c + 2 * η) := by
    rw [ha1, ha2, ← Real.exp_sub, hcdef]; congr 1; ring
  have ha12 : a1 ≤ a2 := by
    rw [ha1, ha2]; refine Real.exp_le_exp.2 ?_
    have : (b - l) / n ≤ b / n := div_le_div_of_nonneg_right (by linarith) hnr.le
    linarith
  set Ann := {w : V n | a1 ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ a2} with hAnn
  have hAnnm : MeasurableSet Ann :=
    ((isClosed_le continuous_const (continuous_norm.pow 2)).inter
      (isClosed_le (continuous_norm.pow 2) continuous_const)).measurableSet
  set K := Real.exp (2 * η) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hfm' : Measurable fun w : V n => ENNReal.ofReal ((‖w‖ ^ 2) ^ (-(n : ℝ))) :=
    ((measurable_norm.pow_const 2).pow_const _).ennreal_ofReal
  set f : V n → ℝ≥0∞ := fun w => ENNReal.ofReal K *
      Ann.indicator (fun w => ENNReal.ofReal ((‖w‖ ^ 2) ^ (-(n : ℝ)))) w with hfdef
  have hfm : Measurable f := measurable_const.mul (hfm'.indicator hAnnm)
  set Zb : V n → V n := (ball p ρ).piecewise Z (fun _ => 0) with hZb
  have hZbm : Measurable Zb :=
    ContinuousOn.measurable_piecewise (hZ.continuousOn.mono hbO) continuousOn_const measurableSet_ball
  set G : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (D v) * f (Zb v) with hG
  have hGm : Measurable G := by
    refine Measurable.mul ?_ (hfm.comp hZbm)
    refine Measurable.ennreal_ofReal ?_
    exact ((ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℂ Z)).norm).pow_const 2

  have hpt : ∀ v ∈ ball p ρ ∩ {v | Z v ≠ 0 ∧ b - l ≤ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ∧
      ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ≤ b},
      ENNReal.ofReal (Real.exp (-φ v) * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) ≤ G v := by
    rintro v ⟨hvb, hv0, hvl, hvu⟩
    obtain ⟨-, -, hv3, hv4, hv5⟩ := hball v hvb
    rw [mem_ball, Real.dist_eq, abs_lt] at hv3 hv4
    set s := ‖Z v‖ ^ 2 with hsdef
    have hsp : 0 < s := pow_pos (norm_pos_iff.2 hv0) 2
    have hlog : Real.log (s * Real.exp (-lam v)) = Real.log s - lam v := by
      rw [Real.log_mul hsp.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    rw [hlog] at hvl hvu ⊢
    have hl1 : (b - l) / n ≤ Real.log s - lam v := by rw [div_le_iff₀ hnr]; linarith
    have hl2 : Real.log s - lam v ≤ b / n := by rw [le_div_iff₀ hnr]; linarith
    have hA : Z v ∈ Ann := by
      refine ⟨?_, ?_⟩
      · exact (Real.exp_le_exp.2 (by linarith)).trans_eq (Real.exp_log hsp)
      · exact (Real.exp_log hsp).symm.trans_le (Real.exp_le_exp.2 (by linarith))
    have hZbv : Zb v = Z v := Set.piecewise_eq_of_mem _ _ _ hvb
    simp only [hG, hfdef, hZbv, Set.indicator_of_mem hA]
    rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsn : s ^ (-(n : ℝ)) = Real.exp (-(n : ℝ) * Real.log s) := by
      rw [Real.rpow_def_of_pos hsp]; ring_nf
    have heq : Real.exp (-φ v) * Real.exp (-((n : ℝ) * (Real.log s - lam v))) =
        Real.exp (-φ v + (n : ℝ) * lam v) * s ^ (-(n : ℝ)) := by
      rw [hsn, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [heq]
    have hexp : Real.exp (-φ v + (n : ℝ) * lam v) ≤ D v * K := by
      have e1 : Real.exp (-φ v + (n : ℝ) * lam v) ≤ Real.exp (-φ p + n * lam p + η) :=
        Real.exp_le_exp.2 (by linarith)
      have e2 : Real.exp (-φ p + n * lam p + η) = D p * Real.exp (-η) * K := by
        rw [hK, show ‖(fderiv ℂ Z p).det‖ ^ 2 = D p from rfl, div_eq_mul_inv]
        have hDi : D p * (D p)⁻¹ = 1 := mul_inv_cancel₀ hD0.ne'
        have hx : Real.exp (-φ p + n * lam p + η) =
            Real.exp (-η) * Real.exp (2 * η) * Real.exp (-φ p + n * lam p) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [hx]
        linear_combination (-(Real.exp (-η) * Real.exp (2 * η) * Real.exp (-φ p + n * lam p))) * hDi
      rw [e2] at e1
      exact e1.trans (mul_le_mul_of_nonneg_right hv5.le hK0)
    have hsn0 : 0 ≤ s ^ (-(n : ℝ)) := Real.rpow_nonneg hsp.le _
    calc Real.exp (-φ v + (n : ℝ) * lam v) * s ^ (-(n : ℝ)) ≤ D v * K * s ^ (-(n : ℝ)) :=
          mul_le_mul_of_nonneg_right hexp hsn0
      _ = D v * (K * s ^ (-(n : ℝ))) := by ring
  have hcov := ReciprocityTheory.L2DbarEstimates.I.cov n (ball p ρ) Z f isOpen_ball (hZ.mono hbO) hinj hfm
  have hpol := ReciprocityTheory.L2DbarEstimates.I.polar n hn a1 a2 ha1p ha12
  calc _ ≤ ∫⁻ v in ball p ρ ∩ {v | Z v ≠ 0 ∧ b - l ≤ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ∧
        ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ≤ b}, G v := setLIntegral_mono hGm hpt
    _ ≤ ∫⁻ v in ball p ρ, G v := lintegral_mono_set Set.inter_subset_left
    _ = ∫⁻ w in Z '' ball p ρ, f w := by
        rw [hcov]
        refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
        simp only [hG, hD, Set.piecewise_eq_of_mem _ _ _ hv, hZb]
    _ ≤ ∫⁻ w, f w := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal K * ENNReal.ofReal (Real.pi ^ n / ((n - 1).factorial : ℝ) * Real.log (a2 / a1)) := by
        rw [hfdef, lintegral_const_mul _ (hfm'.indicator hAnnm), lintegral_indicator hAnnm, hpol]
    _ ≤ _ := by
        rw [← ENNReal.ofReal_mul hK0]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [h21, Real.log_exp, hK]
        have hP : 0 ≤ Real.pi ^ n / ((n - 1).factorial : ℝ) := by positivity
        have hE : 0 ≤ Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2 := by positivity
        calc Real.exp (2 * η) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2) *
              (Real.pi ^ n / ((n - 1).factorial : ℝ) * (c + 2 * η))
            = (Real.pi ^ n / ((n - 1).factorial : ℝ) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2)) *
              (Real.exp (2 * η) * (c + 2 * η)) := by ring
          _ ≤ (Real.pi ^ n / ((n - 1).factorial : ℝ) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2)) *
              ((1 + τ) * c) := mul_le_mul_of_nonneg_left hηc.le (mul_nonneg hP hE)
          _ = _ := by rw [hcdef]; ring

end GlobalTheory.ShellMass
end
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.WedgeDen

theorem alternatingMap_sum_smul_eq_det_smul' {L M N : Type} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] {n : ℕ} (f : M [⋀^Fin n]→ₗ[L] N) (g : Fin n → M)
    (a : Fin n → Fin n → L) :
    f (fun i => ∑ l, a i l • g l) = (Matrix.of a).det • f g := by
  first
  | exact @_root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination
  | exact _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination
  | (apply _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination ..)

theorem exists_smul_ιMulti_eq_smul_ιMulti : ∀ (R L M : Type) [CommRing R] [Field L] [Algebra R L] [AddCommGroup M] [Module L M] (S : Submonoid R) (n : ℕ) (g w : Fin n → M), (∀ i, ∃ r ∈ S, ∃ c : Fin n → R, algebraMap R L r • w i = ∑ l, algebraMap R L (c l) • g l) → ∃ r ∈ S, ∃ c : R, algebraMap R L r • ExteriorAlgebra.ιMulti L n w = algebraMap R L c • ExteriorAlgebra.ιMulti L n g := by
  intro R L M _ _ _ _ _ S n g w h
  classical
  choose r hr c hc using h
  refine ⟨∏ i, r i, prod_mem fun i _ => hr i, (Matrix.of c).det, ?_⟩
  rw [map_prod, ← AlternatingMap.map_smul_univ]
  simp_rw [hc]
  rw [alternatingMap_sum_smul_eq_det_smul', RingHom.map_det]
  rfl

end GlobalTheory.WedgeDen
end

section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

set_option autoImplicit false

theorem GlobalTheory.wedge_D_eq_pow_mul_wedge_D_of_eq_unit_mul_pow : ∀ (k K : Type) [Field k] [CharZero k] [Field K] [Algebra k K] (B : Subalgebra k K) (Q : Ideal B), Q.IsPrime → ∀ (s : B) (m : ℕ) (y : Fin m → K) (T : K) (e : ℕ), 1 ≤ e → s ∈ Q → (∀ v : B, ∃ r : B, r ∉ Q ∧ ∃ c : Fin (m + 1) → B, (r : K) • D k K (v : K) = ∑ l, (c l : K) • (Fin.cons (D k K (s : K)) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) l) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * T = a * s ^ e) → ∃ N Dn : B, N ∉ Q ∧ Dn ∉ Q ∧ (Dn : K) • ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K T) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) = ((N : K) * (s : K) ^ (e - 1)) • ExteriorAlgebra.ιMulti K (m + 1) (Fin.cons (D k K (s : K)) (fun j => D k K (y j)) : Fin (m + 1) → Ω[K⁄k]) := by
  intro k K _ _ _ _ B Q hQ s m y T e he hs hgen ⟨a, r, ha, hr, hT⟩
  classical
  let g : Fin m → Ω[K⁄k] := fun j => D k K (y j)
  let f : Ω[K⁄k] →ₗ[K] ExteriorAlgebra K Ω[K⁄k] :=
    (ExteriorAlgebra.ιMulti K (m+1)).toMultilinearMap.toLinearMap (Fin.cons 0 g) 0
  have hf : ∀ v, f v = ExteriorAlgebra.ιMulti K (m+1) (Fin.cons v g : Fin (m+1) → Ω[K⁄k]) := by
    intro v; simp only [f, MultilinearMap.toLinearMap_apply, Fin.update_cons_zero]; rfl
  have hg0 : ∀ j, f (g j) = 0 := by
    intro j; rw [hf]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := j.succ) (by simp) (Fin.succ_ne_zero j).symm
  have key : ∀ v : B, ∃ ρ : B, ρ ∉ Q ∧ ∃ c0 : B, (ρ : K) • f (D k K (v:K)) = (c0 : K) • f (D k K (s:K)) := by
    intro v
    obtain ⟨ρ, hρ, c, hc⟩ := hgen v
    refine ⟨ρ, hρ, c 0, ?_⟩
    have h2 := congrArg f hc

    rw [map_smul, map_sum, Fin.sum_univ_succ] at h2
    simpa [hg0, g] using h2
  obtain ⟨ρa, hρa, ca, hA⟩ := key a
  obtain ⟨ρr, hρr, cr, hR⟩ := key r
  have hse : (s:K)^e = (s:K) * (s:K)^(e-1) := by
    rw [← pow_succ']; congr 1; omega
  have hX : (r:K) • f (D k K T) + T • f (D k K (r:K)) = ((a:K) * (e:K) * (s:K)^(e-1)) • f (D k K (s:K)) + ((s:K) * (s:K)^(e-1)) • f (D k K (a:K)) := by
    have h1 := congrArg (fun z => f (D k K z)) hT
    simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add (f := _), map_smul, map_nsmul] at h1
    rw [← hse, mul_smul, mul_smul, Nat.cast_smul_eq_nsmul K]; exact h1
  have heB : (e : B) ∉ Q := by
    intro h
    have hu : IsUnit (e : B) := by
      have h3 : (e : B) = algebraMap k B (e : k) := by simp
      rw [h3]
      exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))).map _
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  refine ⟨ρa*ρr*(e:B)*a*r + s*(ρr*r*ca - ρa*a*cr), ρa*ρr*r^2, ?_, ?_, ?_⟩
  · intro h
    have h4 : ρa*ρr*(e:B)*a*r ∈ Q := by
      have := Q.sub_mem h (Q.mul_mem_right (ρr*r*ca - ρa*a*cr) hs)
      simpa using this
    rcases hQ.mem_or_mem h4 with h4 | h4
    · rcases hQ.mem_or_mem h4 with h4 | h4
      · rcases hQ.mem_or_mem h4 with h4 | h4
        · rcases hQ.mem_or_mem h4 with h4 | h4
          · exact hρa h4
          · exact hρr h4
        · exact heB h4
      · exact ha h4
    · exact hr h4
  · intro h
    rcases hQ.mem_or_mem h with h | h
    · rcases hQ.mem_or_mem h with h | h
      · exact hρa h
      · exact hρr h
    · exact hr (hQ.mem_of_pow_mem _ h)
  · have hT' : (r:K) * T = (a:K) * ((s:K) * (s:K)^(e-1)) := by rw [hT, hse]
    rw [← hf, ← hf]
    push_cast
    linear_combination (norm := module) ((ρa:K)*ρr*r) • hX + ((ρr:K)*r*s*(s:K)^(e-1)) • hA - ((ρa:K)*r*T) • hR - ((ρa:K)*cr) • hT' • f (D k K (s:K))
end

section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  first | exact @GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair | exact GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair | (intros; apply GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair <;> assumption)
end
