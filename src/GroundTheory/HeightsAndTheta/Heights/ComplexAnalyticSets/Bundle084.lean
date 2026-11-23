module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle063
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle066
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle044
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle069
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle070
public import Mathlib.Analysis.Analytic.Order
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def UniformiserGradientIndependent.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) →
      ∃ (k : ℕ) (f : Fin k → MvPolynomial σ ℂ), k + 1 = Fintype.card σ ∧ (∀ j, f j ∈ I) ∧
        LinearIndependent ℂ (Fin.cons (fun i ↦ eval w (pderiv i t)) (fun j i ↦ eval w (pderiv i (f j))) :
          Fin (k + 1) → σ → ℂ)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

def UniformiserLocallyInjective.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) →
      ∃ U ∈ 𝓝 w, Set.InjOn (fun z : σ → ℂ ↦ eval z t) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I ∩ U)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology
open scoped NNReal ENNReal

theorem VarBranch.dimH_image_le_two {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (c : VarBranch I 1 q) : dimH c.image ≤ 2 := by
  let ι : ℂ → (Fin 1 → ℂ) := fun τ _ ↦ τ
  have hι : ∀ τ : ℂ, ‖ι τ‖ = ‖τ‖ := fun τ ↦ by simp [ι, pi_norm_const]
  have himg : c.image = (c.toFun ∘ ι) '' Metric.ball 0 c.radius := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t 0, ?_, ?_⟩
      · have h0 : ‖t 0‖ ≤ ‖t‖ := norm_le_pi_norm t 0
        rw [Metric.mem_ball, dist_zero_right] at ht ⊢
        linarith
      · simp only [Function.comp, ι]
        congr 1
        funext i
        rw [Subsingleton.elim i 0]
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨ι τ, ?_, rfl⟩
      rw [Metric.mem_ball, dist_zero_right] at hτ ⊢
      rwa [hι]
  have hd : DifferentiableOn ℂ (c.toFun ∘ ι) (Metric.ball 0 c.radius) := by
    have hιd : Differentiable ℂ ι := differentiable_pi.2 fun _ ↦ differentiable_id
    refine c.differentiableOn.comp hιd.differentiableOn fun τ hτ ↦ ?_
    rw [Metric.mem_ball, dist_zero_right] at hτ ⊢
    rwa [hι]
  have hcd : ContDiffOn ℝ 1 (c.toFun ∘ ι) (Metric.ball 0 c.radius) :=
    (hd.contDiffOn Metric.isOpen_ball).restrict_scalars ℝ
  rw [himg]
  calc dimH ((c.toFun ∘ ι) '' Metric.ball 0 c.radius) ≤ dimH (Metric.ball (0 : ℂ) c.radius) :=
        hcd.dimH_image_le (convex_ball 0 c.radius) le_rfl
    _ ≤ dimH (Set.univ : Set ℂ) := dimH_mono (Set.subset_univ _)
    _ = 2 := by rw [Real.dimH_univ_eq_finrank ℂ, Complex.finrank_real_complex]; norm_num

theorem BranchGermDimOne.proof (h₀ : LocalDimComponentBound.Statement) (h₁ : ZeroDimIsolated.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.Statement) : BranchGermDimOne.Statement := by
  intro n I q m c hm ⟨N, hN, hcov⟩
  let c₀ := c ⟨0, hm⟩
  have hq : q ∈ zeroSet I := c₀.map_zero ▸ c₀.mapsTo (Metric.mem_ball_self c₀.radius_pos)
  have hdimH : dimH (zeroSet I ∩ N) ≤ 2 :=
    (dimH_mono hcov).trans ((dimH_iUnion _).le.trans (iSup_le fun b ↦ (c b).dimH_image_le_two))
  apply le_antisymm
  · obtain ⟨W, hW, hIW, hqW, hle⟩ := h₀ n I q hq
    have hup : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : ℕ) := by
      refine (ringKrullDim_quotient_le W).trans (le_of_eq ?_)
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) := by
      have := hW
      exact ringKrullDim_nonneg_of_nontrivial
    obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = d := by
      revert hnn hup
      generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = x
      intro hup hnn
      induction x using WithBot.recBotCoe with
      | bot => exact absurd hnn (by simp)
      | coe e =>
        induction e using ENat.recTopCoe with
        | top => exact absurd hup (not_le.2 (WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n)))
        | coe d => exact ⟨d, rfl⟩
    rw [hd] at hle
    refine hle.trans ?_
    by_contra hlt
    have h2 : 2 ≤ d := by
      by_contra h
      exact hlt (by exact_mod_cast (by omega : d ≤ 1))
    have hpos := h₂ n d W hW hd q (interior N) isOpen_interior (mem_interior_iff_mem_nhds.2 hN) hqW
    have hsub : zeroSet W ∩ interior N ⊆ zeroSet I ∩ N :=
      fun x hx ↦ ⟨fun f hf ↦ hx.1 f (hIW hf), interior_subset hx.2⟩
    have hlt' : dimH (zeroSet W ∩ interior N) < (((2 * d : ℕ) : ℝ≥0) : ℝ≥0∞) := by
      refine ((dimH_mono hsub).trans hdimH).trans_lt ?_
      rw [ENNReal.coe_natCast]
      exact_mod_cast (by omega : 2 < 2 * d)
    have h0 := hausdorffMeasure_of_dimH_lt hlt'
    rw [NNReal.coe_natCast] at h0
    exact hpos.ne' h0
  · by_contra hlt
    have h0 : ringKrullDim (curveLocalRing I q) ≤ 0 := by
      generalize ringKrullDim (curveLocalRing I q) = x at hlt
      induction x using WithBot.recBotCoe with
      | bot => exact bot_le
      | coe e =>
        have he : e < 1 := by
          by_contra h'
          exact hlt (by exact_mod_cast not_lt.1 h')
        rw [Order.lt_one_iff] at he
        subst he
        exact le_rfl
    obtain ⟨N', hN', hiso⟩ := h₁ n I q h0
    have hcont : ContinuousAt c₀.toFun 0 :=
      c₀.differentiableOn.continuousOn.continuousAt (Metric.ball_mem_nhds 0 c₀.radius_pos)
    have hN'' : N' ∈ 𝓝 (c₀.toFun 0) := by rw [c₀.map_zero]; exact hN'
    have hev : ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), t ∈ Metric.ball 0 c₀.radius ∧ c₀.toFun t ∈ N' :=
      Filter.Eventually.and (Metric.ball_mem_nhds 0 c₀.radius_pos) (hcont hN'')
    have hne : (𝓝[≠] (0 : Fin 1 → ℂ)).NeBot := inferInstance
    have hev' : ∀ᶠ t in 𝓝[≠] (0 : Fin 1 → ℂ), (t ∈ Metric.ball 0 c₀.radius ∧ c₀.toFun t ∈ N') ∧ t ≠ 0 :=
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds hev).and self_mem_nhdsWithin
    obtain ⟨t, ⟨ht, htN⟩, ht0⟩ := hev'.exists
    have hx : c₀.toFun t = q := hiso ⟨c₀.mapsTo ht, htN⟩
    exact ht0 (c₀.injOn ht (Metric.mem_ball_self c₀.radius_pos) (hx.trans c₀.map_zero.symm))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

theorem ringKrullDim_quotient_le_sup_span_add {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R)
    (hI : I ≠ ⊤) {d : ℕ} (t : Fin d → R) (ht : ∀ i, t i ∈ IsLocalRing.maximalIdeal R) :
    ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ (I ⊔ Ideal.span (Set.range t))) + (d : ℕ) := by
  classical
  let s : Finset (R ⧸ I) := Finset.univ.image fun i => Ideal.Quotient.mk I (t i)
  have hs : Ideal.span (s : Set (R ⧸ I)) = (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    simp [s]
  have hjac : (Ideal.span (Set.range t)).map (Ideal.Quotient.mk I) ≤ Ring.jacobson (R ⧸ I) := by
    rw [← Ideal.jacobson_bot, ← Ideal.map_quotient_self I,
      ← Ideal.map_jacobson_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]),
      IsLocalRing.jacobson_eq_maximalIdeal I hI]
    refine Ideal.map_mono ?_
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ht i
  have hkey := ringKrullDim_le_ringKrullDim_quotient_add_card s
    fun x hx => hjac (hs ▸ Ideal.subset_span hx)
  rw [hs, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup I _)] at hkey
  refine hkey.trans ?_
  gcongr
  exact_mod_cast Finset.card_image_le.trans (by simp)

theorem one_le_ringKrullDim_localRingAt_sliceIdeal {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ)
    (hdim : ringKrullDim (localRingAt J q) = (d + 1 : ℕ)) :
    ((1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (localRingAt (sliceIdeal J L q) q) := by
  let φ := algebraMap (MvPolynomial (Fin n) ℂ)
    (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)))
  let t : Fin d → MvPolynomial (Fin n) ℂ := fun i => linPoly L i - C ((L *ᵥ q) i)
  have hI : J.map φ ≠ ⊤ := by
    intro h
    unfold localRingAt at hdim
    have : Subsingleton (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)) ⧸
        J.map φ) := Ideal.Quotient.subsingleton_iff.mpr h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have ht : ∀ i, φ (t i) ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ))) := by
    intro i
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    refine Ideal.mem_map_of_mem _ ?_
    simp [t, RingHom.mem_ker, eval_linPoly]
  have hkey := ringKrullDim_quotient_le_sup_span_add (J.map φ) hI (fun i => φ (t i)) ht
  have hsl : (sliceIdeal J L q).map φ = J.map φ ⊔ Ideal.span (Set.range fun i => φ (t i)) := by
    rw [sliceIdeal, Ideal.map_sup, Ideal.map_span, ← Set.range_comp]
    rfl
  rw [← hsl] at hkey
  change ringKrullDim (localRingAt J q) ≤ ringKrullDim (localRingAt (sliceIdeal J L q) q) + (d : ℕ)
    at hkey
  rw [hdim] at hkey
  generalize ringKrullDim (localRingAt (sliceIdeal J L q) q) = D at hkey ⊢
  induction D using WithBot.recBotCoe with
  | bot => simp at hkey
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe k =>
      have h2 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((k + d : ℕ) : WithBot ℕ∞) := by simpa using hkey
      have h3 : d + 1 ≤ k + d := by exact_mod_cast h2
      exact_mod_cast (show 1 ≤ k by omega)

theorem SliceLocalDimGeneral.proof (hL : LocalDimDomain.Statement)
    (hU : SliceLocalDimUpperZariski.Statement) : SliceLocalDimGeneral.Statement := by
  intro n d J q hJ hdim hq
  obtain ⟨F, hF, hgood⟩ := hU n d J q hJ hdim hq
  have hloc := hL n (d + 1) J hJ hdim q hq
  let e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ) := fun L ij => L ij.1 ij.2
  let ψ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ := fun y => Matrix.of fun i j => y (i, j)
  have he : Continuous e := continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2
  have hψ : Continuous ψ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  refine ⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hLF => le_antisymm (hgood L hLF)
    (one_le_ringKrullDim_localRingAt_sliceIdeal J L q hloc)⟩
  · exact isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const
  · rw [dense_iff_inter_open]
    rintro U hU ⟨L₀, hL₀⟩
    obtain ⟨y, hyU, hyF⟩ := exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hψ) ⟨e L₀, hL₀⟩
    exact ⟨ψ y, hyU, hyF⟩

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

theorem SliceLocalDimUpperZariski.ringKrullDim_le_of_finite {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Finite) : ringKrullDim S ≤ ringKrullDim R := by
  let _ := f.toAlgebra
  have : Module.Finite R S := hf
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  refine Order.krullDim_le_of_strictMono
    (fun p : PrimeSpectrum S => PrimeSpectrum.comap (algebraMap R S) p) ?_
  intro p p' h
  have h' : p.asIdeal < p'.asIdeal := h
  exact Ideal.IsIntegral.comap_lt_comap (R := R) h'

theorem SliceLocalDimUpperZariski.localDim_le {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (q : Fin n → ℂ) (hq : q ∈ zeroSet I) :
    ringKrullDim (localRingAt I q) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) := by
  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hIM : I ≤ M := fun f hf => RingHom.mem_ker.mpr (hq f hf)
  let m : Ideal (MvPolynomial (Fin n) ℂ ⧸ I) := M.map (Ideal.Quotient.mk I)
  have hm : m.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIM)
  have hsub : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ I) M.primeCompl =
      m.primeCompl := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · rintro ⟨z, hz, hzy⟩
      change Ideal.Quotient.mk I y ∉ m
      rw [← hzy]
      change Ideal.Quotient.mk I z ∉ M.map (Ideal.Quotient.mk I)
      rw [Ideal.mem_quotient_iff_mem hIM]
      exact hz
    · intro h
      change Ideal.Quotient.mk I y ∉ M.map (Ideal.Quotient.mk I) at h
      rw [Ideal.mem_quotient_iff_mem hIM] at h
      exact ⟨y, h, rfl⟩
  have : m.IsPrime := hm.isPrime
  have : IsLocalization.AtPrime (localRingAt I q) m := by
    unfold IsLocalization.AtPrime
    rw [← hsub]
    unfold localRingAt
    infer_instance
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (localRingAt I q)]
  exact Ideal.height_le_ringKrullDim_of_isPrime

theorem SliceLocalDimUpperZariski.quotient_dim_le_one {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) (M : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (hML : ∀ i j, M (Fin.castSucc i) j = L i j) (hfin : (projHom J M).toRingHom.Finite) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ sliceIdeal J L q) ≤ (1 : ℕ) := by
  set I := sliceIdeal J L q with hI
  have hJI : J ≤ I := le_sup_left
  let g : MvPolynomial (Fin (d + 1)) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I :=
    (Ideal.Quotient.factor hJI).comp (projHom J M).toRingHom
  have hg : g.Finite :=
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJI)) hfin
  let π : MvPolynomial (Fin (d + 1)) ℂ →+* Polynomial ℂ :=
    (aeval (Fin.lastCases (motive := fun _ => Polynomial ℂ) Polynomial.X
      (fun k => Polynomial.C ((L *ᵥ q) k)))).toRingHom
  let ψ : Polynomial ℂ →+* MvPolynomial (Fin n) ℂ ⧸ I :=
    Polynomial.eval₂RingHom (algebraMap ℂ _) (Ideal.Quotient.mk I (linPoly M (Fin.last d)))
  have hlin : ∀ k : Fin d, linPoly M k.castSucc = linPoly L k := by
    intro k
    simp only [linPoly, hML]
  have hCI : ∀ c : ℂ, algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I) c = Ideal.Quotient.mk I (C c) :=
    fun c => rfl
  have hcomp : ψ.comp π = g := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [π, ψ, g, projHom, pullback, hCI]
    · intro i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · simp [π, ψ, g, projHom, pullback]
      · have hmem : linPoly L k - C ((L *ᵥ q) k) ∈ I :=
          Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
        have hq : Ideal.Quotient.mk I (linPoly L k) = Ideal.Quotient.mk I (C ((L *ᵥ q) k)) :=
          Ideal.Quotient.eq.mpr hmem
        simp [π, ψ, g, projHom, pullback, hlin, hq, hCI]
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (f := π) (by rw [hcomp]; exact hg)
  calc ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) ≤ ringKrullDim (Polynomial ℂ) :=
        SliceLocalDimUpperZariski.ringKrullDim_le_of_finite ψ hψ
    _ = (1 : ℕ) := by
        rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
        rfl

theorem SliceLocalDimUpperZariski.proof : SliceLocalDimUpperZariski.Statement := by
  intro n d J q hJ hdim hq
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hWfin⟩ :=
    ComplexSets.FiniteProjectionsContainOpen.proof ComplexSets.ConeAvoidsFinite.proof
      ComplexSets.FiniteProjHomInjective.proof ComplexSets.ConeAvoidsOpen.proof
      (ComplexSets.ConeAvoidsExists.proof ComplexSets.LeadIdealDim.proof
        ComplexSets.LinearFormCut.proof ComplexSets.HomogDimZeroPow.proof) n (d + 1) J hJ hdim
  rw [hS] at hA₀
  obtain ⟨G, hGS, hG⟩ := hA₀
  let ext : Matrix (Fin d) (Fin n) ℂ → Matrix (Fin (d + 1)) (Fin n) ℂ :=
    fun L i j => if h : (i : ℕ) < d then L ⟨i, h⟩ j else A₀ i j
  let F : MvPolynomial (Fin d × Fin n) ℂ :=
    bind₁ (fun ij : Fin (d + 1) × Fin n =>
      if h : (ij.1 : ℕ) < d then X (⟨ij.1, h⟩, ij.2) else C (A₀ ij.1 ij.2)) G
  have hevF : ∀ L : Matrix (Fin d) (Fin n) ℂ,
      eval (fun ij : Fin d × Fin n => L ij.1 ij.2) F =
        eval (fun ij : Fin (d + 1) × Fin n => ext L ij.1 ij.2) G := by
    intro L
    change eval₂Hom (RingHom.id ℂ) _ (bind₁ _ G) = _
    rw [eval₂Hom_bind₁]
    change eval _ G = _
    refine congrArg (fun f => eval f G) (funext fun ij => ?_)
    simp only [ext]
    split_ifs <;> simp
  have hext0 : ext (fun i j => A₀ i.castSucc j) = A₀ := by
    funext i j
    simp only [ext]
    split_ifs with h
    · rfl
    · rfl
  refine ⟨F, fun h0 => hG ?_, fun L hL => ?_⟩
  · have h1 := hevF (fun i j => A₀ i.castSucc j)
    rw [hext0, h0, map_zero] at h1
    exact h1.symm
  · have hmem : ext L ∈ W := by
      rw [hS]
      exact ⟨G, hGS, (hevF L) ▸ hL⟩
    have hfp : IsFiniteProjection J (ext L) := hWfin hmem
    have hq' : q ∈ zeroSet (sliceIdeal J L q) := by
      rw [zeroSet_sliceIdeal]
      exact ⟨hq, rfl⟩
    refine (SliceLocalDimUpperZariski.localDim_le _ q hq').trans
      (SliceLocalDimUpperZariski.quotient_dim_le_one J L q (ext L) (fun i j => ?_) hfp.finite)
    simp [ext, i.isLt]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCurveBranchOrder.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ) (r : ℝ) (φ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → 0 < r →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) → φ 0 = w →
      ∀ g : MvPolynomial (Fin n ⊕ Fin M.m) ℂ,
        Ring.ord (pointLocalRing M.ideal w)
            (algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ) (pointLocalRing M.ideal w) g) =
          analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0

end

end GroundTheory.Heights₂.Heights
end
