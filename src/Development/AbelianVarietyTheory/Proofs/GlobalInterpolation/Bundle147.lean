module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle143
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle134
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle043
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle037
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle038
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.QuadraticSemicharactersOfProductThetaMem
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle046
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle047
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RightTranslationActionApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.LocalToGlobal.Divisibility.BrJoint
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle145
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_of_analytic {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : V → ℂ}
    (h : AnalyticOnNhd ℂ f Set.univ) : ContDiff ℂ ⊤ f :=
  contDiffOn_univ.1 (h.contDiffOn uniqueDiffOn_univ)

theorem contDiff_opU_one (L : PeriodPair) (s : ℂ) {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ContDiff ℂ ⊤ (Formalism.L2.Th1.F.opU L s f) := by
  have hd : Differentiable ℂ (Formalism.L2.Th1.F.opU L s f) := by
    have h1 : Differentiable ℂ (fun z : ℂ => f (z + s)) := hf.comp (differentiable_id.add_const s)
    have h2 : Differentiable ℂ (fun z : ℂ => Complex.exp (-(Real.pi : ℂ) * Formalism.L2.Th1.F.herm L z s
        - (Real.pi : ℂ) * Formalism.L2.Th1.F.herm L s s / 2)) := by
      unfold Formalism.L2.Th1.F.herm
      fun_prop
    exact h1.mul h2
  exact hd.contDiff

theorem norm_sqrt_inv {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) {m : ℕ} (hm : Nat.Coprime m q) :
    ‖ι (((Real.sqrt m : ℝ) : ℂ)⁻¹)‖ = 1 := by
  have h1 : (((Real.sqrt m : ℝ) : ℂ)) ^ 2 = (m : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg m)]; simp
  have h2 : ‖ι ((Real.sqrt m : ℝ) : ℂ)‖ ^ 2 = 1 := by
    rw [← norm_pow, ← map_pow, h1, map_natCast]
    exact GlobalTheory.MomOne.Basic.norm_nat_eq_one hm.symm
  have h3 : ‖ι ((Real.sqrt m : ℝ) : ℂ)‖ = 1 := by
    have := norm_nonneg (ι ((Real.sqrt m : ℝ) : ℂ))
    nlinarith [sq_nonneg (‖ι ((Real.sqrt m : ℝ) : ℂ)‖ - 1), sq_nonneg (‖ι ((Real.sqrt m : ℝ) : ℂ)‖ + 1)]
  rw [map_inv₀, norm_inv, h3, inv_one]

theorem norm_root {q : ℕ} [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) :
    ‖ι z‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm).1 (by rw [← norm_pow, ← map_pow, hz, map_one, norm_one])

theorem translates_latInt : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (t : D.what₂.Tau → ℂ) (n : ℕ), Nat.Coprime n q → (n : ℂ) • t ∈ B.lamM → LatInt ι (Ω / ι δ₀) B.lamM (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) := by
  intro D cc δ B hcc hδ q _ hq2 hjac hcop ι δ₀ θ Ω hPer t n hn hnt
  obtain ⟨g, e, hS, hidx, he, hten⟩ := GlobalTheory.T.exists_standard_isometry_fourthPower_split_prime D cc δ B hcc hδ q hq2 hjac hcop ι

  have hmem : B.thMM ∈ Formalism.L2.Th1.H.Th (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))
      (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau))) B.lamM :=
    (thM_spec B.L B.ω₀ B.cq B.lamM B.gC B.kappa (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) B.kappa_ne_zero).1
  have hUs : ContDiff ℂ ⊤ (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) :=
    contDiff_of_analytic (Formalism.L2.Th1.H.opUAnalytic (D.what₂.Tau → ℂ) _ t B.thMM hmem.1)
  have hthd : Differentiable ℂ B.th0 := (Formalism.L2.Th1.F.th0Basic B.L B.ω₀ hS.per hS.half).1

  obtain ⟨S, hSr⟩ := (Formalism.L2.Th1.H.repsExist _ _ _ hS.idx₁).1
  have hshape := Formalism.L2.Th1.H.quadraticSemicharacter_identity_reformulated₂ B.L B.ω₀ D.what₂.Tau (hOne B.L D.what₂.Tau) B.lamM _ _ g hS e B.thMM hten S hSr t
  have hidxC : Nat.Coprime (Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau))
      (Formalism.L2.Th1.H.imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) q :=
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hidx).symm
  set Im := Formalism.L2.Th1.H.imgLat (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM) with hIm
  set St := Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau) with hSt
  set idx := Formalism.L2.Th1.H.relIdx St Im with hidxdef
  set v : Fin 4 × D.what₂.Tau → ℂ := g (fun w => t w.2) with hv
  set ω : ℂ_[q] := Ω / ι δ₀ with hω
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : q = 1 := by simpa using hn
    exact (Fact.out : q.Prime).one_lt.ne' h1

  have hnv : (n : ℂ) • v ∈ Im := by
    refine AddSubgroup.mem_map.2 ⟨(n : ℂ) • (fun w : Fin 4 × D.what₂.Tau => t w.2), fun a => hnt, ?_⟩
    show g ((n : ℂ) • fun w : Fin 4 × D.what₂.Tau => t w.2) = (n : ℂ) • v
    rw [map_smul]

  have hord : ∀ x ∈ S, ∀ w, ((n * idx : ℕ) : ℂ) * (v w + x w) ∈ B.L.lattice := by
    intro x hx w
    have h1 : (n : ℂ) • (v + x) ∈ Im := by
      rw [smul_add]
      refine add_mem hnv ?_
      rw [Nat.cast_smul_eq_nsmul]
      exact nsmul_mem (hSr.1 x hx) n
    have h2 := Formalism.L2.Th1.H.relIdx_smul_mem St Im h1
    have h3 := ((AddSubgroup.mem_pi Set.univ).1 h2) w (Set.mem_univ _)
    have e1 : ((n * idx : ℕ) : ℂ) * (v w + x w) = (((idx : ℕ) : ℂ) • (n : ℂ) • (v + x)) w := by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      push_cast
      ring
    rw [e1]
    exact h3
  have hNq : Nat.Coprime (n * idx) q := Nat.Coprime.mul_left hn hidxC

  have hfac : ∀ x ∈ S, ∀ w,
      LatInt ι ω St (fun y : Fin 4 × D.what₂.Tau → ℂ => Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) := by
    intro x hx w
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι ℂ (Fin 4 × D.what₂.Tau → ℂ) ω (lamOf D cc δ) St
      (ContinuousLinearMap.proj w) _ (contDiff_opU_one B.L _ hthd) ?_
      (GlobalTheory.T.cm_theta_translates_prime_to_q_integral D cc δ B hcc hδ q hq2 hjac hcop ι δ₀ θ Ω hPer _ (n * idx) hNq (hord x hx w))
    intro y hy
    refine ⟨1, Nat.coprime_one_left q, ?_⟩
    rw [one_smul, ← B.lat]
    exact ((AddSubgroup.mem_pi Set.univ).1 hy) w (Set.mem_univ _)
  have hcd : ∀ (x : Fin 4 × D.what₂.Tau → ℂ) (w : Fin 4 × D.what₂.Tau),
      ContDiff ℂ ⊤ (fun y : Fin 4 × D.what₂.Tau → ℂ => Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) :=
    fun x w => (contDiff_opU_one B.L _ hthd).comp (contDiff_apply ℂ (fun _ => ℂ) w)
  have hprod : ∀ x : Fin 4 × D.what₂.Tau → ℂ, ContDiff ℂ ⊤ (fun y : Fin 4 × D.what₂.Tau → ℂ =>
      ∏ w, Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) :=
    fun x => contDiff_prod fun w _ => hcd x w

  have hP : ∀ x ∈ S, LatInt ι ω St (fun y : Fin 4 × D.what₂.Tau → ℂ =>
      ∏ w, Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) := fun x hx =>
    (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (Fin 4 × D.what₂.Tau → ℂ) ω St).1 (Fin 4 × D.what₂.Tau)
      (fun w y => Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w)) (hcd x) (hfac x hx)

  set r : (Fin 4 × D.what₂.Tau → ℂ) → ℂ := fun x => e * ((Real.sqrt idx : ℝ) : ℂ)⁻¹
      * Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) x
      * Complex.exp (-(Real.pi : ℂ) * Complex.I * (Formalism.L2.Th1.H.altE (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) v x : ℂ)) with hr
  have hrn : ∀ x ∈ S, ‖ι (r x)‖ ≤ 1 := by
    intro x hx
    have hx2 := hSr.1 x hx
    have hb : ‖ι (Formalism.L2.Th1.H.alphaQ B.cq (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) x)‖ = 1 := by
      rcases hS.betaSemi.1 x hx2 with h | h <;> simp [h]
    have hph : ‖ι (Complex.exp (-(Real.pi : ℂ) * Complex.I
        * (Formalism.L2.Th1.H.altE (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) v x : ℂ)))‖ = 1 :=
      norm_root ι (m := 2 * n) (by omega)
        (Formalism.L2.Th1.H.phase_root_selfDual _ Im hS.selfDual n hnv hx2)
    simp only [hr, map_mul, norm_mul, he, norm_sqrt_inv ι hidxC, hb, hph, one_mul, le_refl]
  set G : (Fin 4 × D.what₂.Tau → ℂ) → ℂ := fun y =>
    ∑ x ∈ S, r x * ∏ w, Formalism.L2.Th1.F.opU B.L (v w + x w) B.th0 (y w) with hG
  have hGd : ContDiff ℂ ⊤ G :=
    ContDiff.sum fun x _ => contDiff_const.mul (hprod x)
  have hGl : LatInt ι ω St G :=
    (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (Fin 4 × D.what₂.Tau → ℂ) ω St).2 _ S r _ (fun x _ => hprod x) hrn hP

  have hpull : LatInt ι ω (Formalism.L2.Th1.H.pow4 B.lamM)
      (fun z => G (LinearMap.toContinuousLinearMap (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) z)) := by
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι _ _ ω St _ _ G hGd ?_ hGl
    intro x hx
    refine ⟨idx, hidxC, ?_⟩
    have h1 : g x ∈ Im := AddSubgroup.mem_map.2 ⟨x, hx, rfl⟩
    have h2 := Formalism.L2.Th1.H.relIdx_smul_mem St Im h1
    rw [Nat.cast_smul_eq_nsmul] at h2
    exact h2
  have hfun : (fun z => G (LinearMap.toContinuousLinearMap (g : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) z))
      = Formalism.L2.Th1.H.tens4 (Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) t B.thMM) := by
    funext z
    have hz := hshape (g z)
    rw [LinearEquiv.symm_apply_apply] at hz
    rw [hz]
    rfl
  rw [hfun] at hpull
  exact GlobalTheory.T.latticeJetsAreBoundedMoments_of_tensorFourthPower q ι D.what₂.Tau ω B.lamM _ hUs hpull

end GlobalTheory.MomN
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

noncomputable section
namespace GlobalTheory.SWQ.FourierSeries

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem bd_rat_add (a : Fin N → F) (η ξ : Fin N → F) (u : Fin N → AF F) :
    Bd (AF F) a (rat η + u) (rat ξ) = algebraMap F (AF F) (Bd F a η ξ) + Bd (AF F) a u (rat ξ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Bd, rat, Pi.add_apply, map_sum, map_mul, mul_add, add_mul, Finset.sum_add_distrib,
    Algebra.algebraMap_self, RingHom.id_apply]

theorem bd_sub (a : Fin N → F) (ξ' ξ : Fin N → F) (u : Fin N → AF F) :
    Bd (AF F) a u (rat ξ') + -Bd (AF F) a u (rat ξ) = Bd (AF F) a u (rat (ξ' - ξ)) := by
  simp only [Bd, rat, Pi.sub_apply, map_sub, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => by ring

theorem bd_zero (a : Fin N → F) (u : Fin N → AF F) : Bd (AF F) a u (rat 0) = 0 := by
  simp [Bd, rat]

theorem continuous_bd (a : Fin N → F) (ξ : Fin N → F) :
    Continuous fun u : Fin N → AF F => Bd (AF F) a u (rat ξ) := by
  unfold Bd
  exact continuous_finsetSum _ fun l _ => (continuous_const.mul (continuous_apply l)).mul continuous_const

end GlobalTheory.SWQ.FourierSeries

namespace GlobalTheory.SWQ.FourierSeries

theorem countable_fn (F : Type) [Field F] [NumberField F] (N : ℕ) : Countable (Fin N → F) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable
  infer_instance

theorem fourier_series : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ D : Set (Fin N → AF F), IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) → muV N ν D = 1 → ∀ (P : (Fin N → AF F) → ℂ) (c : (Fin N → F) → ℂ), Continuous P → (∀ ξ u, P (rat ξ + u) = P u) → (∀ ξ, ∫ u in D, P u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = c ξ) → Summable (fun ξ => ‖c ξ‖) → ∀ u, P u = ∑' ξ, c ξ * ψ (Bd (AF F) a u (rat ξ)) := by
  intro F _ _ N ψ lam ν a hC D hD hD1 P c hP hper hc hsum
  classical
  have hC' := hC
  obtain ⟨_, ⟨hψc, hψn, hψF, -⟩, -, hcov, -⟩ := hC'
  obtain ⟨-, -, -, ⟨K, hK, hKc⟩, -⟩ := GlobalTheory.T.rationalVectors_adeles_fundamentalDomain_mass_one F N ν hcov
  haveI : Countable (Fin N → F) := countable_fn F N
  haveI : IsFiniteMeasure ((muV N ν).restrict D) := isFiniteMeasure_restrict.mpr (by rw [hD1]; simp)
  have hmass : ((muV N ν).restrict D) Set.univ = 1 := by rw [Measure.restrict_apply_univ, hD1]
  have he : ∀ ξ, Continuous fun u : Fin N → AF F => ψ (Bd (AF F) a u (rat ξ)) :=
    fun ξ => hψc.comp (continuous_bd a ξ)
  set S : (Fin N → AF F) → ℂ := fun u => ∑' ξ, c ξ * ψ (Bd (AF F) a u (rat ξ)) with hSdef
  have hS : Continuous S := continuous_tsum (fun ξ => continuous_const.mul (he ξ)) hsum
    (fun ξ u => by simp [norm_mul, hψn])
  have hSper : ∀ η u, S (rat η + u) = S u := by
    intro η u
    simp only [hSdef, bd_rat_add, AddChar.map_add_eq_mul, hψF, one_mul]

  obtain ⟨M, hM⟩ : ∃ M, ∀ u, ‖P u‖ ≤ M := by
    obtain ⟨M, hM⟩ := (hK.image hP.norm).bddAbove
    refine ⟨M, fun u => ?_⟩
    obtain ⟨ξ, hξ⟩ := hKc u
    have : P u = P (u - rat ξ) := by
      rw [← hper ξ (u - rat ξ)]; congr 1; abel
    rw [this]; exact hM ⟨_, hξ, rfl⟩
  set Q : (Fin N → AF F) → ℂ := fun u => P u - S u with hQdef
  have hQc : Continuous Q := hP.sub hS
  have hQper : ∀ ξ u, Q (rat ξ + u) = Q u := fun ξ u => by simp only [hQdef, hper, hSper]
  have hint : ∀ f : (Fin N → AF F) → ℂ, Continuous f → ∀ B : ℝ, (∀ u, ‖f u‖ ≤ B) →
      Integrable f ((muV N ν).restrict D) :=
    fun f hf B hB => Integrable.of_bound hf.aestronglyMeasurable B (Eventually.of_forall hB)
  have hcoefS : ∀ ξ, ∫ u in D, S u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = c ξ := by
    intro ξ
    have hterm : ∀ ξ' u, c ξ' * ψ (Bd (AF F) a u (rat ξ')) * ψ (-(Bd (AF F) a u (rat ξ))) =
        c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ))) := by
      intro ξ' u
      rw [mul_assoc, ← AddChar.map_add_eq_mul, bd_sub]
    have hsw : ∀ u, S u * ψ (-(Bd (AF F) a u (rat ξ))) =
        ∑' ξ', c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ))) := by
      intro u
      simp only [hSdef, ← tsum_mul_right, hterm]
    simp_rw [hsw]
    have hInt : ∀ ξ', Integrable (fun u => c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ))))
        ((muV N ν).restrict D) :=
      fun ξ' => hint _ (continuous_const.mul (he _)) ‖c ξ'‖ (fun u => by simp [norm_mul, hψn])
    have hnorm : ∀ ξ', ∫ u in D, ‖c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ)))‖ ∂(muV N ν) = ‖c ξ'‖ := by
      intro ξ'
      simp only [norm_mul, hψn, mul_one]
      rw [integral_const, smul_eq_mul, measureReal_def, hmass]; simp
    rw [← integral_tsum_of_summable_integral_norm hInt (by simp_rw [hnorm]; exact hsum)]
    have hval : ∀ ξ', ∫ u in D, c ξ' * ψ (Bd (AF F) a u (rat (ξ' - ξ))) ∂(muV N ν) =
        if ξ' = ξ then c ξ else 0 := by
      intro ξ'
      rw [integral_const_mul]
      split_ifs with h
      · subst h
        simp only [sub_self, bd_zero, AddChar.map_zero_eq_one]
        simp [integral_const, measureReal_def, hmass]
      · rw [GlobalTheory.T.integral_adelicVectors_character_orthogonality F N ψ lam ν a hC D hD hD1 (ξ' - ξ) (sub_ne_zero.mpr h), mul_zero]
    simp_rw [hval]
    simp
  have hQcoef : ∀ ξ : Fin N → F, ∫ u in D, Q u * ψ (-(Bd (AF F) a u (rat ξ))) ∂(muV N ν) = 0 := by
    intro ξ
    have h1 : Integrable (fun u => P u * ψ (-(Bd (AF F) a u (rat ξ)))) ((muV N ν).restrict D) :=
      hint _ (hP.mul (hψc.comp (continuous_bd a ξ).neg)) M (fun u => by simpa [norm_mul, hψn] using hM u)
    have hSb : ∀ u, ‖S u‖ ≤ ∑' ξ, ‖c ξ‖ := fun u =>
      (norm_tsum_le_tsum_norm (hsum.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun ξ' => by simp [norm_mul, hψn]))).trans
        (le_of_eq (tsum_congr fun ξ' => by simp [norm_mul, hψn]))
    have h2 : Integrable (fun u => S u * ψ (-(Bd (AF F) a u (rat ξ)))) ((muV N ν).restrict D) :=
      hint _ (hS.mul (hψc.comp (continuous_bd a ξ).neg)) _ (fun u => by simpa [norm_mul, hψn] using hSb u)
    simp only [hQdef, sub_mul]
    rw [integral_sub h1 h2, hc, hcoefS, sub_self]
  have hQ0 := GlobalTheory.T.adelicPeriodic_continuous_eq_zero_of_fourier_coeff F N ψ lam ν a hC D hD hD1 Q hQc hQper hQcoef
  intro u
  have := congrFun hQ0 u
  simp only [hQdef, Pi.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.SWQ.FourierSeries
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option linter.unusedVariables false

namespace GlobalTheory.PerQ.RowIntModel

theorem mem_mtildeL_iff {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (z : MtildeV W Ch sel mu P) :
  z ∈ MtildeL W Ch sel mu P ↔ ∀ d : RowPt Pr R sel mu, z.1 d ∈ nabAt X.emb W.sgTrue d.1.N := Iff.rfl

theorem mtildeL_rep_mem {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (z : MtildeV W Ch sel mu P) (hz : z ∈ MtildeL W Ch sel mu P) (c : (stepX Ch sel mu P).Cl) :
  ∃ y ∈ nabAt X.emb W.sgTrue ((stepX Ch sel mu P).rep c).1.1.deco.1.N, y = z.1 (toRow sel mu ((stepX Ch sel mu P).rep c).1.1) :=
  ⟨z.1 (toRow sel mu ((stepX Ch sel mu P).rep c).1.1), toRow_N sel mu ((stepX Ch sel mu P).rep c).1.1 ▸ (mem_mtildeL_iff W Ch sel mu P z).1 hz (toRow sel mu ((stepX Ch sel mu P).rep c).1.1), rfl⟩

open GlobalTheory.PerQ
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws)



section G
open GlobalTheory.PeriodOnStep
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)

theorem span_mtildeL (hX : X.Ok) : Submodule.span X.K (MtildeL W Ch sel mu P : Set (MtildeV W Ch sel mu P)) = ⊤ := (MtildeH_good W Ch hX sel mu P).2.2

theorem span_toMtP (hX : X.Ok) : Submodule.span ℂ (Set.range fun z : MtildeL W Ch sel mu P => toMtP W Ch sel mu P σ z.1) = ⊤ :=
    toCForm_span_of_span σ W.sgTrue _ _ hX (φ := fun z : MtildeL W Ch sel mu P => z.1) (eq_top_iff.2 ((span_mtildeL W Ch sel mu P hX).ge.trans (Submodule.span_mono fun z hz => ⟨⟨z, hz⟩, rfl⟩)))

include hd in
theorem exists_form_of_mt (F : (perOn W Ch sel mu P b0 til ext tz (fun _ => ⊤)).Mt X.emb σ) : ∃ G : MtP W Ch sel mu P σ, ∀ b d, F.1 b d = G.1 (toRow sel mu d.1.1) := by
  have hl : FrLaw σ W.sgTrue (rowTyG Ch P) (levQX R sel mu) ⊤ fun p : XPt Pr R sel mu => F.1 () (trivPt X _ _ _ _ p) := by
    intro p
    refine ⟨(F.2 () _).1, fun g hg => ?_⟩
    show F.1 () (trivPt X _ _ _ _ (g • p)) = _
    rw [← stepX_smul_trivPt]
    exact (F.2 () (trivPt X _ _ _ _ p)).2 g hg
  obtain ⟨G, hG, e⟩ := hl.exists_form σ W.sgTrue (isSubLev_top _ _) hd
  exact ⟨⟨G, hG⟩, fun b p => ((e p.1.1).trans (congrArg (F.1 ()) ((trivPt X _ ∅ Pr.vGs (QE sel (mu : Chr X.F X.E X.K))).apply_symm_apply p))).symm⟩

theorem exists_mem_of_form (hX : X.Ok) (T : Submodule ℂ ((perOn W Ch sel mu P b0 til ext tz (fun _ => ⊤)).Mt X.emb σ))
  (hT : ∀ z ∈ MtildeL W Ch sel mu P, rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ z ∈ T) (G' : MtP W Ch sel mu P σ) : ∃ F' ∈ T, ∀ b d, F'.1 b d = G'.1 (toRow sel mu d.1.1) := by
    have hG' : G' ∈ Submodule.span ℂ (Set.range fun z : MtildeL W Ch sel mu P => toMtP W Ch sel mu P σ z.1) := by
      rw [span_toMtP W Ch sel mu P σ hX]; exact Submodule.mem_top
    induction hG' using Submodule.span_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact ⟨_, hT z.1 z.2, fun _ _ => rfl⟩
    | zero => exact ⟨0, zero_mem _, fun _ _ => rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ea⟩ := hx; obtain ⟨b, hb, eb⟩ := hy
      exact ⟨a + b, add_mem ha hb, fun c d => congrArg₂ (· + ·) (ea c d) (eb c d)⟩
    | smul r x _ hx =>
      obtain ⟨a, ha, ea⟩ := hx
      exact ⟨r • a, Submodule.smul_mem _ _ ha, fun c d => congrArg (r • ·) (ea c d)⟩

theorem eq_top_of_rowEmb_mem (hX : X.Ok) (T : Submodule ℂ ((perOn W Ch sel mu P b0 til ext tz (fun _ => ⊤)).Mt X.emb σ))
  (hT : ∀ z ∈ MtildeL W Ch sel mu P, rowEmb W Ch sel mu P b0 til ext tz (fun _ => ⊤) hd σ z ∈ T) : T = ⊤ :=
  Submodule.eq_top_iff'.2 fun F => (exists_form_of_mt W Ch sel mu P b0 til ext tz hd σ F).elim fun G e =>
    (exists_mem_of_form W Ch sel mu P b0 til ext tz hd σ hX T hT G).elim fun F' h =>
      (congrArg (· ∈ T) (Subtype.ext (funext fun b => funext fun p => (h.2 b p).trans (e b p).symm) : F' = F)).mp h.1
end G

end GlobalTheory.PerQ.RowIntModel
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

theorem _root_.GlobalTheory.T.normalisedFamily_latticeHyp_and_smooth : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.VecP χ → Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ ∧ (ambOf s B χ cD).ESmooth a b := by
  first | exact @GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth | exact GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth | (intros; apply GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth <;> assumption)
end

section

namespace GlobalTheory.LvT.BuiltChain

theorem branching_ok : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6 := Formalism.L2.DIV.BrJ.branching_interlacing_pairs

end GlobalTheory.LvT.BuiltChain
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitary_volume_eq_rank_mass_all_signatures : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → D.vol W = massI D (P + Q) := by
  first | exact @GlobalTheory.Glob.vol_eq_massI_all_sig | exact GlobalTheory.Glob.vol_eq_massI_all_sig | (intros; apply GlobalTheory.Glob.vol_eq_massI_all_sig <;> assumption)
end
