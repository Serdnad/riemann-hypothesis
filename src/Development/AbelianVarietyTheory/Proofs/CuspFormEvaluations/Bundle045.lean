module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle007
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle029
import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle001
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
import Mathlib.RingTheory.Henselian
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle006
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle007
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.HostClear

theorem absNorm_pos (D : D7) : 0 < Ideal.absNorm D.host.ccK :=
  Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)

theorem d_pos (D : D7) : 0 < D.host.d := D.host.hyp.2.1.pos

theorem sqrt_ne_zero (D : D7) : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have h1 := D.host.sqrtMinusD_sq
  rw [h] at h1
  have h2 : (D.host.d : D.host.E) = 0 := by linear_combination h1
  exact (d_pos D).ne' (by exact_mod_cast h2)

theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.host.E →+* ℂ) :
    ‖τ D.host.xi0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by
  have hn : ‖τ D.host.sqrtMinusD‖ ^ 2 = D.host.d := by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg, Complex.norm_natCast]
  have h1 : ‖τ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  unfold Formalism.BasicNotions.Host.xi0
  rw [map_div₀, map_mul, map_natCast, map_neg, map_one, norm_div, norm_neg, norm_one, norm_mul,
    Complex.norm_natCast, h1]

theorem different_le (D : D7) : differentIdeal ℤ (𝓞 D.host.E) ≤ D.host.𝔟 := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)]
  refine (Ideal.mul_le_inf.trans inf_le_left).trans ?_
  rw [D.host.𝔟_spec.1]
  exact Ideal.mul_le_inf.trans inf_le_left

theorem isIntegral_mul_of_mem (D : D7) {z : 𝓞 D.host.E} (hz : z ∈ D.host.𝔟) {a : D.host.E} (ha : a ∈ D.host.AA) :
    IsIntegral ℤ ((z : D.host.E) * a) := by
  obtain ⟨hB, -⟩ := bB_ne D
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at ha
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hB] at ha
  obtain ⟨w, -, hw⟩ := (FractionalIdeal.mem_coeIdeal _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
  have : (z : D.host.E) * a = (w : D.host.E) := by
    rw [mul_comm]; exact hw.symm
  rw [this]
  exact w.isIntegral_coe

theorem absNorm_mem_AA (D : D7) : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA := by
  obtain ⟨hB, -⟩ := bB_ne D
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hB]
  intro y hy
  obtain ⟨z, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have h1 : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
    rwa [map_natCast] at this
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨_, D.host.ccE.mul_mem_right z h1, ?_⟩
  rw [map_mul, map_natCast]

theorem host_clear : ∀ (D : D7) (L : ℝ), 2 ≤ L → lrd D ≤ 2 * L → Real.log D.host.d ≤ 2 * L → Real.log (Ideal.absNorm D.host.ccK) ≤ 2 * L → (∃ NA : ℕ, 0 < NA ∧ (∀ a ∈ D.host.AA, IsIntegral ℤ ((NA : D.host.E) * a)) ∧ Real.log NA ≤ 4 * L) ∧ ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA ∧ 0 < Ideal.absNorm D.host.ccK ∧ (∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : D.host.E) * (2 * D.host.xi0)) ∧ Real.log m ≤ 4 * L) ∧ Real.log (1 / (2 * xiR D)) ≤ 3 * L ∧ fdeg D.host.E = D.R.f ∧ Real.log (dE D.host.E) ≤ 4 * fdeg D.host.E * L ∧ Real.log (rdE D.host.E) ≤ 2 * L ∧ D.R.f ≤ D.R.r ∧ 1 ≤ D.R.f ∧ ReciprocityTheory.ChartRestriction.G.FD.cc D.host.xi0 = -D.host.xi0 ∧ D.host.xi0 ≠ 0 ∧ (∀ τ : D.host.E →+* ℂ, ‖τ D.host.xi0‖ = xiR D) := by
  intro D L hL hrd hd hc
  have hN := absNorm_pos D
  have hd0 := d_pos D
  have hNR : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hN
  have hdR : (0 : ℝ) < D.host.d := by exact_mod_cast hd0
  have hNE : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hs := sqrt_ne_zero D
  have hfin := GlobalTheory.PinNum.finrank_host D
  have hf1 : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    unfold Ranks.f; omega
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  have hfd : fdeg D.host.E = D.R.f := by
    unfold fdeg; rw [hfin]; omega
  have hdisc : 0 < |((NumberField.discr D.host.E : ℤ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have hlog : Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)| ≤ 4 * D.R.f * L := by
    unfold lrd at hrd
    rw [div_le_iff₀ (by positivity)] at hrd
    linarith
  refine ⟨?_, absNorm_mem_AA D, hN, ?_, ?_, hfd, ?_, ?_, ?_, hf1, conj_xi0_alt D, ?_, ?_⟩
  · have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
    obtain ⟨N, hN0, hNm, hNle⟩ := GlobalTheory.T.exists_natCast_mem_differentIdeal_pow_le_discr_sq D.host.E
    refine ⟨N, hN0, fun a ha => ?_, ?_⟩
    · have := isIntegral_mul_of_mem D (different_le D hNm) ha
      simpa using this
    · have hNR' : (0 : ℝ) < N := by exact_mod_cast hN0
      have h1 := Real.log_le_log (by positivity) hNle
      rw [Real.log_pow, Real.log_pow, hfin] at h1
      push_cast at h1
      have h2 : (D.R.f : ℝ) * Real.log N ≤ D.R.f * (4 * L) := by linarith
      exact le_of_mul_le_mul_left h2 (by linarith)
  · refine ⟨Ideal.absNorm D.host.ccK * D.host.d, Nat.mul_pos hN hd0, ?_, ?_⟩
    · have h1 : ((Ideal.absNorm D.host.ccK * D.host.d : ℕ) : D.host.E) * (2 * D.host.xi0) =
          2 * D.host.sqrtMinusD := by
        have h2 : (D.host.d : D.host.E) = -D.host.sqrtMinusD ^ 2 := by
          rw [D.host.sqrtMinusD_sq, neg_neg]
        unfold Formalism.BasicNotions.Host.xi0
        push_cast
        rw [h2]
        field_simp
      rw [h1]
      exact IsIntegral.mul (by exact_mod_cast isIntegral_natCast (R := ℤ) (B := D.host.E) 2) (sqrtMinusD_isIntegral D)
    · push_cast
      rw [Real.log_mul hNR.ne' hdR.ne']
      linarith
  · have hsq : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 hdR
    have h1 : 1 / (2 * xiR D) = (Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d / 2 := by
      unfold xiR
      rw [norm_embedding_hostFormConstant_eq]
      field_simp
    rw [h1, Real.log_div (by positivity) two_ne_zero, Real.log_mul hNR.ne' hsq.ne', Real.log_sqrt hdR.le]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  · rw [hfd]; exact hlog
  · unfold rdE dE
    rw [Real.log_rpow hdisc, hfin]
    unfold lrd at hrd
    push_cast
    rw [one_div_mul_eq_div]
    exact hrd
  · have h1 := D.R.f_le_k
    have h2 := D.R.two_le_m
    unfold Ranks.f Ranks.n Ranks.r
    omega
  · unfold Formalism.BasicNotions.Host.xi0
    exact div_ne_zero (neg_ne_zero.2 one_ne_zero) (mul_ne_zero hNE hs)
  · intro τ
    unfold xiR
    rw [norm_embedding_hostFormConstant_eq, norm_embedding_hostFormConstant_eq]

end GlobalTheory.HostClear
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem half_level_generator_norm :
    ∀ (D : D7) (T : Top D) (_h : LawsP T) (_EX : ErrX D), ∃ α : 𝓞 D.host.E, α * T.Q.H.bar α = (T.Q.l.M : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {T.Q.H.bar α} := by
  intro D T h _EX
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM

  have hbb : ∀ x : 𝓞 D.host.E, T.Q.H.bar (T.Q.H.bar x) = x := by
    intro x
    rw [bar_core T.toCore, bar_core T.toCore, barE_barE]

  have hn : ∀ i, piOf T.toCore _EX i * T.Q.H.bar (piOf T.toCore _EX i) = (D.host.g i : 𝓞 D.host.E) := by
    intro i
    rw [bar_core T.toCore]
    exact piOf_mul_barE T.toCore _EX i
  set π₀ := piOf T.toCore _EX 0
  set π₁ := piOf T.toCore _EX 1
  refine ⟨T.Q.H.bar (π₀ * π₁), ?_, ?_⟩
  · rw [hbb, map_mul, level_M T.toCore hM]
    have h0 := hn 0
    have h1 := hn 1
    push_cast
    rw [← h0, ← h1]
    ring
  · rw [hbb, Mb_eq T.toCore hM, ← span_piOf T.toCore hM _EX 0, ← span_piOf T.toCore hM _EX 1,
      Ideal.span_singleton_mul_span_singleton]

end GlobalTheory.RunIn
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

theorem cc_eq_host_conj (D : D7) (x : D.host.E) :
    ReciprocityTheory.ChartRestriction.G.FD.cc x = D.host.conj x :=
  bridge_star_holds D.R D.host x

theorem principalDatum_trace_perfect : ∀ D : D7, ∃ AA : Submodule (𝓞 D.host.E) D.host.E,
    AA.FG ∧ AA ≠ ⊥ ∧ ∀ x : D.host.E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ,
      Algebra.trace ℚ D.host.E (D.host.xi0 * x * a * ReciprocityTheory.ChartRestriction.G.FD.cc b) = z) ↔
        IsIntegral ℤ x := by
  intro D
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hA := AA_ne_zero hP D
  have hone : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := one_ne_zero
  refine ⟨(D.host.AA : Submodule (𝓞 D.host.E) D.host.E), ?_, ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact FractionalIdeal.fg_of_isNoetherianRing le_rfl _
  · intro h0
    exact hA (FractionalIdeal.coeToSubmodule_eq_bot.1 h0)
  · have h1 : ∀ w ∈ D.host.AA * D.host.AAbar, ∀ c : 𝓞 D.host.E, ∃ z : ℤ,
        Algebra.trace ℚ D.host.E (D.host.xi0 * x * (c • w)) = z := by
      intro w hw
      refine FractionalIdeal.mul_induction_on (C := fun w => ∀ c : 𝓞 D.host.E, ∃ z : ℤ,
        Algebra.trace ℚ D.host.E (D.host.xi0 * x * (c • w)) = z) hw
        (fun a ha b hb c => ?_) (fun u v hu hv c => ?_)
      · obtain ⟨z, hz⟩ := h (c • a) (Submodule.smul_mem _ c ha) (D.host.conj b) (conj_mem_AA D hb)
        refine ⟨z, ?_⟩
        rw [cc_eq_host_conj, conj_conj] at hz
        rw [← hz, ← smul_mul_assoc, mul_assoc (D.host.xi0 * x)]
      · obtain ⟨z, hz⟩ := hu c
        obtain ⟨z', hz'⟩ := hv c
        refine ⟨z + z', ?_⟩
        rw [smul_add, mul_add, map_add (f := _), hz, hz', Int.cast_add]
    have h2 : x ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.dual ℤ ℚ
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) := by
      rw [FractionalIdeal.mem_dual (FractionalIdeal.dual_ne_zero ℤ ℚ hone)]
      intro a ha
      rw [← dual_eq hP D, mul_assoc, FractionalIdeal.mem_singleton_mul] at ha
      obtain ⟨w, hw, rfl⟩ := ha
      obtain ⟨z, hz⟩ := h1 w hw 1
      rw [one_smul] at hz
      refine ⟨z, ?_⟩
      rw [Algebra.traceForm_apply, ← mul_assoc, mul_comm x, hz]
      exact eq_intCast _ _
    rw [FractionalIdeal.dual_dual, FractionalIdeal.mem_one_iff] at h2
    obtain ⟨c, rfl⟩ := h2
    exact c.isIntegral_coe
  · intro a ha b hb
    have hm : (⟨x, h⟩ : 𝓞 D.host.E) • (a * D.host.conj b) ∈ NAA D :=
      Submodule.smul_mem _ _ (FractionalIdeal.mul_mem_mul ha (conj_mem_AAbar D hb))
    obtain ⟨z, hz⟩ := trace_int_of_mem hP D hm
    refine ⟨z, ?_⟩
    rw [← hz, cc_eq_host_conj, Algebra.smul_def]
    congr 1
    change _ = D.host.xi0 * (x * (a * D.host.conj b))
    ring

end GlobalTheory
end

section

set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.RunIn

namespace GlobalTheory


open scoped TensorProduct in
theorem natCard_quot_smul_top_of_projective {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  classical
  open scoped TensorProduct in
  have hA : Finite (Ideal (R ⧸ I)) :=
    Finite.of_injective (fun J : Ideal (R ⧸ I) => (J : Set (R ⧸ I))) SetLike.coe_injective
  have hMS : Finite (MaximalSpectrum (R ⧸ I)) :=
    Finite.of_injective (fun m : MaximalSpectrum (R ⧸ I) => m.asIdeal) (fun a b h => MaximalSpectrum.ext h)
  have rk : ∀ P : MaximalSpectrum (R ⧸ I), Module.finrank ((R ⧸ I) ⧸ P.1)
      (((R ⧸ I) ⧸ P.1) ⊗[R ⧸ I] ((R ⧸ I) ⊗[R] N)) = Module.finrank R N := by
    intro P
    have hP := P.2
    let _ : Field ((R ⧸ I) ⧸ P.1) := Ideal.Quotient.field P.1
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.1) ((R ⧸ I) ⧸ P.1) N).finrank_eq]
    have h1 := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := (R ⧸ I) ⧸ P.1)
      (M := ((R ⧸ I) ⧸ P.1) ⊗[R] N)) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_baseChange, Pi.natCast_apply, Nat.cast_id] at h1
    rw [← h1]
    generalize PrimeSpectrum.comap (algebraMap R ((R ⧸ I) ⧸ P.1)) ⟨⊥, Ideal.isPrime_bot⟩ = q
    obtain ⟨p, hp⟩ := q
    rw [← Ideal.finrank_fiber_eq_rankAtStalk, Ideal.finrank_fiber_eq_finrank]
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N)
    (Module.finrank R N) rk
  calc Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card ((R ⧸ I) ⊗[R] N) :=
        Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv.symm
    _ = Nat.card (Fin (Module.finrank R N) → R ⧸ I) := Nat.card_congr b.equivFun.toEquiv
    _ = Nat.card (R ⧸ I) ^ Module.finrank R N := by simp [Nat.card_fun]

theorem absNorm_level_half {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (l : Level H) :
    Ideal.absNorm l.Mb = l.M ^ FD.fdeg E := by
  have h1 : Ideal.absNorm (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm l.Mb := by
    simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv l.Mb _ H.bar rfl).toEquiv.symm
  have h2 := congrArg Ideal.absNorm l.prod
  rw [map_mul, h1, Ideal.absNorm_span_singleton] at h2
  have h3 : (Algebra.norm ℤ ((l.M : ℕ) : 𝓞 E)).natAbs = l.M ^ Module.finrank ℚ E := by
    have : ((l.M : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (l.M : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have hev : Module.finrank ℚ E = 2 * FD.fdeg E := by
    have h := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h
    unfold FD.fdeg
    omega
  rw [h3, hev, pow_mul', ← sq] at h2
  exact Nat.pow_left_injective two_ne_zero h2

theorem card_levQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H),
    Finite (LevQ Dw l) ∧ Nat.card (LevQ Dw l) = l.M ^ (FD.fdeg E * (Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw l
  unfold LevQ
  have := Dw.fin
  have := Dw.proj
  have hN := absNorm_level_half l
  have : Finite (𝓞 E ⧸ l.Mb) := by
    rw [← Ideal.absNorm_ne_zero_iff, hN]
    exact pow_ne_zero _ (by have := l.three_le; omega)
  have hc := natCard_quot_smul_top_of_projective (N := Dw.La) l.Mb
  have hq : Nat.card (𝓞 E ⧸ l.Mb) = l.M ^ FD.fdeg E := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Dw.rank, hq, ← pow_mul] at hc
  refine ⟨?_, hc⟩
  apply Nat.finite_of_card_ne_zero
  rw [hc]
  exact pow_ne_zero _ (by have := l.three_le; omega)

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem pPow_size : ∀ (D : D7) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ D.host.q ∧ 1 ≤ D.host.d ∧ 0 ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) ∧ 0 ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ∧ (c2 D w : ℝ) * Real.log D.host.QS + (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) * Real.log D.host.q + (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) * Real.log D.host.d ≤ ((WeightAlgebra.DF w : ℝ) + 1) * Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) ∧ ∀ a b c : ℕ, 1 ≤ pPow D a b c ∧ Real.log (pPow D a b c) = a * Real.log D.host.QS + b * Real.log D.host.q + c * Real.log D.host.d := by
  intro D j w
  have hq : 1 ≤ D.host.q := by have := D.host.qd_big.1; omega
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hqR : (1 : ℝ) ≤ D.host.q := by exact_mod_cast hq
  have hdR : (1 : ℝ) ≤ D.host.d := by exact_mod_cast hd
  have hlq : 0 ≤ Real.log D.host.q := Real.log_nonneg hqR
  have hld : 0 ≤ Real.log D.host.d := Real.log_nonneg hdR
  have hQ : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hl2 : 0 ≤ Real.log D.host.QS := Real.log_nonneg hQ
  have hQf : (D.host.QS : ℝ) ≤ 4 * ((D.R.f : ℝ) / 2) ^ 2 := by
    have h1 : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by exact_mod_cast D.host.QS_le
    have h2 : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
    rw [h2]; nlinarith [sq_nonneg (D.R.n : ℝ)]
  have hlf : Real.log D.host.QS ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2) := Real.log_le_log (by linarith) hQf
  have hlog : Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) =
      Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2) + Real.log D.host.q + Real.log D.host.d := by
    have h0 : (0 : ℝ) < 4 * ((D.R.f : ℝ) / 2) ^ 2 := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul h0.ne' (by positivity)]
  have hD : (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := Nat.cast_nonneg _
  refine ⟨hq, hd, ?_, ?_, ?_, ?_⟩
  · rw [hlog]; linarith
  · apply Real.log_nonneg
    have h0 : (1 : ℝ) ≤ D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).one_le
    have h1 : (1 : ℝ) ≤ D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).one_le
    nlinarith
  · have hc2 : (c2 D w : ℝ) = (WeightAlgebra.DF w : ℝ) := rfl
    have hch : (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) ≤ (WeightAlgebra.DF w : ℝ) + 1 := by
      have h1 := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) / 2 by positivity)).le
      unfold Formalism.MainNotions.DIV.Cons.cHalf
      linarith
    have a1 := mul_le_mul_of_nonneg_left hlf hD
    have a2 := mul_le_mul_of_nonneg_right hch hlq
    have a3 := mul_le_mul_of_nonneg_right hch hld
    rw [hlog, hc2]
    nlinarith
  · intro a b c
    have hQ0 : 0 < D.host.QS := D.host.QS_pos
    refine ⟨?_, ?_⟩
    · unfold pPow
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · unfold pPow
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]

end GlobalTheory.RunIn
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem normaliser_factor_mul_bar {D : D7} (EX : ErrX D) (i : Fin 2) :
    EX.piG i * piBarO EX i = ((D.host.g i : ℕ) : 𝓞 D.host.E) := by
  apply NumberField.RingOfIntegers.ext
  simpa [piBarO, NumberField.RingOfIntegers.mapRingHom_apply] using EX.piG_norm i

theorem map_piBar_eq_conj {D : D7} (EX : ErrX D) (i : Fin 2) (ρ : 𝓞 D.host.E →+* ℂ)
    (hρ : Function.Injective ρ) : ρ (piBarO EX i) = starRingEnd ℂ (ρ (EX.piG i)) := by
  let ψ : D.host.E →+* ℂ := IsFractionRing.lift hρ
  have hψ : ∀ x : 𝓞 D.host.E, ψ (x : D.host.E) = ρ x := fun x => IsFractionRing.lift_algebraMap hρ x
  rw [← hψ (piBarO EX i), ← hψ (EX.piG i), piBarO, NumberField.RingOfIntegers.mapRingHom_apply]
  exact D.host.toHostAx.conjE_apply ψ _

theorem log_norm_normaliser : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ), nnW B hinj EX w ≠ 0 ∧ Real.log ‖σ (nnW B hinj EX w : B.KO)‖ = (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
  intro D B hinj EX j w σ
  set ρ : 𝓞 D.host.E →+* ℂ := σ.comp ((algebraMap (𝓞 B.KO) B.KO).comp (iE D hinj B)) with hρdef
  have hρ : Function.Injective ρ :=
    σ.injective.comp ((IsFractionRing.injective (𝓞 B.KO) B.KO).comp (iE_injective D hinj B))
  have hg : ∀ i : Fin 2, (0 : ℝ) < (D.host.g i : ℝ) := fun i => by
    exact_mod_cast (D.host.g_prime i).pos
  have hval : σ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) =
      ∏ i : Fin 2, ρ (EX.piG i ^ Dplus w * piBarO EX i ^ Dminus w) := by
    simp [nnW, hρdef, map_prod, map_mul, map_pow]
  have hnorm : ‖σ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO)‖ =
      ∏ i : Fin 2, (D.host.g i : ℝ) ^ (((Dplus w : ℝ) + Dminus w) / 2) := by
    rw [hval, norm_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact norm_map_pow_mul_pow_of_mul_conj ρ _ _ _ (normaliser_factor_mul_bar EX i)
      (map_piBar_eq_conj EX i ρ hρ) _ _
  have hDF : WeightAlgebra.DF w = Dplus w + Dminus w := by
    simp only [WeightAlgebra.DF, WeightAlgebra.degP, Dplus, Dminus, Finset.sum_add_distrib]
  have h0 := Real.rpow_pos_of_pos (hg 0) (((Dplus w : ℝ) + Dminus w) / 2)
  have h1 := Real.rpow_pos_of_pos (hg 1) (((Dplus w : ℝ) + Dminus w) / 2)
  refine ⟨fun hz => ?_, ?_⟩
  · have hz' : ‖σ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO)‖ = 0 := by rw [hz]; simp
    rw [hnorm, Fin.prod_univ_two] at hz'
    nlinarith [mul_pos h0 h1]
  · rw [hnorm, Fin.prod_univ_two, Real.log_mul h0.ne' h1.ne', Real.log_rpow (hg 0), Real.log_rpow (hg 1),
      Real.log_mul (hg 0).ne' (hg 1).ne', hDF]
    push_cast
    ring

end GlobalTheory
end
