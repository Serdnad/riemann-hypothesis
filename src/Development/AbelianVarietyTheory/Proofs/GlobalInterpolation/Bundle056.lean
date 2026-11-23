module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle007
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle006
public import Formalism.LocalToGlobal.GlobalTheory.GL3.Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle227
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle001
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.LatOfDiscrHolds
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.UniqInvHolds
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOfThetaHeisenbergTranslates
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle059
public import Formalism.LocalToGlobal.Columns.ScaledRamifiedLattice
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
public import Mathlib.Analysis.Analytic.Order
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle043
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle055
public import Formalism.SharpRestriction.ParConsts
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
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
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
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.UniqInvOfLat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

abbrev cj : ℂ →+ ℂ := (starRingEnd ℂ).toAddMonoidHom

theorem cj_apply (z : ℂ) : cj z = starRingEnd ℂ z := rfl

theorem map_cj_map_cj (Λ : AddSubgroup ℂ) : (Λ.map cj).map cj = Λ := by
  rw [AddSubgroup.map_map]
  have : cj.comp cj = AddMonoidHom.id ℂ := by ext z; simp [cj_apply]
  rw [this, AddSubgroup.map_id]

theorem eisG_map_cj (Λ : AddSubgroup ℂ) (k : ℕ) :
    eisG (Λ.map cj) k = starRingEnd ℂ (eisG Λ k) := by
  unfold eisG
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ Λ.map cj ∧ w ≠ 0} :=
    { toFun := fun w => ⟨starRingEnd ℂ w.1, ⟨w.1, w.2.1, rfl⟩, by simpa using w.2.2⟩
      invFun := fun w => ⟨starRingEnd ℂ w.1, by
          obtain ⟨v, hv, hv'⟩ := AddSubgroup.mem_map.1 w.2.1
          have : starRingEnd ℂ w.1 = v := by rw [← hv']; simp [cj_apply]
          rw [this]; exact hv, by simpa using w.2.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  rw [← e.tsum_eq, Complex.conj_tsum]
  congr 1
  ext w
  show (1 : ℂ) / (starRingEnd ℂ (w : ℂ)) ^ (2 * k) = starRingEnd ℂ (1 / (w : ℂ) ^ (2 * k))
  simp [map_div₀, map_pow]

theorem eisenstein_g_two_map_conj (Λ : AddSubgroup ℂ) : g2 (Λ.map cj) = starRingEnd ℂ (g2 Λ) := by
  unfold g2; rw [eisG_map_cj, map_mul, map_ofNat]

theorem eisenstein_g_three_map_conj (Λ : AddSubgroup ℂ) : g3 (Λ.map cj) = starRingEnd ℂ (g3 Λ) := by
  unfold g3; rw [eisG_map_cj, map_mul, map_ofNat]

theorem discr_map_cj (Λ : AddSubgroup ℂ) :
    Formalism.MainNotions.TaylorLogMetric.discr (Λ.map cj) = starRingEnd ℂ (Formalism.MainNotions.TaylorLogMetric.discr Λ) := by
  unfold Formalism.MainNotions.TaylorLogMetric.discr; rw [eisenstein_g_two_map_conj, eisenstein_g_three_map_conj, map_sub, map_mul, map_pow, map_pow, map_ofNat]

theorem lamConj_spec (hU : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization) (M : IntermediateField ℚ ℂ)
    (ρ : M →ₐ[ℚ] ℂ) (Λ : AddSubgroup ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) (h1 : Formalism.MainNotions.TaylorLogMetric.discr Λ = 1) :
    g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩ ∧ g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩ ∧
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ Λ) = 1 := by
  have hl2 : liftM M (g2 Λ) = ⟨g2 Λ, h2⟩ := dif_pos h2
  have hl3 : liftM M (g3 Λ) = ⟨g3 Λ, h3⟩ := dif_pos h3
  have hdM : (⟨g2 Λ, h2⟩ : M) ^ 3 - 27 * (⟨g3 Λ, h3⟩ : M) ^ 2 = 1 := by
    apply M.val.injective
    rw [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one]
    exact h1
  have hab : (ρ ⟨g2 Λ, h2⟩) ^ 3 - 27 * (ρ ⟨g3 Λ, h3⟩) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hdM, map_one]
  obtain ⟨Λ', -, h2', h3'⟩ := (hU _ _ (by rw [hab]; exact one_ne_zero)).1
  have hex : ∃ Λ' : AddSubgroup ℂ, g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)) :=
    ⟨Λ', by rw [hl2]; exact h2', by rw [hl3]; exact h3'⟩
  have hs := Classical.epsilon_spec hex
  have e2 : g2 (lamConj M ρ Λ) = ρ ⟨g2 Λ, h2⟩ := hs.1.trans (by rw [hl2])
  have e3 : g3 (lamConj M ρ Λ) = ρ ⟨g3 Λ, h3⟩ := hs.2.trans (by rw [hl3])
  refine ⟨e2, e3, ?_⟩
  show g2 _ ^ 3 - 27 * g3 _ ^ 2 = 1
  rw [e2, e3, hab]

def conjO (D : D7) : 𝓞 D.host.K ≃+* 𝓞 D.host.K :=
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  RingOfIntegers.mapRingEquiv
    ((AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K ≃ₐ[ℚ] D.host.K) : D.host.K ≃+* D.host.K)

theorem phi_conjO (D : D7) (a : 𝓞 D.host.K) :
    D.host.φ₀ (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) =
      starRingEnd ℂ (D.host.φ₀ ((a : D.host.K) : D.host.E)) := by
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  have h : (((conjO D a : 𝓞 D.host.K) : D.host.K) : D.host.E) = D.host.conj ((a : D.host.K) : D.host.E) := by
    rw [conjO, RingOfIntegers.mapRingEquiv_apply]
    exact AlgEquiv.restrictNormal_commutes D.host.conj D.host.K (a : D.host.K)
  rw [h]
  exact D.host.toHostAx.conjE_apply _ _

theorem lamOf_map_cj (D : D7) (c : Ideal (𝓞 D.host.K)) (x : ℂ) :
    (lamOf D c x).map cj = lamOf D (c.map (conjO D)) (starRingEnd ℂ x) := by
  unfold lamOf
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨conjO D a, Ideal.mem_map_of_mem _ ha, ?_⟩
    rw [phi_conjO, cj_apply, map_mul]
  · rintro ⟨b, hb, rfl⟩
    rw [Ideal.mem_map_of_equiv] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact ⟨_, ⟨a, ha, rfl⟩, by rw [phi_conjO, cj_apply, map_mul]⟩

end GlobalTheory.ConjLattice

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem containsData {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {M : IntermediateField ℚ ℂ}
    (h : DataIn D (tor0 D cc δ) M) : EquidistributedConjugates.ContainsData D M (lamOf D cc δ) := by
  refine ⟨fun x => ?_, h.2.1, h.2.2⟩
  have := h.1 (D.eTau.symm 1) (x : D.host.E)
  rwa [show (tor0 D cc δ).emb (D.eTau.symm 1) (x : D.host.E) = embT D (D.eTau.symm 1) (x : D.host.E) from rfl,
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_K D _ _ x.2] at this

theorem conj_lattice : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization →
    EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x := by
  intro hU hCE _ D cc δ M _ t hS ρ
  obtain ⟨hcc, hδ, hM, -⟩ := hS
  have h1 : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have h2 : g2 (lamOf D cc δ) ∈ M := hM.2.1
  have h3 : g3 (lamOf D cc δ) ∈ M := hM.2.2
  have hsp := fun ρ' => lamConj_spec hU M ρ' (lamOf D cc δ) h2 h3 h1
  refine ⟨(hsp ρ).2.2, ?_⟩
  obtain ⟨⟨c, hcH, -⟩, hC2, -⟩ := hCE D cc δ hcc hδ M (containsData hM)
  by_cases hρ : EquidistributedConjugates.FixesK D M ρ
  · obtain ⟨x, hx, hxe⟩ := hcH ⟨ρ, hρ⟩
    exact ⟨_, nonZeroDivisors.coe_ne_zero _, x, hx, hxe⟩
  · obtain ⟨hρ', -⟩ := hC2 ρ hρ
    obtain ⟨x, hx, hxe⟩ := hcH ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩
    have hUI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.UniqInv :=
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqInv_of_lat Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds hU
    have hmap : (lamConj M ρ (lamOf D cc δ)).map cj = lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ) := by
      apply hUI
      · rw [discr_map_cj, (hsp ρ).2.2, map_one]; exact one_ne_zero
      · rw [eisenstein_g_two_map_conj, (hsp ρ).1, (hsp _).1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
      · rw [eisenstein_g_three_map_conj, (hsp ρ).2.1, (hsp _).2.1]; exact (EquidistributedConjugates.conjEmb_apply _ _ _).symm
    have hback : lamConj M ρ (lamOf D cc δ) = (lamConj M (EquidistributedConjugates.conjEmb M ρ) (lamOf D cc δ)).map cj := by
      rw [← hmap, map_cj_map_cj]
    refine ⟨(c ⟨EquidistributedConjugates.conjEmb M ρ, hρ'⟩ : Ideal (𝓞 D.host.K)).map (conjO D), ?_, starRingEnd ℂ x,
      (map_ne_zero _).2 hx, by rw [hback, hxe, lamOf_map_cj]⟩
    intro hbot
    rw [Ideal.map_eq_bot_iff_of_injective (conjO D).injective] at hbot
    exact nonZeroDivisors.coe_ne_zero _ hbot

end GlobalTheory.ConjLattice

namespace GlobalTheory.ConjLattice

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem uniformization_holds : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.Uniformization := by
  intro a b h
  refine ⟨?_, fun Λ Λ' hΛ hΛ' h2 h3 h2' h3' =>
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.uniqLat_holds Λ Λ' hΛ hΛ' (h2.trans h2'.symm) (h3.trans h3'.symm)⟩
  obtain ⟨L, h2, h3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants h
  obtain ⟨e2, e3, hΔ, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)
  exact ⟨_, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.latOfDiscr_holds _ hΔ, e2.trans h2, e3.trans h3⟩

theorem conj_lattice_holds : EquidistributedConjugates.ConjugatesEquidistributed → PeriodLatticeAgreement.LatticePeriodEta →
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∀ ρ : M →ₐ[ℚ] ℂ,
      discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧ ∃ c : Ideal (𝓞 D.host.K), c ≠ ⊥ ∧ ∃ x : ℂ, x ≠ 0 ∧
        lamConj M ρ (lamOf D cc δ) = lamOf D c x :=
  conj_lattice uniformization_holds

end GlobalTheory.ConjLattice
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.eq_of_theta_heisenbergTranslates : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → ∀ G G' : (Fin N → AF F) → ℂ, Decay G → Decay G' → (∀ x y, th (rho ψ a x y G) = th (rho ψ a x y G')) → G = G' := by
  first | exact @GlobalTheory.SWQ.eq_of_theta_rho | exact GlobalTheory.SWQ.eq_of_theta_rho | (intros; apply GlobalTheory.SWQ.eq_of_theta_rho <;> assumption)
end

section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

namespace GlobalTheory.MomN

theorem measure_eq_of_moments : ∀ (q : ℕ) [Fact q.Prime] (κ : Type) [Fintype κ]
    (μ μ' : C(κ → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]),
    (∀ (k : ℕ) (j : Fin k → κ) (f : C(κ → ℤ_[q], ℂ_[q])),
      (∀ a, f a = ∏ l, zc (a (j l))) → μ f = μ' f) → μ = μ' := by
  intro q _ κ _ μ μ' h
  let e := Fintype.equivFin κ
  let π : C(κ → ℤ_[q], Fin (Fintype.card κ) → ℤ_[q]) :=
    ⟨fun b i => b (e.symm i), by fun_prop⟩
  let π' : C(Fin (Fintype.card κ) → ℤ_[q], κ → ℤ_[q]) :=
    ⟨fun a i => a (e i), by fun_prop⟩
  let Φ : C(Fin (Fintype.card κ) → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] C(κ → ℤ_[q], ℂ_[q]) :=
    { toFun := fun G => G.comp π
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := ContinuousMap.continuous_precomp π }
  have hz : (μ - μ').comp Φ = 0 := by
    exact GlobalTheory.MonomialDense.eq_zero_of_monomials q _ _ fun m k g hg => by
      have := h m (fun l => e.symm (k l)) (Φ g) fun b => hg (π b)
      simp [this]
  ext F
  have hF : Φ (F.comp π') = F := by
    ext b
    change F (π' (π b)) = F b
    congr 1
    funext i
    simp [π, π']
  have := congrArg (fun ν => ν (F.comp π')) hz
  simp only [ContinuousLinearMap.comp_apply, hF, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply] at this
  exact sub_eq_zero.mp this

end GlobalTheory.MomN
end

section

open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory

theorem liesOver_span_of_natCast_mem_heightOne {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (P : HeightOneSpectrum (𝓞 E)) (h : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal) :
    P.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := by
    have : Fact p.Prime := ⟨hp⟩
    exact Int.ideal_span_isMaximal_of_prime p
  refine ⟨hmax.eq_of_le (Ideal.comap_ne_top _ P.isPrime.ne_top) ?_⟩
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact h

theorem exists_comap_eq_or_eq_conj :
    ∀ (X : Fields), X.AbelianUnramifiedExtensionConditions → ∀ (p : ℕ), p.Prime → ∀ (w : HeightOneSpectrum (𝓞 X.K)) (P : HeightOneSpectrum (𝓞 X.E)),
      ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal → ((p : ℕ) : 𝓞 X.E) ∈ P.asIdeal → ∃ τ : X.Tau, SeesP w τ P ∨ SeesPbar w τ P := by
  intro X hX p hp w P hw hP
  have := hX.galE
  obtain ⟨τ₀⟩ : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.ok.f_pos
  have h0 : ((p : ℕ) : 𝓞 X.E) ∈ (pullW τ₀ w).asIdeal := by
    change ((p : ℕ) : 𝓞 X.E) ∈ w.asIdeal.comap (X.embO τ₀)
    rw [Ideal.mem_comap, map_natCast]
    exact hw
  obtain ⟨g, hg⟩ := Ideal.exists_comap_galRestrict_eq ℤ ℚ X.E (𝓞 X.E) (p := Ideal.span {(p : ℤ)})
    (P₁ := (pullW τ₀ w).asIdeal) (P₂ := P.asIdeal)
    ⟨(pullW τ₀ w).isPrime, liesOver_span_of_natCast_mem_heightOne hp _ h0⟩
    ⟨P.isPrime, liesOver_span_of_natCast_mem_heightOne hp _ hP⟩
  have key : ∀ x : 𝓞 X.E, x ∈ P.asIdeal ↔ X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g x) ∈ w.asIdeal := by
    intro x
    rw [← hg]
    rfl
  have hc : ∀ x : 𝓞 X.E, ((X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g x) : 𝓞 X.K) : X.K) = X.emb τ₀ (g (x : X.E)) := by
    intro x
    exact congrArg (X.emb τ₀) (algebraMap_galRestrict_apply ℤ g x)
  obtain ⟨τ, hτ | hτ⟩ := hX.ok.emb_all ((X.emb τ₀).comp (g : X.E →+* X.E))
  · refine ⟨τ, Or.inl ?_⟩
    apply HeightOneSpectrum.ext
    ext x
    rw [key]
    have : X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g x) = X.embO τ x := by
      apply RingOfIntegers.ext
      rw [hc]
      exact RingHom.congr_fun hτ (x : X.E)
    rw [this]
    rfl
  · refine ⟨τ, Or.inr ?_⟩
    apply HeightOneSpectrum.ext
    ext x
    rw [mem_conjP, key]
    have : X.embO τ₀ (galRestrict ℤ ℚ X.E (𝓞 X.E) g (cO X.E x)) = X.embO τ (cO X.E (cO X.E x)) := by
      apply RingOfIntegers.ext
      rw [hc]
      exact RingHom.congr_fun hτ ((cO X.E x : 𝓞 X.E) : X.E)
    rw [this, cO_cO]
    rfl

end GlobalTheory
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

theorem _root_.GlobalTheory.T.relativeDeterminant_isometry_norm_one : ∀ (D : D7) (γ₀ γ : IsoK D), ((γ.detRel γ₀ : D.host.K) : D.host.E) * D.host.conj ((γ.detRel γ₀ : D.host.K) : D.host.E) = 1 := by
  first | exact @GlobalTheory.detRel_mul_conj_eq_one | exact GlobalTheory.detRel_mul_conj_eq_one | (intros; apply GlobalTheory.detRel_mul_conj_eq_one <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.algebraicDirection_scaled_embedding : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsCurveIdeal D cc → admitted D N N' L L' → δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → ∀ y : Matrix (Fin N') (Fin N) D.host.E, S.AlgDir ((δ₀ / δ) • e (δ • embV D B.tor y)) := by
  first | exact @GlobalTheory.AlgDirMom.algDir_smul_embV | exact GlobalTheory.AlgDirMom.algDir_smul_embV | (intros; apply GlobalTheory.AlgDirMom.algDir_smul_embV <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.pairing_scaledDirections_eq_period_pairing : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[p]), δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → Nat.Coprime (Ideal.absNorm cc) p → (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) → JMB.pairD lam Ω S.d S.Hm (fun i => e (δ • embV D B.tor (b i))) ((δ₀ / δ) • e (δ • embV D B.tor y)) a = pairN D lam (Ω * (Ideal.absNorm cc : ℂ_[p]) * lamC lam (δ / δ₀)) b y a := by
  first | exact @GlobalTheory.MomFin.pairing_scaled | exact GlobalTheory.MomFin.pairing_scaled | (intros; apply GlobalTheory.MomFin.pairing_scaled <;> assumption)
end

section

open Complex DirichletCharacter Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ZerosNearOne

theorem density_and_regions : ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧
    (∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((∑ p ∈ T, analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C1 * Q ^ ((1 : ℝ) / 4)) ∧
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ, LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re → IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (LFunction χ) ρ = 1 ∧ ∀ ρ' : ℂ, LFunction χ ρ' = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3)) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.ZeroDensityMult.zero_density_mult
  obtain ⟨c, hc, H2, H3⟩ := GlobalTheory.ZeroFreeHalf.main GlobalTheory.LandauPageRegion.main
  exact ⟨C, c, hC, hc, H, H2, H3⟩

end GlobalTheory.ZerosNearOne
end

section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem scale_one_le_a (s : Scale) : 1 ≤ s.a := by
  have hx : 1 < s.x := s.one_lt_alt
  have hL : 0 ≤ s.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ s.b := by
    unfold Scale.b
    exact Real.one_le_exp hL
  unfold Scale.a
  exact one_le_mul_of_one_le_of_one_le hx.le hb

theorem famP_La_nonneg : ∀ (eps : ℝ) (Fm : FamP eps), ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x,
    0 ≤ (Fm.L x i).La := by
  intro eps Fm x hx i
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := Fm.sizes x hx i
  obtain ⟨-, -, -, -, -, -, hrd, -⟩ := hQD
  unfold SizeData₂.La
  exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (scale_one_le_a _) hrd)

end GlobalTheory
end
