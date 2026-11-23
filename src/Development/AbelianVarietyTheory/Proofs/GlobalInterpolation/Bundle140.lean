module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle133
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle130
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle073
public import Development.AutomorphicArithmetic.ShortNorms.Primes
public import Development.AutomorphicArithmetic.ShortNorms.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle063
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle060
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle013
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle137
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle110
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle105
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle138
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.DualIndexPow

theorem nIdx_eq_zpow : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (c : ℤ), (∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp c) → LocalAdditiveCharacterDual.nIdx F ψ v = (PlaceSplittingTypes.resCard F v : ℝ) ^ c := by
  intro F _ _ ψ v c h
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective F v
    (WithZero.exp (-c))
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact WithZero.exp_ne_zero ha.symm
  have hu : ∀ hx : WithZero.exp (-c) ≠ 0, Multiplicative.toAdd (WithZero.unzero hx) = -c :=
    fun _ => rfl

  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.psiDual F ψ v = GlobalTheory.LocalDensityProduct.colonV v a := by
    ext t
    rw [GlobalTheory.LocalDensityProduct.mem_colonV]
    change (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1) ↔ _
    rw [h t, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, ha,
      WithZero.exp_neg, mul_inv_le_iff₀ (by simp), one_mul]
  have hi : GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.intV F v = GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex.intV F v := rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.nIdx
  rw [hd, hi, (GlobalTheory.LocalDensityProduct.index_colonV v a ha0).2,
    NumberField.FinitePlace.norm_def, ha,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.resCard]
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, WithZero.log_exp]
  simp [_root_.zpow_neg]

end GlobalTheory.DualIndexPow
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

theorem _root_.GlobalTheory.T.product_localDensities_adeleCharacter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ, IsCharAF F ψ → (∀ v, (intV F v).relIndex (dualV F ψ v) ≠ 0 ∧ (dualV F ψ v).relIndex (intV F v) ≠ 0) ∧ ∀ a : F, a ≠ 0 → IsScalingInf F ψ a → ∀ M : ℕ, 2 ≤ M → Summable (fun v => |localDensity F E ψ M v - 1|) ∧ ∃ P : ℝ, 0 < P ∧ HasProd (localDensity F E ψ M) P ∧ absInf F a ^ ((M : ℝ) - 1 / 2) * P = absDiscr F ^ ((1 : ℝ) / 2 - M) / Formalism.HermitianLatticesTheory.lValEta E M := by
  first | exact @GlobalTheory.LocalDensityProduct.density_product | exact GlobalTheory.LocalDensityProduct.density_product | (intros; apply GlobalTheory.LocalDensityProduct.density_product <;> assumption)
end

section

namespace GlobalTheory.UnfoldingObj

theorem unfolding : ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.LatticeTensorUnfolding.Unfolding D := fun D =>
  (GlobalTheory.UnfoldingCompare.unfolding_iff D).1 (GlobalTheory.T.unitaryUnfolding_volume_vectorStabilizer GlobalTheory.T.quotientMeasure_integration_formulas_unimodular GlobalTheory.T.adelicUnitaryGroupHaarProperties_proof GlobalTheory.T.stabSelfDualLattice_transitive_on_length D)

end GlobalTheory.UnfoldingObj
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem normOne_pair_form {d M p : ℕ} (h : GlobalTheory.Mem.An.NormOne d M p) : GlobalTheory.EX.NormOne d M p := by
  obtain ⟨A, B, h1, h2, h3⟩ := h
  exact ⟨(A, B), h1, h2, h3⟩

theorem normPrimes_unconditional : NormPrimes := by
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := UpperTheory.T3.normPrimesN UpperTheory.T3.shortNorm eps he0
  refine ⟨x0, fun s R N d hs hx hR hq => ?_⟩
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hb : 0 < s.b := Real.exp_pos _
  have hY : 0 < ((R.k : ℝ) * s.b) ^ 8 := by positivity
  have hlog : 8 * s.x ^ eps ≤ Real.log (((R.k : ℝ) * s.b) ^ 8) := by
    rw [Real.log_pow, Real.log_mul (by linarith) hb.ne']
    have h1 : Real.log s.b = s.x ^ eps := by
      rw [← hs]; exact Real.log_exp _
    have h2 := Real.log_nonneg hk
    push_cast
    linarith
  refine (hx0 s.x hx N d (hs ▸ hq) _ hY hlog).trans ?_
  refine Nat.cast_le.mpr (Finset.card_le_card fun g hg => ?_)
  simp only [GlobalTheory.Mem.An.normPrimes, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hg ⊢
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hg
  exact ⟨Nat.lt_succ_of_le h2, h3, (Nat.lt_of_floor_lt h1).le, normOne_pair_form h4⟩

theorem levelPrime_unconditional : LevelPrime := by
  intro eps c he0 he1 hc
  obtain ⟨x0, hx0⟩ := UpperTheory.T3.levelPrimeN UpperTheory.T3.shortNorm eps he0 he1 c 9 hc (by norm_num)
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps he0 he1
  refine ⟨max x0 x1, fun s R N d g0 g1 Ts hs hx hR hq hg0 hg1 hb0 hb1 hTs hlog => ?_⟩
  obtain ⟨hf, -, hr, hkr, -, -, -, -, -, -, -, -, -, -, -, hm, -⟩ :=
    hx1 s R hs (le_trans (le_max_right _ _) hx) hR
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hn : 1 ≤ R.n := R.toFrame.ord_pos
  have hk : (1 : ℝ) ≤ R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ R.k)
  have hf1 : (1 : ℝ) ≤ R.f := by
    exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ R.f)
  have hL : s.L = s.x ^ eps := by rw [← hs]; rfl
  have hg : ∀ g : ℕ, 1 ≤ g → (g : ℝ) ≤ s.b ^ 9 → Real.log g ≤ 9 * s.x ^ eps := by
    intro g h1 h2
    have h3 : (0 : ℝ) < g := by exact_mod_cast h1
    refine (Real.log_le_log h3 h2).trans (le_of_eq ?_)
    rw [Real.log_pow, Scale.b, Real.log_exp, hL]
    norm_num
  have hm' : s.x ^ ((1 : ℝ) / 3) ≤ (R.m : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [hs]; linarith)).trans hm
  have hW1 : (1 : ℝ) ≤ (R.f : ℝ) * R.k := one_le_mul_of_one_le_of_one_le hf1 hk
  have hW2 : (R.f : ℝ) * R.k ≤ s.x ^ (12 : ℝ) := by
    have hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := (Nat.cast_le.mpr hkr).trans hr
    exact (rank_mul_le hxp (by linarith) hf hk5).trans
      (Real.rpow_le_rpow_of_exponent_le hx1'.le (by norm_num))
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := hx0 s.x (le_trans (le_max_left _ _) hx) N d g0 g1 R.m (hs ▸ hq)
    hg0 hg1 (hg g0 hg0 hb0) (hg g1 hg1 hb1) hm' _ Ts hW1 hW2 hTs (hL ▸ hlog)
  exact ⟨T, hT1, hT2.le, hT3, normOne_pair_form hT4⟩

theorem normPrimes_and_levelPrime_unconditional : NormPrimes ∧ LevelPrime :=
  ⟨normPrimes_unconditional, levelPrime_unconditional⟩

end GlobalTheory.EX
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_archimedean_exponents_adeleCharacter : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∃ lam, IsLam ψ lam := by
  first | exact @GlobalTheory.SWQ.exists_isLam | exact GlobalTheory.SWQ.exists_isLam | (intros; apply GlobalTheory.SWQ.exists_isLam <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.finiteAdeleVector_annihilators_compact_open_basis : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (AF F) ℂ) (lam : InfinitePlace F → ℝ) (ν : Measure (AF F)) (a : Fin N → F), Ctx ψ lam ν a → (∀ L : AddSubgroup (Fin N → Af F), IsOpen (L : Set (Fin N → Af F)) → IsCompact {u : Fin N → Af F | ∀ y ∈ L, ψ (pairA F 0 (Bd (Af F) a u y)) = 1}) ∧ (∀ K : Set (Fin N → Af F), IsCompact K → {y : Fin N → Af F | ∀ u ∈ K, ψ (pairA F 0 (Bd (Af F) a u y)) = 1} ∈ 𝓝 0) ∧ ∀ U ∈ 𝓝 (0 : Fin N → Af F), ∃ L : AddSubgroup (Af F), IsOpen (L : Set (Af F)) ∧ IsCompact (L : Set (Af F)) ∧ ∀ u : Fin N → Af F, (∀ l, u l ∈ L) → u ∈ U := by
  first | exact @GlobalTheory.SWQ.finite_annihilators | exact GlobalTheory.SWQ.finite_annihilators | (intros; apply GlobalTheory.SWQ.finite_annihilators <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NegVol

open Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold

variable {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') {Γ K : Subgroup G} {Γ' K' : Subgroup G'}
  (hΓ : ∀ h, h ∈ Γ ↔ φ h ∈ Γ') (hK : ∀ h, h ∈ K ↔ φ h ∈ K')

def stabEquiv (g' : G') : stab Γ K (φ.symm g') ≃ stab Γ' K' g' where
  toFun γ := ⟨⟨φ γ.1, (hΓ _).mp γ.1.2⟩, by
    have h := (hK _).mp γ.2
    simp only [stab, Set.mem_setOf_eq] at h ⊢
    simpa [map_mul, map_inv] using h⟩
  invFun γ := ⟨⟨φ.symm γ.1, (hΓ _).mpr (by simpa using γ.1.2)⟩, by
    have h := γ.2
    simp only [stab, Set.mem_setOf_eq] at h ⊢
    rw [hK]
    simpa [map_mul, map_inv] using h⟩
  left_inv γ := by ext; simp
  right_inv γ := by ext; simp

include hΓ hK in
theorem transport {ι : Type*} (g' : ι → G')
    (hcov : ∀ x : G', ∃ i, ∃ γ : Γ', ∃ k : K', x = (γ : G') * g' i * k)
    (hdisj : ∀ i j (γ γ' : Γ') (k k' : K'), (γ : G') * g' i * k = (γ' : G') * g' j * k' → i = j)
    (hfin : ∀ i, (stab Γ' K' (g' i)).Finite) :
    (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * φ.symm (g' i) * k) ∧
    (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * φ.symm (g' i) * k = (γ' : G) * φ.symm (g' j) * k' → i = j) ∧
    (∀ i, (stab Γ K (φ.symm (g' i))).Finite) ∧
    (∀ i, Nat.card (stab Γ K (φ.symm (g' i))) = Nat.card (stab Γ' K' (g' i))) := by
  refine ⟨fun x => ?_, fun i j γ γ' k k' h => ?_, fun i => ?_, fun i => Nat.card_congr (stabEquiv φ hΓ hK (g' i))⟩
  · obtain ⟨i, γ, k, hx⟩ := hcov (φ x)
    refine ⟨i, ⟨φ.symm γ, (hΓ _).mpr (by simpa using γ.2)⟩, ⟨φ.symm k, (hK _).mpr (by simpa using k.2)⟩, ?_⟩
    apply φ.injective
    simp [map_mul, hx]
  · refine hdisj i j ⟨φ γ, (hΓ _).mp γ.2⟩ ⟨φ γ', (hΓ _).mp γ'.2⟩ ⟨φ k, (hK _).mp k.2⟩ ⟨φ k', (hK _).mp k'.2⟩ ?_
    have := congrArg φ h
    simpa [map_mul] using this
  · have := (hfin i).to_subtype
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (stabEquiv φ hΓ hK (g' i)).symm)

end GlobalTheory.NegVol

namespace GlobalTheory.NegVol

theorem vol_neg_eq : ∀ D : D7, VolTie D → ∀ (W : HSpace D.host.E) (n : ℕ), W.SigOK → (∀ τ, W.sig τ = (0, n)) →
    D.vol W = D.vol (GlobalTheory.NegSpace.neg W) := by
  intro D hT W n hW hsig
  set W' := GlobalTheory.NegSpace.neg W with hW'def
  have hW' : W'.SigOK := GlobalTheory.T.hermitianSpaceOppositeForm_signatureCondition _ W hW
  have hn : n = W.rank := by
    have := Formalism.BasicNotions.sig_sum W hW D.host.φ₀
    rw [hsig] at this; simpa using this
  have hsig' : ∀ τ, W'.sig τ = (W'.rank, 0) := by
    intro τ
    rw [GlobalTheory.NegSpace.neg_sig, hsig τ, GlobalTheory.NegSpace.neg_rank, ← hn]

  obtain ⟨⟨μ, hμ⟩, hall⟩ := hT W 0 n hW hsig
  obtain ⟨⟨𝓕, h𝓕⟩, hF⟩ := hall μ hμ
  obtain ⟨⟨μ', hμ'⟩, hall'⟩ := hT W' W'.rank 0 hW' hsig'
  obtain ⟨⟨𝓕', h𝓕'⟩, hF'⟩ := hall' μ' hμ'

  obtain ⟨φ, -, hΓ, hS⟩ := GlobalTheory.T.unitaryGroup_neg_form_compatible D.host.F D.host.E D.sp.cm.sig W.rank W.gram (-W.gram) rfl

  obtain ⟨m, g', hcov', hdisj', -⟩ := GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass D W' hW' hsig'
  have hfin' : ∀ i, (Unfold.stab (GamA D W') (StabFin.SFin D.sp.cm.sig W'.gram (L0c D W')) (g' i)).Finite :=
    fun i => StabFin.stab_finite W' D.sp.cm.sig (fun _ => rfl) (fun τ => D.sp.cm.cmUnram.2.1 τ) hW' hsig' _
      (fun k hk y hy => (hk y).mp hy) (g' i)
  obtain ⟨hcov, hdisj, hfin, hcard⟩ := transport φ.toMulEquiv
    (Γ := GamA D W) (K := StabFin.SFin D.sp.cm.sig W.gram (L0c D W))
    (Γ' := (GamA D W' : Subgroup (HA (AF D.host.F) D.sp.cm.sig (-W.gram))))
    (K' := (StabFin.SFin D.sp.cm.sig W'.gram (L0c D W') : Subgroup (HA (AF D.host.F) D.sp.cm.sig (-W.gram)))) hΓ (hS _) g' hcov' hdisj' hfin'

  have hK1 : μ (StabFin.SFin D.sp.cm.sig W.gram (L0c D W) : Set _) = 1 := GlobalTheory.T.negDefinite_selfDualStabilizer_volume_one D W n hW hsig μ hμ
  obtain ⟨θ, hθ⟩ := hμ'.2.1
  obtain ⟨A, hA⟩ := (hμ'.2.2 θ hθ).1
  have hK1' : μ' (StabFin.SFin D.sp.cm.sig W'.gram (L0c D W') : Set _) = 1 := by
    have hK : KSub D W' W'.rank 0 θ A = StabFin.SFin D.sp.cm.sig W'.gram (L0c D W') :=
      SetLike.coe_injective (StabFin.KSub_eq D W' hW' hsig' θ hθ A hA)
    rw [← hK]; exact measure_KSub D W' W'.rank μ' hμ' θ hθ A hA
  have := Unfold.borelHA D.sp.cm.sig W.gram
  have := Unfold.borelHA D.sp.cm.sig W'.gram
  haveI := hμ.1
  haveI := hμ'.1
  haveI := Unfold.measurableMulHA D.sp.cm.sig W.gram
  haveI := Unfold.measurableMulHA D.sp.cm.sig W'.gram
  haveI : Countable (GamA D W) := Unfold.countableGamma D.sp.cm.sig W.gram
  haveI : Countable (GamA D W') := Unfold.countableGamma D.sp.cm.sig W'.gram
  have e := Unfold.measure_fd_toReal μ (StabFin.isOpen_SFin W D.sp.cm.sig).measurableSet hK1 _ hcov hdisj hfin h𝓕
  have e' := Unfold.measure_fd_toReal μ' (StabFin.isOpen_SFin W' D.sp.cm.sig).measurableSet hK1' g' hcov' hdisj'
    hfin' h𝓕'
  rw [hF 𝓕 h𝓕, ENNReal.toReal_ofReal (D.vol_pos W).le] at e
  rw [hF' 𝓕' h𝓕', ENNReal.toReal_ofReal (D.vol_pos W').le] at e'
  rw [e, e']
  exact Finset.sum_congr rfl fun i _ => congrArg (fun k : ℕ => ((k : ℝ))⁻¹) (hcard i)

end GlobalTheory.NegVol
end

section

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (tops)

noncomputable section
namespace GlobalTheory.LvT.WtSign

theorem m_pos (R : Ranks) : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m

theorem k_pred_lt (R : Ranks) : R.k - 1 < R.k := by have := R.m_add_three_le_k; omega

def uLast {R : Ranks} (P : HCParam R) : ℚ := P.u ⟨R.k - 1, k_pred_lt R⟩

def eFirst {R : Ranks} (P : HCParam R) : ℚ := P.e ⟨0, m_pos R⟩

def SignLaw {R : Ranks} {ι : Type} (hc : ι → HCParam R) (top : ι → Prop) : Prop :=
  (∀ τ, top τ → uLast (hc τ) ≤ -(((R.k : ℚ) - 1) / 2)) ∧ ∀ τ, (R.k : ℚ) / 2 ≤ eFirst (hc τ)

theorem e_ge {R : Ranks} (P : HCParam R) (i : ℕ) (hi : i < R.m) :
    eFirst P + (i : ℚ) * ((R.t : ℚ) + 3) ≤ P.e ⟨i, hi⟩ := by
  induction i with
  | zero => simp [eFirst]
  | succ i ih =>
    have h1 := ih (by omega)
    have h2 := P.gap_eb ⟨i, by omega⟩ hi
    have h3 := P.gap_be ⟨i + 1, hi⟩
    push_cast
    simp only at h2
    linarith

theorem sExp_nonneg {R : Ranks} (P : HCParam R) (h : (R.k : ℚ) / 2 ≤ eFirst P) (i : ℕ) (hi : i < R.m) :
    0 ≤ sExp R (P.e ⟨i, hi⟩) (i + 1) := by
  have h1 := e_ge P i hi
  have h2 : (0 : ℚ) ≤ (i : ℚ) * (R.t : ℚ) := by positivity
  have h3 : (0 : ℚ) ≤ (i : ℚ) := by positivity
  simp only [sExp, Ranks.N, Nat.add_sub_cancel]
  push_cast
  nlinarith

theorem eFirst_ge_of_uLast_le {R : Ranks} (P : HCParam R) (h : uLast P ≤ -(((R.k : ℚ) - 1) / 2)) :
    (R.k : ℚ) / 2 ≤ eFirst P := by
  have h1 := P.u_last_gt (by have := k_pred_lt R; omega) (m_pos R)
  have h2 := P.gap_be ⟨0, m_pos R⟩
  have h3 : (0 : ℚ) ≤ R.t := by positivity
  unfold uLast at h
  unfold eFirst
  linarith

theorem eFirst_ge_of_uLast_nonpos {R : Ranks} (P : HCParam R) (h : uLast P ≤ 0) : (R.k : ℚ) / 2 ≤ eFirst P := by
  have h1 := P.u_last_gt (by have := k_pred_lt R; omega) (m_pos R)
  have h2 := P.gap_be ⟨0, m_pos R⟩
  have h5 : (R.k : ℚ) ≤ R.t := by
    have := R.rank_add_five_le
    exact_mod_cast (by omega : R.k ≤ R.t)
  unfold uLast at h
  unfold eFirst
  linarith

variable {D : D7} {u : D.what₂.Word}

theorem bTop_cast (X : Ch D u) (τ : D.what₂.Tau) :
    (X.fm.bTop τ : ℚ) = -uLast (D.hc τ) - ((D.R.k : ℚ) - 1) / 2 := by
  have hk := k_pred_lt D.R
  have hN : D.R.N 0 = D.R.k := by simp [Ranks.N]
  have h := X.fm.lam_eq 0 (Nat.zero_le _) τ ⟨D.R.N 0 - 1, by omega⟩
  rw [dite_eq_left (show D.R.N 0 - 1 < D.R.k by omega)] at h
  have e : (⟨D.R.N 0 - 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, hk⟩ := Fin.ext (by simp only; omega)
  simp only [e, hcToWeightQ, rhoVec] at h
  rw [D.hcW_last u τ (by omega), Nat.cast_sub (by omega)] at h
  unfold MemberForms.bTop DomWeight.detShift uLast
  rw [dite_eq_left (D.R.N_pos 0)]
  push_cast at h ⊢
  rw [h, show (D.R.N 0 : ℚ) = D.R.k by exact_mod_cast hN]
  ring

theorem sDiv_cast (X : Ch D u) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    (X.C.sDiv i τ : ℚ) = sExp D.R ((D.hc τ).e ⟨i, hi⟩) (i + 1) := by
  rw [X.C.sDiv_eq i hi τ, D.hcW_e]

theorem wtSigns_iff (X : Ch D u) : TwColumn.WtSigns X ↔ SignLaw D.hc (· ∈ tops D) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun τ hτ => ?_, fun τ => ?_⟩
    · have h : (0 : ℚ) ≤ (X.fm.bTop τ : ℚ) := by exact_mod_cast h1 τ hτ
      rw [bTop_cast] at h
      linarith
    · have h : (0 : ℚ) ≤ (X.C.sDiv 0 τ : ℚ) := by exact_mod_cast h2 0 (m_pos _) τ
      rw [sDiv_cast X 0 (m_pos _)] at h
      simp only [sExp, Ranks.N, Nat.add_sub_cancel, zero_mul, add_zero] at h
      unfold eFirst
      linarith
  · rintro ⟨h1, h2⟩
    refine ⟨fun τ hτ => ?_, fun i hi τ => ?_⟩
    · have h : (0 : ℚ) ≤ (X.fm.bTop τ : ℚ) := by
        rw [bTop_cast]
        linarith [h1 τ hτ]
      exact_mod_cast h
    · have h : (0 : ℚ) ≤ (X.C.sDiv i τ : ℚ) := by
        rw [sDiv_cast X i hi]
        exact sExp_nonneg _ (h2 τ) i hi
      exact_mod_cast h

theorem mem_tops (τ : D.what₂.Tau) : τ ∈ tops D ↔ (D.eTau τ : D.R.GG) ∈ D.host.topPlaces := by
  simp [tops, topsOf]

theorem b'_pos (s : Scale) : 0 < s.b' := by
  have := s.one_lt_alt
  unfold Scale.b' Scale.a Scale.b Scale.X'
  positivity

theorem uLast_le (L : SizeData₂ D) (τ : D.what₂.Tau) (hτ : τ ∈ tops D) :
    uLast (D.hc τ) ≤ -(((D.R.k : ℚ) - 1) / 2) := by
  have h1 := (mem_tops τ).1 hτ
  unfold Host.topPlaces at h1
  obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h1
  have h2 := (L.top_u τ ⟨t, ht⟩ (by have := k_pred_lt D.R; omega) e.symm).2
  have h3 := L.bT_ge ⟨t, ht⟩
  have h4 := b'_pos L.sc
  have h5 : ((uLast (D.hc τ) : ℚ) : ℝ) ≤ ((-(((D.R.k : ℚ) - 1) / 2) : ℚ) : ℝ) := by
    unfold uLast
    rw [h2]
    push_cast
    linarith
  exact_mod_cast h5

open GlobalTheory.Mem

def BaseSigns (B : Base) : Prop := SignLaw B.hc (· ∈ B.wts.tops)

theorem wtSigns_assemble_iff (B : Base) (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W)
    (N : NStage B C W) (G : GJStage B C) (u : B.Word) (X : Ch (assemble B C W V S N G) u) :
    TwColumn.WtSigns X ↔ BaseSigns B := by
  have e : ∀ τ, τ ∈ tops (assemble B C W V S N G) ↔ τ ∈ B.wts.tops := fun τ =>
    (mem_tops (D := assemble B C W V S N G) τ).trans (B.mem_wts_tops τ).symm
  exact (wtSigns_iff (D := assemble B C W V S N G) X).trans
    (and_congr (forall_congr' fun τ => imp_congr (e τ) Iff.rfl) Iff.rfl)


end GlobalTheory.LvT.WtSign
end
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassNumberMass

theorem classFin_and_classMass : ∀ D : D7, ClassFin D ∧ ClassMass D := by
  intro D
  refine ⟨fun W hW hsig => ?_, fun W hW hsig n g hcov hdisj => ?_⟩
  · obtain ⟨n, g, hcov, hdisj, _⟩ := GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass D W hW hsig
    exact ⟨n, g, hcov, hdisj⟩
  · obtain ⟨m, g', hcov', hdisj', hsum⟩ := GlobalTheory.T.lattice_stabilizer_doubleCosets_classRest_mass D W hW hsig
    rw [← hsum]
    exact GlobalTheory.WeightedDoubleCoset.sum_inv_card_stab_eq _ _ _ n m g g' hcov hdisj hcov' hdisj'

end GlobalTheory.ClassNumberMass
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

theorem _root_.GlobalTheory.T.movedVacuum_mem_thetaFunctions_and_moves : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (a b : ℕ), TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → (∀ L L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → Base.chiFac χ a b L L' ≠ 0 ∧ B.thMoved a b L L' ∈ Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L L')) ∧ (∀ L L' L'', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L' → StandardLatticesGL3.SD D L'' → B.thMoved a b L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved a b L L')) ∧ ∀ L L₁ L', StandardLatticesGL3.SD D L → StandardLatticesGL3.SD D L₁ → StandardLatticesGL3.SD D L' → B.thMoved a b L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved a b L L') := by
  first | exact @GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves | exact GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves | (intros; apply GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves <;> assumption)
end
