module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle115
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle215
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle309
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle303
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle226
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle297
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle230
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle227
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle003
import Mathlib.Algebra.AlgebraicCard
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.Bundle001
public import Formalism.LocalRingCardinality.Bundle001
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import ReciprocityTheory.SemistableReduction.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle254
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnramifiedOfIsCMUnram
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle117
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
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle116
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure

theorem _root_.GlobalTheory.T.isCountableDiscreteWithFundDomains_rationalVectorStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → IsDiscreteWithDomains (HstabFin (AF F) σ J x) := by
  first | exact @GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin | exact GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin | (intros; apply GlobalTheory.RationalStabiliserDomains.isDiscreteWithDomains_HstabFin <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

namespace GlobalTheory.AdelicCharDilate

theorem exists_eq_std_dilate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E →
    ∀ ψ₀, IsStdChar F ψ₀ → ∀ ψ, IsCharAF F ψ →
      ∃ a : F, a ≠ 0 ∧ ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x) := by
  intro F E _ _ _ _ _ _ σ hCM _ _ ψ₀ h₀ ψ h
  haveI := hCM.1
  exact GlobalTheory.T.exists_ne_zero_adele_char_eq_comp_mul_totally_real F ψ₀ ψ h₀.1 h

end GlobalTheory.AdelicCharDilate
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.HalfPeriodValue

open Formalism.MainNotions.StandardLatticesGL3 (wpF cj FixK rhoBar StarPt w0 InRationalLattice)

theorem wpF_add_of_mem {Λ : AddSubgroup ℂ} (h : GlobalTheory.ThetaConj.IsLat Λ) {z ω : ℂ} (hz : z ∉ Λ)
    (hω : ω ∈ Λ) : wpF Λ (z + ω) = wpF Λ z := by
  obtain ⟨L, hL⟩ := h.exists_periodPair
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  have hzω : z + ω ∉ Λ := fun hh => hz (by simpa using Λ.sub_mem hh hω)
  rw [(hd.2.2.2.2.1 _ hzω).1, (hd.2.2.2.2.1 _ hz).1]
  exact L.weierstrassP_add_coe z ⟨ω, (hL ω).1 hω⟩

theorem cmGenerator_mul_mem_curveLattice {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) :
    ∀ z ∈ lamOf D cc δ, w0 D * z ∈ lamOf D cc δ := by
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  rw [← ha]
  exact (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.2.2.2 a

theorem key_of_fix {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ ρ) {t t' : ℂ}
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t)
    (ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') :
    t' ∉ lamConj ⊤ ρ (lamOf D cc δ) ∧
      wpF (lamConj ⊤ ρ (lamOf D cc δ)) t' = cj ⊤ ρ (wpF (lamOf D cc δ) t) := by
  obtain ⟨hex, -, -, -, hmul, hord, -⟩ :=
    GlobalTheory.T.galStar_complexMultiplication_points D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨cc', δ', h', -, hL⟩ :=
    GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top 1 one_pos
  rw [GlobalTheory.ThetaConj.twoTorsionCMPoint_iff] at ht ht'
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have ha' : D.host.φ₀ ((((1 - a : 𝓞 D.host.K) : D.host.K) : D.host.E)) = 1 - w0 D := by
    rw [← ha]
    change D.host.φ₀ (algebraMap D.host.K D.host.E (algebraMap (𝓞 D.host.K) D.host.K (1 - a))) = _
    rw [map_sub, map_sub, map_sub, map_one, map_one, map_one]
    rfl
  have htn : t ∉ lamOf D cc δ := fun hh => ht.2.1 (cmGenerator_mul_mem_curveLattice h _ hh)
  obtain ⟨t'', ht''⟩ := hex t ⟨2, by norm_num, by exact_mod_cast ht.1⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  have e2 := (hord 2 _ _ ht'').1 (by exact_mod_cast ht.1)
  have ea := (hord 1 _ _ (hmul a _ _ ht'')).2
  have eb := (hord 1 _ _ (hmul (1 - a) _ _ ht'')).2
  rw [ha] at ea
  rw [ha'] at eb
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at e2 ea eb
  obtain ⟨k, hk⟩ := GlobalTheory.ThetaConj.weylMatrix_mul_apply D
  have hlat : GlobalTheory.ThetaConj.IsLat (lamConj ⊤ ρ (lamOf D cc δ)) := hL ▸ GlobalTheory.ThetaConj.isLat_lamOf h'
  have hdiff : t' - t'' ∈ lamConj ⊤ ρ (lamOf D cc δ) :=
    GlobalTheory.ThetaConj.two_torsion_unique hlat (w0 D) k hk ht'.1 ht'.2.1 ht'.2.2 e2
      (fun hh => ht.2.1 (ea hh)) (fun hh => ht.2.2 (eb hh)) (by rw [hL]; exact cmGenerator_mul_mem_curveLattice h')
  rcases ht'' with ⟨hin, -⟩ | ⟨-, hn'', -, -, hwp, -⟩
  · exact absurd hin htn
  · refine ⟨fun hh => hn'' (by simpa using (lamConj ⊤ ρ (lamOf D cc δ)).sub_mem hh hdiff), ?_⟩
    rw [← hwp, ← wpF_add_of_mem hlat hn'' hdiff, add_sub_cancel]

theorem wpF_conj (Λ : AddSubgroup ℂ) (z : ℂ) :
    wpF (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ z) = starRingEnd ℂ (wpF Λ z) := by
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃
      {w : ℂ // w ∈ Λ.map (starRingEnd ℂ).toAddMonoidHom ∧ w ≠ 0} :=
    { toFun := fun w => ⟨starRingEnd ℂ w, by rw [GlobalTheory.ThetaConj.mem_conj, Complex.conj_conj]; exact w.2.1,
        by simpa using w.2.2⟩
      invFun := fun w => ⟨starRingEnd ℂ w, GlobalTheory.ThetaConj.mem_conj.1 w.2.1, by simpa using w.2.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  unfold wpF
  rw [map_add (f := _), Complex.conj_tsum, ← e.tsum_eq]
  simp [e, map_sub]

theorem key_top {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) {t t' : ℂ}
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t)
    (ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') :
    t' ∉ lamConj ⊤ ρ (lamOf D cc δ) ∧
      wpF (lamConj ⊤ ρ (lamOf D cc δ)) t' = cj ⊤ ρ (wpF (lamOf D cc δ) t) := by
  obtain ⟨hK, hT, -⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ h ⊤ ρ
    ⟨fun _ _ => IntermediateField.mem_top, IntermediateField.mem_top, IntermediateField.mem_top⟩
  rcases hK with hK | hK
  · exact key_of_fix h ρ hK ht ht'
  · have hL : lamConj ⊤ (rhoBar ⊤ ρ) (lamOf D cc δ) =
        (lamConj ⊤ ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom := congrArg Tor.abelian₂ hT
    obtain ⟨hn, hw⟩ := key_of_fix h _ hK (t' := starRingEnd ℂ t') ht (hL ▸ GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht')
    rw [hL, wpF_conj, GlobalTheory.ThetaConj.cj_rhoBar] at hw
    rw [hL, GlobalTheory.ThetaConj.mem_conj, Complex.conj_conj] at hn
    exact ⟨hn, (starRingEnd ℂ).injective hw⟩

theorem halfPeriod_value : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
    ∃ e g : M, (g : ℂ) = g2 (lamOf D cc δ) ∧ lamConj M M.val (lamOf D cc δ) = lamOf D cc δ ∧
      ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧
        g2 (lamConj M ρ (lamOf D cc δ)) = ρ g ∧ t ρ ∉ lamConj M ρ (lamOf D cc δ) ∧
        Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) = ρ e := by
  intro D cc δ M _ t hS
  obtain ⟨hcc, hδ, hdata, ht⟩ := hS
  have h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hg2 : g2 (lamOf D cc δ) ∈ M := hdata.2.1
  have hg3 : g3 (lamOf D cc δ) ∈ M := hdata.2.2
  have hlat := GlobalTheory.ThetaConj.isLat_lamOf h
  have hdisc : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 :=
    (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.2.1
  have hself : lamConj M M.val (lamOf D cc δ) = lamOf D cc δ :=
    GlobalTheory.ThetaConj.lamConj_eq_self hlat
      (by unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM; rw [dite_eq_left hg2]; rfl)
      (by unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM; rw [dite_eq_left hg3]; rfl)
  have ht0 : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) (t M.val) := by
    have := ht M.val
    rw [hself] at this
    exact this
  have he : wpF (lamOf D cc δ) (t M.val) ∈ M := by
    obtain ⟨y, hy⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := M)
      (wpF (lamOf D cc δ) (t M.val)) (fun σ => by
        have hσ : ∀ z ∈ M, cj ⊤ (GlobalTheory.ThetaConj.topHom (σ : ℂ →+* ℂ)) z = z := fun z hz => by
          rw [GlobalTheory.ThetaConj.cj_top]; exact σ.commutes ⟨z, hz⟩
        have hL := GlobalTheory.ThetaConj.lamConj_eq_self hlat (hσ _ hg2) (hσ _ hg3)
        have := (key_top h (GlobalTheory.ThetaConj.topHom (σ : ℂ →+* ℂ)) ht0 (by rw [hL]; exact ht0)).2
        rw [hL, GlobalTheory.ThetaConj.cj_top] at this
        exact this.symm)
    rw [← hy]
    exact y.2
  have hg2M : Formalism.MainNotions.TaylorLogMetric.liftM M (g2 (lamOf D cc δ)) = ⟨_, hg2⟩ := by simp [Formalism.MainNotions.TaylorLogMetric.liftM, hg2]
  have hg3M : Formalism.MainNotions.TaylorLogMetric.liftM M (g3 (lamOf D cc δ)) = ⟨_, hg3⟩ := by simp [Formalism.MainNotions.TaylorLogMetric.liftM, hg3]
  have hone : (⟨_, hg2⟩ : M) ^ 3 - 27 * (⟨_, hg3⟩ : M) ^ 2 = 1 :=
    by
    have := hdisc
    unfold Formalism.MainNotions.TaylorLogMetric.discr at this
    ext; push_cast; exact this
  refine ⟨⟨_, he⟩, ⟨_, hg2⟩, rfl, hself, fun ρ => ?_⟩
  have hρ1 : ρ ⟨_, hg2⟩ ^ 3 - 27 * ρ ⟨_, hg3⟩ ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hone, map_one]
  have hspec : g2 (lamConj M ρ (lamOf D cc δ)) = ρ ⟨_, hg2⟩ ∧
      g3 (lamConj M ρ (lamOf D cc δ)) = ρ ⟨_, hg3⟩ := by
    obtain ⟨L0, hL0⟩ := hlat.exists_periodPair
    obtain ⟨L', h2', h3'⟩ := (GlobalTheory.LatticeInvariants.invariants_dictionary L0 _ hL0).2.2.2.2.2.2 _ _
      (by rw [hρ1]; exact one_ne_zero)
    have hw := GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
    have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
      g2 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (g2 (lamOf D cc δ))) ∧
        g3 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (g3 (lamOf D cc δ))))
      ⟨L'.lattice.toAddSubgroup, by rw [hw.1, h2', hg2M], by rw [hw.2.1, h3', hg3M]⟩
    exact ⟨hs.1.trans (congrArg ρ hg2M), hs.2.trans (congrArg ρ hg3M)⟩
  have hcM : Set.Countable (M : Set ℂ) := (Algebraic.countable ℚ ℂ).mono fun x hx =>
    show IsAlgebraic ℚ x from
      (IntermediateField.isAlgebraic_iff (x := (⟨x, hx⟩ : M))).mp (Algebra.IsAlgebraic.isAlgebraic _)
  haveI : Countable M := hcM.to_subtype
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := M) M.val.toRingHom ρ.toRingHom
  have hcj : ∀ z (hz : z ∈ M), cj M ρ z = cj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) z := fun z hz => by
    rw [GlobalTheory.ThetaConj.cj_of_mem _ _ hz, GlobalTheory.ThetaConj.cj_top]
    exact (hσ ⟨z, hz⟩).symm
  have hL : lamConj M ρ (lamOf D cc δ) = lamConj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) (lamOf D cc δ) :=
    GlobalTheory.ThetaConj.lamConj_congr (hcj _ hg2) (hcj _ hg3)
  have ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) (lamOf D cc δ)) (t ρ) := by
    have := ht ρ
    rw [hL] at this
    exact this
  obtain ⟨hn, hw⟩ := key_top h (GlobalTheory.ThetaConj.topHom σ.toRingHom) ht0 ht'
  refine ⟨?_, hspec.1, hL ▸ hn, ?_⟩
  · unfold Formalism.MainNotions.TaylorLogMetric.discr
    rw [hspec.1, hspec.2, hρ1]
  · rw [hL, hw, GlobalTheory.ThetaConj.cj_top]
    exact hσ ⟨_, he⟩

end GlobalTheory.HalfPeriodValue
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

noncomputable section

namespace GlobalTheory.Glob.FormDescent

theorem desc : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (z : S.Cl → GlobalTheory.Mem.Col2.Fr emb σ n → ℂ), z ∈ S.Fi emb σ lam → ∀ v : S.Cl → Formalism.L2.DIV.VV K lam, (∀ c, z c = evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (v c)) → ∃ y : S.FormsK emb lam h, (∀ c, y.1 c = v c) ∧ S.embF emb σ lam h y = z := by
  intro E K ι _ _ _ _ _ _ _ emb σ n S lam h z hz v hv
  have hinj : Function.Injective (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ) := by
    intro a b hab
    have h1 := congrArg (polOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n)) hab
    rw [GlobalTheory.LvT.BuiltChain.polOf_evV, GlobalTheory.LvT.BuiltChain.polOf_evV] at h1
    exact Subtype.ext (MvPolynomial.map_injective σ σ.injective h1)
  refine ⟨⟨v, fun c g => ?_⟩, fun c => rfl, ?_⟩
  · apply hinj
    show evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam c.1 g.1 (v c)) = _
    rw [GlobalTheory.LvT.BuiltChain.evV_rho, ← hv c]
    exact (hz c).2 ⟨g.1, g.2⟩
  · funext c
    exact (hv c).symm

end GlobalTheory.Glob.FormDescent
end
end

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

theorem infPow_infDiag {E : Type} [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ) (k : Eˣ) :
    infPow n (infDiag k) = infPow n (diagUnits E k) := by
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E).1 = ((diagUnits E k : Ideles E) : AdeleRing (𝓞 E) E).1 := by
    rw [infDiag_eq]
    rfl
  simp only [infPow, h]

end GlobalTheory.HeckeGal

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

theorem _root_.GlobalTheory.T.exists_conj_polynomial_definiteUnitary_rational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ), ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ p' ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  first | exact @GlobalTheory.UnitaryBC.exists_conj_polyFun | exact GlobalTheory.UnitaryBC.exists_conj_polyFun | (intros; apply GlobalTheory.UnitaryBC.exists_conj_polyFun <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix ComplexConjugate
attribute [local instance] IsCMField.starRing

namespace GlobalTheory.SelfDualDet
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.LocalConjugacy GlobalTheory.LocalLattice

theorem congr_of_hasSignature {r p q : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ}
    (hA : Formalism.UG.HasSignature A p q) (hB : Formalism.UG.HasSignature B p q) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ Bᵀ = Qᵀ * Aᵀ * Q.map conj := by
  obtain ⟨e, P, hP⟩ := hA
  obtain ⟨f, R, hR⟩ := hB
  have hc : ∀ M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ :=
    fun _ => rfl
  rw [hc] at hP hR
  have h1 : Matrix.reindex f f B = (P * R⁻¹).1ᴴ * Matrix.reindex e e A * (P * R⁻¹).1 := by
    have h2 : (R⁻¹).1ᴴ * R.1ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    calc Matrix.reindex f f B = ((R⁻¹).1ᴴ * R.1ᴴ) * Matrix.reindex f f B * (R.1 * (R⁻¹).1) := by
          rw [h2, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
      _ = (R⁻¹).1ᴴ * (R.1ᴴ * Matrix.reindex f f B * R.1) * (R⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hR, ← hP, Units.val_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
  generalize P * R⁻¹ = S at h1
  refine ⟨S.1.submatrix e f, ?_, ?_⟩
  · refine (Matrix.isUnit_det_of_right_inverse (B := (S⁻¹).1.submatrix f e) ?_).ne_zero
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv]
  · have h3 := congrArg (fun M => (Matrix.submatrix M f f)ᵀ) h1
    simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_comp_self,
      Matrix.submatrix_id_id] at h3
    rw [← Matrix.submatrix_mul_equiv _ _ f e f, ← Matrix.submatrix_mul_equiv _ _ f e e,
      Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id] at h3
    exact h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem det_eq_of_matrix [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] {r r' : ℕ} (h : r = r')
    {G : Matrix (Fin r) (Fin r) E} {G' : Matrix (Fin r') (Fin r') E}
    (hG : ∀ a b, cc (Gᵀ a b) = Gᵀ b a) (hG' : ∀ a b, cc (G'ᵀ a b) = G'ᵀ b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    {L : Submodule (𝓞 E) (Fin r → E)} {L' : Submodule (𝓞 E) (Fin r' → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L')
    (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm Gᵀ x y))
    (hsd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', IsIntegral ℤ (herm G'ᵀ x y))
    (hs : ∀ τ : E →+* ℂ, ∃ p q, Formalism.UG.HasSignature (G.map τ) p q ∧ Formalism.UG.HasSignature (G'.map τ) p q) :
    ∃ z : E, G'.det = z * star z * G.det := by
  subst h
  obtain ⟨P, -, hP⟩ := congr_of_modular (E := E) (𝔟 := 1)
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt one_ne_zero
    (fun _ hz => mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 hz)))
    hG hG' (by rwa [Matrix.det_transpose]) (by rwa [Matrix.det_transpose]) hL hL'
    (by simpa only [mem_one_fractionalIdeal_iff] using hsd)
    (by simpa only [mem_one_fractionalIdeal_iff] using hsd')
    fun τ => by
      obtain ⟨p, q, h1, h2⟩ := hs τ
      exact congr_of_hasSignature h1 h2
  have h1 := congrArg Matrix.det hP
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_transpose, Matrix.det_transpose,
    Published.det_map_cc] at h1
  refine ⟨P.det, h1.trans ?_⟩
  change _ = _ * cc _ * _
  ring

theorem det_eq_norm_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ W₁ W₂ : HSpace E, W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank → (∀ τ, W₁.sig τ = W₂.sig τ) → ∃ z : E, W₂.gram.det = z * star z * W₁.gram.det := by
  intro E _ _ _ hc W₁ W₂ h₁ h₂ hr hs
  haveI := GlobalTheory.DefiniteMass.unramified_of_isCMUnram hc
  exact det_eq_of_matrix hr (fun a b => W₁.herm.eq (W₁.frame b) (W₁.frame a))
    (fun a b => W₂.herm.eq (W₂.frame b) (W₂.frame a))
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₁).ne_zero (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₂).ne_zero
    (isLattice_coordLat W₁ W₁.L0 W₁.standardTuple_isLattice W₁.baseLattice_isUnimodular)
    (isLattice_coordLat W₂ W₂.L0 W₂.standardTuple_isLattice W₂.baseLattice_isUnimodular)
    (selfDual_coordLat W₁ W₁.L0 W₁.baseLattice_isUnimodular) (selfDual_coordLat W₂ W₂.L0 W₂.baseLattice_isUnimodular)
    fun τ => ⟨_, _, h₁ τ, hs τ ▸ h₂ τ⟩

end GlobalTheory.SelfDualDet
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.inverseIsometry_fourfoldLattice_denominator_coprime_alt : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], Nat.Coprime (Ideal.absNorm cc) q → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.IsIsom (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.stdH B.L (Fin 4 × D.what₂.Tau)) (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ¬ q ∣ Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) → Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0 → ∀ (G : (Fin 4 × D.what₂.Tau → D.host.K) ≃ₗ[D.host.K] (Fin 4 × D.what₂.Tau → D.host.K)), (∀ v : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((G v w : D.host.K) : D.host.E)) → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, (∀ w, v w ∈ (algebraMap (𝓞 D.host.K) D.host.K).range) → ∃ s : ℕ, Nat.Coprime s q ∧ ∀ a, (s : D.host.E) * B.γ₀.g.symm (G.symm v) a ∈ D.host.AA0 := by
  first | exact @GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime | exact GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime | (intros; apply GlobalTheory.LatInvDenom.inverseIsometry_fourfoldLattice_denominator_coprime <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem _root_.GlobalTheory.T.unitary_fourfoldLattice_preserves_rationalVectors : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, ∃ v' : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((v' w : D.host.K) : D.host.E) := by
  first | exact @GlobalTheory.LatDesc.unitary_maps_rational | exact GlobalTheory.LatDesc.unitary_maps_rational | (intros; apply GlobalTheory.LatDesc.unitary_maps_rational <;> assumption)
end
