module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle026
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle027
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
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Polynomial
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem HolomorphicOnSubset.continuousWithinAt {σ : Type*} [Fintype σ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : (σ → ℂ) → E} {S : Set (σ → ℂ)}
    (hf : HolomorphicOnSubset f S) {z : σ → ℂ} (hz : z ∈ S) : ContinuousWithinAt f S z := by
  obtain ⟨U, hUo, hzU, F, hF, hFeq⟩ := hf z hz
  have hc : ContinuousWithinAt F S z :=
    (hF.differentiableAt (hUo.mem_nhds hzU)).continuousAt.continuousWithinAt
  refine hc.congr_of_eventuallyEq ?_ (hFeq ⟨hz, hzU⟩)
  filter_upwards [inter_mem_nhdsWithin S (hUo.mem_nhds hzU)] with y hy
  exact hFeq hy

theorem BranchContainsNormalPoint.proof (hirr : NormalLocallyIrreducible.Statement)
    (hinv : BranchInverseHolomorphic.Statement) (hext : NormalRiemannExtension.Statement)
    (hmax : NormalMaximumPrinciple.Statement) : BranchContainsNormalPoint.Statement := by
  intro σ _ I h w k r φ B hI hIc hh hw hφd hφi hφZ hB hfill
  obtain ⟨B', hB'o, hwB', hB'B, -, hdense⟩ := hirr σ I h w hI hIc hh hw B hB
  set P := (zeroSetIn I ∩ B') \ {z | eval z h = 0} with hP
  have hPfill : P ⊆ φ '' Metric.ball 0 r := fun z hz => hfill ⟨⟨hz.1.1, hB'B hz.1.2⟩, hz.2⟩
  have hPsub : P ⊆ zeroSetIn I ∩ B' := fun y hy => hy.1
  have hwcl : w ∈ closure P := hdense ⟨hw, hwB'⟩
  obtain ⟨ψ, hψ, hψφ⟩ := hinv σ I h w k r φ B hI hIc hh hw hφd hφi hφZ hB hfill
  have hPψ : ∀ z ∈ P, ψ z ∈ Metric.ball (0 : Fin k → ℂ) r ∧ φ (ψ z) = z := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hPfill hz
    rw [hψφ t ht]
    exact ⟨ht, rfl⟩
  have hPlt : ∀ z ∈ P, ∀ j, ‖ψ z j‖ < r := fun z hz j =>
    (norm_le_pi_norm (ψ z) j).trans_lt (mem_ball_zero_iff.mp (hPψ z hz).1)

  have hcoord : ∀ j : Fin k, ∃ g : (σ → ℂ) → ℂ, HolomorphicOnSubset g (zeroSetIn I ∩ B') ∧
      Set.EqOn g (fun z => ψ z j) P := by
    intro j
    refine hext σ I h B' (fun z => ψ z j) hI hIc hh hB'o ?_ ?_
    · intro z hz
      obtain ⟨U, hUo, hzU, F, hF, hFeq⟩ := hψ z (hPfill hz)
      exact ⟨U, hUo, hzU, fun y => F y j, differentiableOn_pi.mp hF j,
        fun y hy => congrFun (hFeq ⟨hPfill hy.1, hy.2⟩) j⟩
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r)).subset ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hPlt z hz j).le
  choose g hg hgeq using hcoord

  have hgle : ∀ j, ∀ z ∈ zeroSetIn I ∩ B', ‖g j z‖ ≤ r := by
    intro j z hz
    have hcl := (((hg j).continuousWithinAt hz).mono hPsub).mem_closure_image (hdense hz)
    have hsub : g j '' P ⊆ Metric.closedBall 0 r := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right, hgeq j hy]
      exact (hPlt y hy j).le
    have := closure_minimal hsub Metric.isClosed_closedBall hcl
    rwa [Metric.mem_closedBall, dist_zero_right] at this

  have hglt : ∀ j, ‖g j w‖ < r := by
    intro j
    by_contra hlt
    have heq : ‖g j w‖ = r := le_antisymm (hgle j w ⟨hw, hwB'⟩) (not_lt.mp hlt)
    have hev := hmax σ I w B' (g j) hI hIc hw (hB'o.mem_nhds hwB') (hg j)
      (fun z hz => (hgle j z hz).trans heq.ge)
    obtain ⟨z, hz, hzP⟩ := mem_closure_iff_nhds.mp hwcl _ hev
    have h1 : ‖g j z‖ < r := (congrArg norm (hgeq j hzP)).trans_lt (hPlt z hzP j)
    rw [hz hzP.1.1, heq] at h1
    exact lt_irrefl r h1
  have hr : 0 < r := by
    obtain ⟨z, -, hzP⟩ := mem_closure_iff_nhds.mp hwcl _ Filter.univ_mem
    exact (norm_nonneg _).trans_lt (mem_ball_zero_iff.mp (hPψ z hzP).1)
  set t₀ : Fin k → ℂ := fun j => g j w with ht₀
  have ht₀Δ : t₀ ∈ Metric.ball (0 : Fin k → ℂ) r := mem_ball_zero_iff.mpr ((pi_norm_lt_iff hr).mpr hglt)
  refine ⟨t₀, ht₀Δ, ?_⟩

  have : (𝓝[P] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hwcl
  have hG : Tendsto (fun z => fun j => g j z) (𝓝[P] w) (𝓝 t₀) :=
    tendsto_pi_nhds.mpr fun j => (((hg j).continuousWithinAt ⟨hw, hwB'⟩).mono hPsub).tendsto
  have hφc : ContinuousAt φ t₀ := (hφd.differentiableAt (Metric.isOpen_ball.mem_nhds ht₀Δ)).continuousAt
  have h1 : Tendsto (fun z => φ (fun j => g j z)) (𝓝[P] w) (𝓝 (φ t₀)) := hφc.tendsto.comp hG
  have h2 : Tendsto (fun z => φ (fun j => g j z)) (𝓝[P] w) (𝓝 w) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hgz : (fun j => g j z) = ψ z := funext fun j => hgeq j hz
    rw [hgz, (hPψ z hz).2]
    rfl
  exact tendsto_nhds_unique h1 h2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem monic_eval_div_mul_pow {d : ℕ} (a : Fin d → ℂ) {F G : ℂ} (hG : G ≠ 0) :
    F ^ d + ∑ j : Fin d, a j * F ^ (j : ℕ) * G ^ (d - (j : ℕ)) =
      G ^ d * ((F / G) ^ d + ∑ j : Fin d, a j * (F / G) ^ (j : ℕ)) := by
  rw [mul_add, Finset.mul_sum, div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hG)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℕ) ≤ d := j.isLt.le
  have hGd : G ^ d = G ^ (j : ℕ) * G ^ (d - (j : ℕ)) := by rw [← pow_add, Nat.add_sub_cancel' hj]
  rw [hGd, div_pow]
  field_simp

theorem NormalBoundedQuotient.proof (hwi : WeaklyHolomorphicIntegral.Statement)
    (hic : NormalGermIntegrallyClosed.Statement) : NormalBoundedQuotient.Statement := by
  intro σ _ I w N F G hI hIc hw hN hwN hF hG hnv hb

  have hhol : HolomorphicOnSubset (fun z => F z / G z) ((zeroSetIn I ∩ N) \ {z | G z = 0}) := by
    intro z hz
    refine ⟨N ∩ G ⁻¹' {0}ᶜ, hG.continuousOn.isOpen_inter_preimage hN isOpen_compl_singleton,
      ⟨hz.1.2, hz.2⟩, fun z => F z / G z, ?_, fun _ _ => rfl⟩
    have hsub : N ∩ G ⁻¹' {0}ᶜ ⊆ N := Set.inter_subset_left
    simp only [div_eq_mul_inv]
    exact (hF.mono hsub).mul ((hG.mono hsub).inv fun y (hy : y ∈ N ∩ G ⁻¹' {0}ᶜ) => hy.2)
  obtain ⟨V, hVo, hwV, hVN, d, a, ha, heq⟩ :=
    hwi σ I w N G (fun z => F z / G z) hI hIc hw hN hwN hG hnv hhol hb
  refine hic σ I w V F G d a hI hIc hw hVo hwV (hF.mono hVN) (hG.mono hVN) ha hnv ?_
  intro z hz
  rw [monic_eval_div_mul_pow (fun j => a j z) (show G z ≠ 0 from hz.2), heq z hz, mul_zero]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem FormalFibresRegular.proof (hQ : FormalFibreQuotient.Statement)
    (hP : FormalFibresRegularPolynomial.Statement) : FormalFibresRegular.Statement := by
  intro k A _ _ _ hA m hm P _
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hA
  have hfs : Function.Surjective (f : MvPolynomial (Fin n) k →+* A) := hf
  obtain ⟨P', -, ⟨e⟩⟩ :=
    hQ (MvPolynomial (Fin n) k) A (f : MvPolynomial (Fin n) k →+* A) hfs inferInstance m P
  have hM : (m.comap (f : MvPolynomial (Fin n) k →+* A)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hfs (H := hm)
  have := hP k n _ hM P'.asIdeal
  exact IsRegularLocalRing.of_ringEquiv e.symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem primeFibreLocalRing_nonempty_equiv_of_surjective
    {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R R'] [Algebra S S'] (f : R →+* S) (φ : R' →+* S')
    (hf : Function.Surjective f) (hφ : Function.Surjective φ)
    (hcomm : φ.comp (algebraMap R R') = (algebraMap S S').comp f)
    (hker : RingHom.ker φ ≤ (RingHom.ker f).map (algebraMap R R'))
    (P : Ideal S') [P.IsPrime] :
    Nonempty (primeFibreLocalRing S P ≃+* primeFibreLocalRing R (P.comap φ)) := by
  set q := P.comap (algebraMap S S') with hq
  have hq' : (P.comap φ).comap (algebraMap R R') = q.comap f := by
    rw [hq, Ideal.comap_comap, Ideal.comap_comap, hcomm]
  have hmapq : ((q.comap f).map (algebraMap R R')).map φ = q.map (algebraMap S S') := by
    rw [Ideal.map_map, hcomm, ← Ideal.map_map, Ideal.map_comap_of_surjective f hf]
  let ψ : Localization.AtPrime (P.comap φ) →+* Localization.AtPrime P :=
    Localization.localRingHom (P.comap φ) P φ rfl
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    obtain ⟨a', rfl⟩ := hφ a
    obtain ⟨t', ht'⟩ := hφ (t : S')
    have ht'' : t' ∈ (P.comap φ).primeCompl := by
      change t' ∉ P.comap φ
      rw [Ideal.mem_comap, ht']
      exact t.2
    refine ⟨IsLocalization.mk' _ a' ⟨t', ht''⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht'
  let χ := (Ideal.Quotient.mk ((q.map (algebraMap S S')).map
    (algebraMap S' (Localization.AtPrime P)))).comp ψ
  have hχ : Function.Surjective χ := Ideal.Quotient.mk_surjective.comp hψ
  have hkerχ : ((q.comap f).map (algebraMap R R')).map
      (algebraMap R' (Localization.AtPrime (P.comap φ))) = RingHom.ker χ := by
    ext x
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (P.comap φ).primeCompl x
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
      Localization.localRingHom_mk', IsLocalization.mk'_mem_map_algebraMap_iff,
      IsLocalization.mk'_mem_map_algebraMap_iff]
    constructor
    · rintro ⟨t, ht, htr⟩
      refine ⟨φ t, ht, ?_⟩
      rw [← map_mul, ← hmapq]
      exact Ideal.mem_map_of_mem φ htr
    · rintro ⟨t, ht, htr⟩
      obtain ⟨t', rfl⟩ := hφ t
      refine ⟨t', ht, ?_⟩
      have h1 : φ (t' * r) ∈ ((q.comap f).map (algebraMap R R')).map φ := by
        rw [hmapq, map_mul]
        exact htr
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective φ hφ] at h1
      have key : Ideal.comap φ ⊥ ≤ (q.comap f).map (algebraMap R R') := by
        refine le_trans ?_ (le_trans hker (Ideal.map_mono ?_))
        · intro y hy
          simpa using hy
        · intro y hy
          rw [Ideal.mem_comap, RingHom.mem_ker.mp hy]
          exact q.zero_mem
      exact (sup_le le_rfl key) h1
  refine ⟨(((Ideal.quotEquivOfEq ?_).trans (RingHom.quotientKerEquivOfSurjective hχ))).symm⟩
  rw [← hkerχ, hq']

theorem exists_adicCompletion_surjection_of_surjective
    {B A : Type} [CommRing B] [CommRing A] (f : B →+* A) (hf : Function.Surjective f)
    (hB : IsNoetherianRing B) (m : Ideal A) :
    ∃ φ : AdicCompletion (m.comap f) B →+* AdicCompletion m A, Function.Surjective φ ∧
      φ.comp (algebraMap B (AdicCompletion (m.comap f) B)) =
        (algebraMap A (AdicCompletion m A)).comp f ∧
      RingHom.ker φ ≤ (RingHom.ker f).map (algebraMap B (AdicCompletion (m.comap f) B)) := by
  have := hB
  have : IsNoetherianRing A := isNoetherianRing_of_surjective B A f hf
  set M := m.comap f with hM
  have hpow : ∀ n : ℕ, (M ^ n).map f = m ^ n := fun n => by
    rw [Ideal.map_pow, hM, Ideal.map_comap_of_surjective f hf]
  let fam : (n : ℕ) → AdicCompletion M B →+* A ⧸ m ^ n := fun n =>
    (Ideal.quotientMap (m ^ n) f (Ideal.le_comap_pow f n)).comp
      (AdicCompletion.evalₐ M n : AdicCompletion M B →+* B ⧸ M ^ n)
  have hfam : ∀ {k n : ℕ} (hle : k ≤ n), (Ideal.Quotient.factorPow m hle).comp (fam n) = fam k := by
    intro k n hle
    ext x
    induction x using AdicCompletion.induction_on with
    | h b =>
      simp only [fam, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.evalₐ_mk]
      change Ideal.Quotient.factorPow m hle (Ideal.Quotient.mk (m ^ n) (f (b n))) =
        Ideal.Quotient.mk (m ^ k) (f (b k))
      rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
      have hb := AdicCompletion.AdicCauchySequence.mk_eq_mk hle b
      rw [Submodule.Quotient.eq] at hb
      have hb' : b n - b k ∈ M ^ k := by simpa using hb
      rw [← map_sub]
      exact Ideal.le_comap_pow f k hb'
  let φ : AdicCompletion M B →+* AdicCompletion m A := AdicCompletion.liftRingHom m fam hfam
  have hcomm : φ.comp (algebraMap B (AdicCompletion M B)) = (algebraMap A (AdicCompletion m A)).comp f := by
    refine RingHom.ext fun b => AdicCompletion.ext_evalₐ fun n => ?_
    simp only [φ, fam, RingHom.comp_apply, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_liftRingHom,
      RingHom.coe_coe, AdicCompletion.evalₐ_of, Algebra.algebraMap_self, RingHom.id_apply]
    rfl
  refine ⟨φ, ?_, hcomm, ?_⟩
  · have fgM : M.FG := IsNoetherian.noetherian M
    have fgm : m.FG := IsNoetherian.noetherian m
    have := AdicCompletion.isAdicComplete_self M fgM
    have hmap : (M.map (algebraMap B (AdicCompletion M B))).map φ =
        m.map (algebraMap A (AdicCompletion m A)) := by
      rw [Ideal.map_map, hcomm, ← Ideal.map_map, hM, Ideal.map_comap_of_surjective f hf]
    have : IsHausdorff ((M.map (algebraMap B (AdicCompletion M B))).map φ) (AdicCompletion m A) := by
      rw [hmap]
      exact (AdicCompletion.isAdicComplete_self m fgm).toIsHausdorff
    apply surjective_of_mk_map_comp_surjective (I := M.map (algebraMap B (AdicCompletion M B))) φ
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ m y)
    obtain ⟨b, rfl⟩ := hf a
    refine ⟨algebraMap B _ b, ?_⟩
    rw [RingHom.comp_apply, ← RingHom.comp_apply φ, hcomm, RingHom.comp_apply, Ideal.Quotient.eq, hmap,
      ← AdicCompletion.ker_evalOneₐ_eq_map m fgm, RingHom.mem_ker]
    simp [ha, AdicCompletion.algebraMap_apply]
  · intro x hx
    let _ : Algebra B A := f.toAlgebra
    let K := RingHom.ker f
    let g : B →ₗ[B] A := Algebra.linearMap B A
    have hg : Function.Surjective g := hf
    have hfg : Function.Exact K.subtype g := by
      intro y
      simp [g, K, RingHom.mem_ker, Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]
    have hx' : AdicCompletion.map M g x = 0 := by
      induction x using AdicCompletion.induction_on with
      | h b => ?_
      have hb := RingHom.mem_ker.mp hx
      refine AdicCompletion.ext fun n => ?_
      have h1 : f (b n) ∈ m ^ n := by
        have := congrArg (AdicCompletion.evalₐ m n) hb
        rw [map_zero] at this
        simp only [φ, AdicCompletion.evalₐ_liftRingHom, fam, RingHom.comp_apply, RingHom.coe_coe,
          AdicCompletion.evalₐ_mk] at this
        exact Ideal.Quotient.eq_zero_iff_mem.mp this
      have h2 : g (b n) ∈ (M ^ n • ⊤ : Submodule B A) := by
        rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
        change f (b n) ∈ (M ^ n).map f
        rw [hpow]
        exact h1
      simpa [AdicCompletion.map_mk] using h2
    obtain ⟨z, rfl⟩ := ((AdicCompletion.map_exact (I := M) Subtype.val_injective hfg hg) x).mp hx'
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite M K z
    have hnat := congrArg (fun F => F t) (AdicCompletion.ofTensorProduct_naturality M K.subtype)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hnat
    rw [hnat]
    clear hnat hx hx'
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r k =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq,
        Submodule.coe_subtype, AdicCompletion.ofTensorProduct_tmul]
      exact Ideal.mul_mem_left _ r (Ideal.mem_map_of_mem _ k.2)
    | add t₁ t₂ h₁ h₂ =>
      rw [map_add (f := _), map_add (f := _)]
      exact add_mem h₁ h₂

theorem FormalFibreQuotient.proof : FormalFibreQuotient.Statement := by
  intro B A _ _ f hf hB m P _
  obtain ⟨φ, hφ, hcomm, hker⟩ := exists_adicCompletion_surjection_of_surjective f hf hB m
  refine ⟨⟨P.comap φ, inferInstance⟩, ?_, ?_⟩
  · change (P.comap φ).comap _ = _
    rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
  · exact primeFibreLocalRing_nonempty_equiv_of_surjective f φ hf hφ hcomm hker P

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

theorem ringKrullDim_mvPolynomial_complex (d : ℕ) :
    ringKrullDim (MvPolynomial (Fin d) ℂ) = d := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem FiniteProjHomInjective.proof : FiniteProjHomInjective.Statement := by
  intro n d J A _ hdim hfin
  set f : MvPolynomial (Fin d) ℂ →+* MvPolynomial (Fin n) ℂ ⧸ J := (projHom J A).toRingHom with hf
  have hinj : Function.Injective f := by
    by_contra hni
    rw [injective_iff_map_eq_zero] at hni
    push Not at hni
    obtain ⟨p, hp0, hp⟩ := hni
    let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := f.toAlgebra
    have hint : f.IsIntegral := hfin.to_isIntegral

    let g : PrimeSpectrum (MvPolynomial (Fin n) ℂ ⧸ J) →
        PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin d) ℂ) (Ideal.span {p}) := fun q =>
      ⟨PrimeSpectrum.comap f q, by
        rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le,
          Set.singleton_subset_iff]
        show f p ∈ q.asIdeal
        rw [hp0]; exact q.asIdeal.zero_mem⟩
    have hg : StrictMono g := by
      intro q₁ q₂ hq
      have hlt : q₁.asIdeal < q₂.asIdeal := hq
      obtain ⟨hle, x, hx2, hx1⟩ := SetLike.lt_iff_le_and_exists.mp hlt
      show q₁.asIdeal.comap (algebraMap _ _) < q₂.asIdeal.comap (algebraMap _ _)
      exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hx2, hx1⟩ (hint x)
    have h1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤
        ringKrullDim (MvPolynomial (Fin d) ℂ ⧸ Ideal.span {p}) := by
      rw [ringKrullDim_quotient (Ideal.span {p})]
      exact Order.krullDim_le_of_strictMono g hg
    have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero hp)
    rw [ringKrullDim_mvPolynomial_complex] at h2
    rw [hdim] at h1
    have h3 : ((d : ℕ) : WithBot ℕ∞) + 1 ≤ (d : WithBot ℕ∞) := le_trans (by gcongr) h2
    have h4 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by exact_mod_cast h3
    have h5 : d + 1 ≤ d := by exact_mod_cast h4
    omega
  exact fun a b h => hinj h

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def NormalLocalDepthTwo.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B],
    SerreSAt B 2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreCriterion.Statement : Prop :=
  ∀ (A : Type) [CommRing A], IsNoetherianRing A → (NormalRing A ↔ SerreR A 1 ∧ SerreS A 2)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def SerreRFlatAscent.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], IsNoetherianRing A → IsNoetherianRing B →
    Module.Flat A B → ∀ k : ℕ, SerreR A k →
      (∀ (P : Ideal B) [P.IsPrime], SerreRAt (primeFibreLocalRing A P) k) → SerreR B k

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
