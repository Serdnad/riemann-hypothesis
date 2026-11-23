module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle648
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open scoped ContDiff ComplexConjugate Topology

noncomputable section

namespace MainStatements.WeightKernel.Dec.DDerMemc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exp_entry (Z : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • Z)) i j := by
  open scoped Matrix.Norms.Operator in
  have h1 : ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • Z) : Matrix (Fin n) (Fin n) ℂ) := by
    have : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
      contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    exact this.comp (contDiff_id.smul contDiff_const)
  open scoped Matrix.Norms.Operator in
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff.comp h1

theorem lineSm (h : IsCMExt F E σ) {b : ℝ → GAd σ J} (hb : IsRealLine σ J b) :
    ContDiff ℝ ∞ fun t => infCoord σ J (projInf σ J (b t)) := by
  classical
  obtain ⟨w, τ, Z, -, hZ⟩ := hb
  choose y hy hyZ using hZ
  refine contDiff_pi.2 fun u => contDiff_pi.2 fun τ' => contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e0 : ∀ t, infCoord σ J (projInf σ J (b t)) u τ' i j = archMat σ J τ' (projArch σ J u (embArch σ J w (y t))) i j :=
    fun t => by rw [← hy t, ← projInfArch_projInf]; rfl
  simp only [e0]
  by_cases hu : u = w
  · subst hu
    simp only [projArch_embArch_self]
    have e1 : ∀ t, infEmb τ ((matHom _ σ J (y t)).1 i j) = (NormedSpace.exp (t • Z)) i j := fun t => by
      rw [← hyZ t]; rfl
    rcases infEmb_eq_or_conj h τ τ' with e | e
    · have : ∀ t, archMat σ J τ' (y t) i j = (NormedSpace.exp (t • Z)) i j := fun t => by
        rw [← e1 t, ← e]; rfl
      simp only [this]; exact exp_entry Z i j
    · have : ∀ t, archMat σ J τ' (y t) i j = conj ((NormedSpace.exp (t • Z)) i j) := fun t => by
        rw [← e1 t]
        change infEmb τ' _ = _
        rw [e]; rfl
      simp only [this]; exact Complex.conjCLE.contDiff.comp (exp_entry Z i j)
  · simp only [projArch_embArch_ne σ J hu]
    exact contDiff_const

theorem main (h : IsCMExt F E σ) {b : ℝ → GAd σ J} (hb : IsRealLine σ J b) {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    (∀ g, DifferentiableAt ℝ (fun t => f (g * b t)) 0) ∧ lineDer b f ∈ CcAd σ J := by
  have hβ := lineSm h hb
  have hfin : ∀ t, projFin σ J (b t) = 1 := fun t =>
    mem_infPts.1 (GlobalTheory.RealLineInf.realLine_mem_infPts F E σ n J b hb t)
  have hbc : Continuous b := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
  have hb0 : b 0 = 1 := GlobalTheory.UAut.ConstAut.realLine_zero h hb
  obtain ⟨-, ⟨m, hm, em⟩, -⟩ := isGroupCoord_infCoord σ J
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ⟨hac, Φ, hΦ, ea⟩, c, hc, rfl⟩ := hf
    set G := fun p : _ × ℝ => Φ (m (p.1, infCoord σ J (projInf σ J (b p.2)))) with hG
    have hGs : ContDiff ℝ ∞ G := hΦ.comp (hm.comp (contDiff_fst.prodMk (hβ.comp contDiff_snd)))
    have hd : ∀ x, HasDerivAt (fun t : ℝ => G (x, t)) (fderiv ℝ G (x, 0) (0, 1)) 0 := fun x =>
      ((hGs.differentiable (by simp)) (x, (0 : ℝ))).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))
    have ea' : ∀ (g : GInf σ J) t, a (g * projInf σ J (b t)) = G (infCoord σ J g, t) := fun g t => by
      rw [ea, em]
    have e1 : ∀ g, (fun t => infFin σ J a c (g * b t)) =
        fun t => G (infCoord σ J (projInf σ J g), t) * c (projFin σ J g) := fun g => funext fun t => by
      simp only [infFin, map_mul, hfin, mul_one, ea']
    refine ⟨fun g => by rw [e1]; exact ((hd _).mul_const _).differentiableAt, ?_⟩
    have e2 : lineDer b (infFin σ J a c) =
        infFin σ J (fun g => fderiv ℝ G (infCoord σ J g, 0) (0, 1)) c := funext fun g => by
      rw [lineDer, e1, ((hd _).mul_const _).deriv]; rfl
    rw [e2]
    refine infFin_mem_ccAd ⟨HasCompactSupport.intro hac.isCompact fun g hg => ?_,
      fun x => fderiv ℝ G (x, 0) (0, 1), ?_, fun _ => rfl⟩ hc
    · rw [← (hd _).deriv]
      have hc1 : Continuous fun t => g * projInf σ J (b t) :=
        continuous_const.mul ((continuous_projInf σ J).comp hbc)
      have : ∀ᶠ t in 𝓝 (0 : ℝ), g * projInf σ J (b t) ∈ (tsupport a)ᶜ :=
        hc1.continuousAt.eventually_mem ((isClosed_tsupport a).isOpen_compl.mem_nhds (by simpa [hb0] using hg))
      have e3 : (fun t : ℝ => G (infCoord σ J g, t)) =ᶠ[𝓝 0] fun _ => 0 :=
        this.mono fun t ht => (ea' g t).symm.trans (image_eq_zero_of_notMem_tsupport ht)
      rw [e3.deriv_eq, deriv_const]
    · exact ((hGs.fderiv_right (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const
  | zero => exact ⟨fun g => differentiableAt_const _, by
      have : lineDer b (0 : GAd σ J → ℂ) = 0 := funext fun g => by simp [lineDer]
      rw [this]; exact zero_mem _⟩
  | add f f' _ _ h1 h2 =>
    refine ⟨fun g => (h1.1 g).add (h2.1 g), ?_⟩
    have : lineDer b (f + f') = lineDer b f + lineDer b f' := funext fun g => deriv_add (h1.1 g) (h2.1 g)
    rw [this]; exact add_mem h1.2 h2.2
  | smul a f _ h1 =>
    refine ⟨fun g => (h1.1 g).const_smul a, ?_⟩
    have : lineDer b (a • f) = a • lineDer b f := funext fun g => deriv_const_smul a (h1.1 g)
    rw [this]; exact Submodule.smul_mem _ a h1.2

end MainStatements.WeightKernel.Dec.DDerMemc

theorem MainStatements.WeightKernel.Dec.derMem : MainStatements.WeightKernel.Dec.DerMem :=
  fun _ _ _ _ _ _ _ _ h _ _ _ _ hf _ hb => (MainStatements.WeightKernel.Dec.DDerMemc.main h hb hf).2
end
end

section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DBase

theorem ncard_biUnion_le' {α ι : Type*} (I : Finset ι) (S : ι → Set α) (h : ∀ i ∈ I, (S i).Finite) :
    (⋃ i ∈ I, S i).ncard ≤ ∑ i ∈ I, (S i).ncard := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert j I hj ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hj]
    refine (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) _)

end MainStatements.WeightKernel.Dec.DBase

namespace MainStatements.WeightKernel.Dec
open DBase

theorem base : Base := by
  intro D V r X Y hW c hc
  obtain ⟨V₀, hV₀c, hV₀n⟩ := exists_compact_mem_nhds (1 : GA D V)
  have hC₀ : IsCompact (V₀⁻¹ * V₀) := hV₀c.inv.mul hV₀c
  obtain ⟨A, B₀, hAB⟩ := GlobalTheory.T.finite_lattice_points_in_siegel_set_bound D V r X Y hW c hc _ hC₀
  refine ⟨A, fun Γ hΓ f hf hfs C W hC hW' => ?_⟩
  set K : Set (GA D V) := C⁻¹ * tsupport f * W⁻¹ with hK
  have hKc : IsCompact K := (hC.inv.mul hfs.isCompact).mul hW'.inv
  have hint : interior V₀ ∈ nhds (1 : GA D V) := interior_mem_nhds.2 hV₀n
  obtain ⟨I, hI⟩ := hKc.elim_finite_subcover (fun g : K => (g : GA D V) • interior V₀)
    (fun g => isOpen_interior.smul _) (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩,
      ⟨1, mem_of_mem_nhds hint, by simp⟩⟩)
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfs
  refine ⟨max M 0 * I.card * max B₀ 0, fun t ht a ha x hx y hy => ?_⟩
  obtain ⟨hfin₀, hcnt₀⟩ := hAB t ht a ha
  set S₀ := {δ : GF V | a⁻¹ * rat V δ * a ∈ V₀⁻¹ * V₀}
  set S : K → Set (GF V) := fun g => {δ : GF V | a⁻¹ * rat V δ * a ∈ (g : GA D V) • V₀}
  have hS : ∀ g, (S g).Finite ∧ (S g).ncard ≤ S₀.ncard := by
    intro g
    rcases (S g).eq_empty_or_nonempty with h | ⟨δ₀, hδ₀⟩
    · rw [h]; simp
    have hmap : ∀ δ ∈ S g, δ₀⁻¹ * δ ∈ S₀ := by
      intro δ hδ
      obtain ⟨u, hu, hu'⟩ := hδ
      obtain ⟨u₀, hu₀, hu₀'⟩ := hδ₀
      refine ⟨u₀⁻¹, Set.inv_mem_inv.2 hu₀, u, hu, ?_⟩
      simp only [smul_eq_mul] at hu' hu₀'
      have e : a⁻¹ * rat V (δ₀⁻¹ * δ) * a = (a⁻¹ * rat V δ₀ * a)⁻¹ * (a⁻¹ * rat V δ * a) := by
        simp [map_mul, map_inv, mul_assoc]
      rw [e, ← hu', ← hu₀']; group
    have hinj : Set.InjOn (fun δ => δ₀⁻¹ * δ) (S g) := fun _ _ _ _ h => mul_left_cancel h
    have hf1 : (S g).Finite := Set.Finite.of_finite_image (hfin₀.subset (by
      rintro _ ⟨δ, hδ, rfl⟩; exact hmap δ hδ)) hinj
    exact ⟨hf1, Set.ncard_le_ncard_of_injOn _ hmap hinj hfin₀⟩
  set T := {δ : GF V | a⁻¹ * rat V δ * a ∈ K}
  have hTsub : T ⊆ ⋃ g ∈ I, S g := by
    intro δ hδ
    obtain ⟨g, hg, hmem⟩ := Set.mem_iUnion₂.1 (hI hδ)
    exact Set.mem_iUnion₂.2 ⟨g, hg, Set.smul_set_mono interior_subset hmem⟩
  have hUfin : (⋃ g ∈ I, S g).Finite := Set.Finite.biUnion I.finite_toSet fun g _ => (hS g).1
  have hTfin : T.Finite := hUfin.subset hTsub
  have hTcnt : (T.ncard : ℝ) ≤ I.card * max B₀ 0 * (∏ i, max (t i) 1) ^ A := by
    have h1 : T.ncard ≤ I.card * S₀.ncard := by
      refine (Set.ncard_le_ncard hTsub hUfin).trans ((ncard_biUnion_le' I S fun g _ => (hS g).1).trans ?_)
      simpa using Finset.sum_le_sum (s := I) fun g _ => (hS g).2
    have hP : 0 ≤ (∏ i, max (t i) 1) ^ A :=
      pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) A
    calc (T.ncard : ℝ) ≤ I.card * S₀.ncard := by exact_mod_cast h1
      _ ≤ I.card * (max B₀ 0 * (∏ i, max (t i) 1) ^ A) := by
          gcongr
          exact hcnt₀.trans (by gcongr; exact le_max_left _ _)
      _ = _ := by ring

  set g : Γ → ℂ := fun ν => f (x * a⁻¹ * ν * (a * y)) with hg
  have hsupp : ∀ ν : Γ, g ν ≠ 0 → ∃ δ ∈ T, rat V δ = ν := by
    intro ν hν
    obtain ⟨δ, hδ⟩ : (ν : GA D V) ∈ (ratEmb D.sp.cm.sig V.gram).range :=
      (range_ratEmb D.sp.cm.sig V.gram).symm ▸ hΓ ν.2
    refine ⟨δ, ?_, hδ⟩
    have hs : x * a⁻¹ * ν * (a * y) ∈ tsupport f := subset_tsupport _ hν
    show a⁻¹ * rat V δ * a ∈ K
    refine ⟨x⁻¹ * (x * a⁻¹ * ν * (a * y)), ⟨x⁻¹, Set.inv_mem_inv.2 hx, _, hs, rfl⟩, y⁻¹,
      Set.inv_mem_inv.2 hy, ?_⟩
    show _ = _
    rw [show rat V δ = ν from hδ]; group
  have hsf : (Function.support g).Finite := by
    refine (hTfin.image (rat V)).preimage (Subtype.val_injective.injOn) |>.subset ?_
    intro ν hν
    obtain ⟨δ, hδ, e⟩ := hsupp ν hν
    exact ⟨δ, hδ, e⟩
  have hcard : (hsf.toFinset.card : ℝ) ≤ T.ncard := by
    have : (Function.support g).ncard ≤ T.ncard := by
      have h2 : (Function.support g).ncard ≤ (rat V '' T).ncard :=
        Set.ncard_le_ncard_of_injOn Subtype.val (fun ν hν => by
          obtain ⟨δ, hδ, e⟩ := hsupp ν hν; exact ⟨δ, hδ, e⟩) Subtype.val_injective.injOn (hTfin.image _)
      exact h2.trans (Set.ncard_image_le hTfin)
    rw [Set.ncard_eq_toFinset_card _ hsf] at this
    exact_mod_cast this
  show ‖∑' ν : Γ, g ν‖ ≤ _
  rw [tsum_eq_sum (s := hsf.toFinset) (fun ν hν => by simpa using hν)]
  have hP : 0 ≤ (∏ i, max (t i) 1) ^ A :=
    pow_nonneg (Finset.prod_nonneg fun i _ => le_trans zero_le_one (le_max_right _ _)) A
  calc ‖∑ ν ∈ hsf.toFinset, g ν‖ ≤ ∑ ν ∈ hsf.toFinset, ‖g ν‖ := norm_sum_le _ _
    _ ≤ ∑ _ν ∈ hsf.toFinset, max M 0 := Finset.sum_le_sum fun ν _ => (hM _).trans (le_max_left _ _)
    _ = hsf.toFinset.card * max M 0 := by simp
    _ ≤ T.ncard * max M 0 := by gcongr
    _ ≤ (I.card * max B₀ 0 * (∏ i, max (t i) 1) ^ A) * max M 0 := by gcongr
    _ = _ := by ring

end MainStatements.WeightKernel.Dec
end
end
