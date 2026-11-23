module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.WittVector.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle816
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle034
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.WithLp
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
import Mathlib.CategoryTheory.Preadditive.EndoFunctor
public import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle003
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle012

@[expose] public section

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.ColengthLemmas

variable {R : Type} [CommRing R]

theorem length_comp_range {A B C : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (u : B →ₗ[R] A) (v : C →ₗ[R] B) (hu : Function.Injective u) :
    Module.length R (A ⧸ LinearMap.range (u ∘ₗ v)) =
      Module.length R (A ⧸ LinearMap.range u) + Module.length R (B ⧸ LinearMap.range v) := by
  have hle : LinearMap.range v ≤ (LinearMap.range (u ∘ₗ v)).comap u := by
    rintro _ ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  have hle2 : LinearMap.range (u ∘ₗ v) ≤ LinearMap.range u := LinearMap.range_comp_le_range v u
  let f := (LinearMap.range v).mapQ (LinearMap.range (u ∘ₗ v)) u hle
  let g := Submodule.factor hle2
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := hx
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨c, hu hc⟩
  have hg : Function.Surjective g := Submodule.factor_surjective hle2
  have hex : Function.Exact f g := by
    intro x
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
    constructor
    · intro h
      have h' : a ∈ LinearMap.range u := by
        simpa [g, Submodule.factor_mk, Submodule.Quotient.mk_eq_zero] using h
      obtain ⟨b, rfl⟩ := h'
      exact ⟨Submodule.Quotient.mk b, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
      rw [← hy]
      show g (Submodule.Quotient.mk (u b)) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨b, rfl⟩
  rw [Module.length_eq_add_of_exact f g hf hg hex, add_comm]

theorem eq_of_le_of_length_eq {A : Type} [AddCommGroup A] [Module R A] (L L' : Submodule R A)
    (h : L ≤ L') (hl : Module.length R (A ⧸ L) = Module.length R (A ⧸ L'))
    (ht : Module.length R (A ⧸ L) ≠ ⊤) : L = L' := by
  let g := Submodule.factor h
  have e := Module.length_eq_add_of_exact (LinearMap.ker g).subtype g
    (LinearMap.ker g).injective_subtype (Submodule.factor_surjective h)
    (LinearMap.exact_subtype_ker_map g)
  have h0 : Module.length R (LinearMap.ker g) = 0 := by
    rw [← hl] at e
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 ht
    rw [← hn] at e
    generalize Module.length R (LinearMap.ker g) = b at e ⊢
    induction b using ENat.recTopCoe with
    | top => simp at e
    | coe b =>
      norm_cast at e ⊢
      omega
  rw [Module.length_eq_zero_iff] at h0
  refine le_antisymm h fun x hx => ?_
  have hmem : (Submodule.Quotient.mk x : A ⧸ L) ∈ LinearMap.ker g := by
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero _).2 hx
  have h1 : (⟨Submodule.Quotient.mk x, hmem⟩ : LinearMap.ker g) = 0 := Subsingleton.elim _ _
  have h2 : (Submodule.Quotient.mk x : A ⧸ L) = 0 := congrArg Subtype.val h1
  exact (Submodule.Quotient.mk_eq_zero _).1 h2

theorem length_quot_smul_range_free (O M : Type) [CommRing O] [Nontrivial O] [AddCommGroup M]
    [Module O M] [Module.Free O M] [Module.Finite O M] (a : O) :
    Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) =
      (Module.finrank O M : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical
  set d := Module.finrank O M
  let e : M ≃ₗ[O] (Fin d → O) := (Module.finBasis O M).equivFun
  have hmap : (LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))).map (e : M →ₗ[O] (Fin d → O))
      = Submodule.pi Set.univ (fun _ : Fin d => (Ideal.span {a} : Submodule O O)) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, true_implies,
      LinearMap.smul_apply, LinearMap.id_apply]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩ i
      rw [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
    · intro h
      choose c hc using fun i => Ideal.mem_span_singleton'.1 (h i)
      refine ⟨a • e.symm c, ⟨e.symm c, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      simp [← hc i, mul_comm]
  let f := (Submodule.Quotient.equiv _ _ e hmap).trans
    (Submodule.quotientPi (fun _ : Fin d => (Ideal.span {a} : Submodule O O)))
  rw [f.length_eq, Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]

theorem length_quot_p_pow (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (n : ℕ) : Module.length (WittVector p k) (WittVector p k ⧸ Ideal.span {(p : WittVector p k) ^ n}) = n := by
  rw [← Ideal.span_singleton_pow, ← (WittVector.irreducible p).maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal _ n

end GlobalTheory.Dieu.ColengthLemmas

namespace GlobalTheory.Dieu

open GlobalTheory.Dieu.ColengthLemmas in
theorem colength_add_and_pow_and_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A B C : Type) [AddCommGroup A] [Module (WittVector p k) A] [AddCommGroup B] [Module (WittVector p k) B] [AddCommGroup C] [Module (WittVector p k) C], (∀ (u : B →ₗ[(WittVector p k)] A) (v : C →ₗ[(WittVector p k)] B), Function.Injective u → Module.length (WittVector p k) (A ⧸ LinearMap.range (u ∘ₗ v)) = Module.length (WittVector p k) (A ⧸ LinearMap.range u) + Module.length (WittVector p k) (B ⧸ LinearMap.range v)) ∧ (Module.Free (WittVector p k) A → Module.Finite (WittVector p k) A → ∀ (n : ℕ) (u : A →ₗ[(WittVector p k)] A), (∀ a, u a = p ^ n • a) → Module.length (WittVector p k) (A ⧸ LinearMap.range u) = (n * Module.finrank (WittVector p k) A : ℕ)) ∧ ∀ L L' : Submodule (WittVector p k) A, L ≤ L' → Module.length (WittVector p k) (A ⧸ L) = Module.length (WittVector p k) (A ⧸ L') → Module.length (WittVector p k) (A ⧸ L) ≠ ⊤ → L = L' := by
  intro p _ k _ _ _ A B C _ _ _ _ _ _
  refine ⟨fun u v hu => length_comp_range u v hu, fun _ _ n u hu => ?_,
    fun L L' h hl ht => eq_of_le_of_length_eq L L' h hl ht⟩
  have hu' : u = ((p : WittVector p k) ^ n) • (LinearMap.id : A →ₗ[WittVector p k] A) := by
    ext a
    rw [hu a, LinearMap.smul_apply, LinearMap.id_apply, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [hu', length_quot_smul_range_free, length_quot_p_pow]
  push_cast
  ring

end GlobalTheory.Dieu
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviWeightChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem nmat_hasDerivAt (X : Data E r) {f : ℂ → V (nd X)} {f' : V (nd X)} {t : ℂ}
    (hf : HasDerivAt f f' t) (τ : X.Ψ) (a c : Fin r) :
    HasDerivAt (fun s => nmat X (f s) τ a c) (nmat X f' τ a c - if a = c then 1 else 0) t := by
  unfold nmat
  by_cases h : c < a
  · simp only [h, dif_pos, h.ne', if_false, sub_zero]
    exact
      ((PiLp.proj 2 (fun _ : Fin (nd X) => ℂ) ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩)).hasFDerivAt).comp_hasDerivAt t hf
  · simp only [h, dif_neg, not_false_eq_true, sub_self]
    exact hasDerivAt_const _ _

theorem nmat_zero_apply (X : Data E r) (τ : X.Ψ) (a c : Fin r) :
    nmat X 0 τ a c = if a = c then 1 else 0 := by
  have := congrFun (congrFun (IW.nmat_zero X τ) a) c
  simpa [mat, Matrix.one_apply] using this

theorem levi_transport_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x1 b : Frame X.Ψ r) (z : V (nd X)), IsOrth X x1 → z ∈ OmF X x0 → b ∈ Bor X.Ψ r → cpt X x0 z = rmul x1 b → ∀ ξ : Fin (nd X) → ℂ, ∃ ξ' : Fin (nd X) → ℂ, (∀ la : Wt X.Ψ r, leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 ξ') ∧ ∃ B : Frame X.Ψ r, (∀ τ (a c : Fin r), c < a → B τ a c = 0) ∧ ∀ τ, mat x0 τ * (mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) = mat x1 τ * ((mat (nmat X (WithLp.toLp 2 ξ')) τ - 1) * mat b τ + mat B τ) := by
  intro E _ _ _ r X x0 x1 b z ho hz hb hxb ξ
  have hz1 : (0 : V (nd X)) ∈ OmF X x1 := IW.zero_mem_OmF X x1 ho
  have hxb' : cpt X x0 z = rmul (cpt X x1 0) b := by rw [IW.cpt_zero]; exact hxb
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv 0 hz1 b hb
  rw [← hxb'] at h0
  have hcd : Differentiable ℂ (cpt X x0) := IW.cpt_diff X x0
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = 0 := h0.2.1
  have hbz : bf z = b := h0.2.2
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  set v : V (nd X) := WithLp.toLp 2 ξ with hv
  have hγ : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hγU : ∀ᶠ t in 𝓝 (0 : ℂ), z + t • v ∈ U := by
    have h := (hγ.continuousAt)
    simp only [ContinuousAt, zero_smul, add_zero] at h
    exact h (hU.mem_nhds hzU)
  have hbfD : HasDerivAt (fun t : ℂ => bf (z + t • v)) (fderiv ℂ bf z v) 0 :=
    (hbf.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
  have hΦD : HasDerivAt (fun t : ℂ => Φ (z + t • v)) (fderiv ℂ Φ z v) 0 :=
    (hΦ.differentiableAt (hU.mem_nhds hzU)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp)
  have hbfE : ∀ τ a c, HasDerivAt (fun t : ℂ => bf (z + t • v) τ a c) (fderiv ℂ bf z v τ a c) 0 :=
    fun τ a c => hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 hbfD τ) a) c
  refine ⟨fun k => (fderiv ℂ Φ z v).ofLp k, fun la => ?_, fderiv ℂ bf z v, ?_, ?_⟩
  · have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
      classical
      intro w hw
      unfold bchar
      refine DifferentiableAt.differentiableWithinAt ?_
      refine (HasFDerivAt.finsetProd (g' := fun τ => fderiv ℂ (fun w => ∏ i, bf w τ i i ^ la τ i) w)
        fun τ _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      refine (HasFDerivAt.finsetProd (g' := fun i => fderiv ℂ (fun w => bf w τ i i ^ la τ i) w)
        fun i _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
      have hw' : DifferentiableAt ℂ bf w := hbf.differentiableAt (hU.mem_nhds hw)
      have hi : DifferentiableAt ℂ (fun w => bf w τ i i) w :=
        differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hw' τ) i) i
      have hzp : DifferentiableAt ℂ (fun t : ℂ => t ^ la τ i) (bf w τ i i) :=
        differentiableAt_zpow.2
          (Or.inl (GlobalTheory.LeviTransfer.borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
      exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
    have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
      (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
    have hne : bchar la (bf z) ≠ 0 := IW.bchar_ne_zero X (hsplit _ hz h0.1).2.1 _
    have hev : (fun w => ((phla X la (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun w => ((phla X la (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
      filter_upwards [hU.mem_nhds hzU] with w hw
      obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
      rw [← GlobalTheory.LeviTransfer.metric_rmul normFactor_rightBorel_holds X la h1 h2, ← h3]
    have hg : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 w)) (Φ z) := by
      rw [hΦz]
      exact (IW.phla_cpt_cdAt X x1 hz1 la).of_le HE.two_le_inf
    have h1 : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 (Φ w))) z :=
      hg.comp z ((hΦ2.contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ)
    have h2 : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (bchar la (bf w)))) z :=
      (HE.normSq_contDiffAt hchz).log (Complex.normSq_pos.2 hne).ne'
    have hgC : ContDiffAt ℝ 2 (fun w => ((phla X la (cpt X x1 w) : ℝ) : ℂ)) (Φ z) :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
    have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
    rw [hΦz] at hc
    unfold leviM
    rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 h2,
      HE.levi_logNormSq_zero_at _ z hchz hne ξ, add_zero]
    exact congrArg Complex.re hc
  · intro τ a c hca
    have hev : (fun t : ℂ => bf (z + t • v) τ a c) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
      filter_upwards [hγU] with t ht
      exact ((hsplit _ ht.1 ht.2).2.1 τ).2 a c hca
    exact (hbfE τ a c).unique ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq hev)
  · intro τ
    ext a c
    have hL : HasDerivAt (fun t : ℂ => ∑ k, x0 τ a k * nmat X (z + t • v) τ k c)
        (∑ k, x0 τ a k * (nmat X v τ k c - if k = c then 1 else 0)) 0 :=
      HasDerivAt.fun_sum fun k _ => (nmat_hasDerivAt X hγ τ k c).const_mul _
    have hR : HasDerivAt (fun t : ℂ => ∑ k, (∑ l, x1 τ a l * nmat X (Φ (z + t • v)) τ l k) * bf (z + t • v) τ k c)
        (∑ k, ((∑ l, x1 τ a l * (nmat X (fderiv ℂ Φ z v) τ l k - if l = k then 1 else 0)) * bf (z + (0:ℂ) • v) τ k c
          + (∑ l, x1 τ a l * nmat X (Φ (z + (0:ℂ) • v)) τ l k) * fderiv ℂ bf z v τ k c)) 0 :=
      HasDerivAt.fun_sum fun k _ =>
        (HasDerivAt.fun_sum fun l _ => (nmat_hasDerivAt X hΦD τ l k).const_mul _).fun_mul (hbfE τ k c)
    have hev : (fun t : ℂ => ∑ k, x0 τ a k * nmat X (z + t • v) τ k c) =ᶠ[𝓝 0]
        fun t : ℂ => ∑ k, (∑ l, x1 τ a l * nmat X (Φ (z + t • v)) τ l k) * bf (z + t • v) τ k c := by
      filter_upwards [hγU] with t ht
      have e0 : cpt X x0 (z + t • v) = rmul (cpt X x1 (Φ (z + t • v))) (bf (z + t • v)) :=
        (hsplit _ ht.1 ht.2).2.2
      have e := congrFun (congrFun (congrFun e0 τ) a) c
      simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply] at e
      exact e
    have heq := hL.unique (hR.congr_of_eventuallyEq hev)
    simp only [zero_smul, add_zero, hΦz, hbz, nmat_zero_apply] at heq
    simp only [Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, mat, Matrix.of_apply,
      WithLp.toLp_ofLp]
    rw [heq]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]

end GlobalTheory.LeviWeightChart
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GrpMulSpread

attribute [local instance] Over.cartesianMonoidalCategory

theorem isPullback_pullbackMap {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} (cart : IsPullback F G'.hom G.hom f) :
    IsPullback (pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm)
      (G' ⊗ G').hom (G ⊗ G).hom f := by
  have p : IsPullback (pullback.snd G.hom G.hom) (pullback.fst G.hom G.hom) G.hom G.hom :=
    (IsPullback.of_hasPullback G.hom G.hom).flip
  have p' : IsPullback (pullback.snd G'.hom G'.hom) (pullback.fst G'.hom G'.hom) G'.hom G'.hom :=
    (IsPullback.of_hasPullback G'.hom G'.hom).flip
  have c₁ : pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ pullback.fst G.hom G.hom =
      pullback.fst G'.hom G'.hom ≫ F := pullback.lift_fst _ _ _
  have c₂ : pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫ pullback.snd G.hom G.hom =
      pullback.snd G'.hom G'.hom ≫ F := pullback.lift_snd _ _ _
  have q : IsPullback (pullback.map G'.hom G'.hom G.hom G.hom F F f cart.w.symm cart.w.symm ≫
      pullback.snd G.hom G.hom) (pullback.fst G'.hom G'.hom) G.hom (F ≫ G.hom) := by
    rw [c₂, cart.w]
    exact p'.paste_horiz cart
  exact (IsPullback.of_right q c₁ p).paste_vert cart

theorem pullbackMap_comp {S₁ S₀ Y : Scheme.{0}} {A₁ : Over S₁} {D : Over S₀} {U : Over Y} {k : S₁ ⟶ S₀}
    {h₀ : S₀ ⟶ Y} {φ : A₁.left ⟶ D.left} {ψ : D.left ⟶ U.left} (hφ : IsPullback φ A₁.hom D.hom k)
    (cart : IsPullback ψ D.hom U.hom h₀) :
    pullback.map A₁.hom A₁.hom D.hom D.hom φ φ k hφ.w.symm hφ.w.symm ≫
        pullback.map D.hom D.hom U.hom U.hom ψ ψ h₀ cart.w.symm cart.w.symm =
      pullback.map A₁.hom A₁.hom U.hom U.hom (φ ≫ ψ) (φ ≫ ψ) (k ≫ h₀)
        (hφ.paste_horiz cart).w.symm (hφ.paste_horiz cart).w.symm := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc]

theorem isGrpPullback_comp_spread_to_subring :
    ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → IsGrpPullback e.A d₀.A (spMap R₀.subtype) j → IsGrpPullback e.A u.A (spMap R₀.subtype ≫ h₀) (j ≫ ψ) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (A₁ : Over (Sp R₁)) [GrpObj A₁] (φ₁ : A₁.left ⟶ d₀.A.left), IsGrpPullback A₁ d₀.A (spMap (Subring.inclusion hle)) φ₁ → IsGrpPullback A₁ u.A (spMap (Subring.inclusion hle) ≫ h₀) (φ₁ ≫ ψ) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ ψ sE e j cart hj hjψ
  haveI := d₀.ab.proper
  haveI := u.ab.smooth
  haveI hqc : QuasiCompact (pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom) := inferInstance
  haveI hlft : LocallyOfFiniteType (pullback.snd u.A.hom h₀) := inferInstance
  set f₀ : pullback d₀.A.hom d₀.A.hom ⟶ Sp R₀ := pullback.fst d₀.A.hom d₀.A.hom ≫ d₀.A.hom with hf₀
  have hμd : (μ[d₀.A]).left ≫ d₀.A.hom = f₀ := Over.w μ[d₀.A]
  have hμu : (μ[u.A]).left ≫ u.A.hom = pullback.fst u.A.hom u.A.hom ≫ u.A.hom := Over.w μ[u.A]
  set mψ := pullback.map d₀.A.hom d₀.A.hom u.A.hom u.A.hom ψ ψ h₀ cart.w.symm cart.w.symm with hmψ
  have w₁ : ((μ[d₀.A]).left ≫ ψ) ≫ u.A.hom = f₀ ≫ h₀ := by
    rw [Category.assoc, cart.w, ← Category.assoc, hμd]
  have w₂ : (mψ ≫ (μ[u.A]).left) ≫ u.A.hom = f₀ ≫ h₀ := by
    rw [Category.assoc, hμu, ← Category.assoc, hmψ, pullback.lift_fst, Category.assoc, cart.w, hf₀,
      Category.assoc]
  let a : pullback d₀.A.hom d₀.A.hom ⟶ pullback u.A.hom h₀ := pullback.lift _ _ w₁
  let b : pullback d₀.A.hom d₀.A.hom ⟶ pullback u.A.hom h₀ := pullback.lift _ _ w₂
  have key : ∀ {S₁ : Scheme.{0}} {A₁ : Over S₁} [GrpObj A₁] {k : S₁ ⟶ Sp R₀} {φ : A₁.left ⟶ d₀.A.left}
      (hφ : IsPullback φ A₁.hom d₀.A.hom k),
      pullback.map A₁.hom A₁.hom d₀.A.hom d₀.A.hom φ φ k hφ.w.symm hφ.w.symm ≫ mψ =
        pullback.map A₁.hom A₁.hom u.A.hom u.A.hom (φ ≫ ψ) (φ ≫ ψ) (k ≫ h₀)
          (hφ.paste_horiz cart).w.symm (hφ.paste_horiz cart).w.symm := by
    intro S₁ A₁ _ k φ hφ
    exact pullbackMap_comp hφ cart
  have hab : pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm ≫ a =
      pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm ≫ b := by
    have m₁ := (GlobalTheory.PullDegCompare.isGrpPullback_iff hj.1).1 hj
    have m₂ := (GlobalTheory.PullDegCompare.isGrpPullback_iff hjψ.1).1 hjψ
    apply pullback.hom_ext
    · simp only [a, b, Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, ← m₁, Category.assoc, m₂]
      exact (congrArg (· ≫ (μ[u.A]).left) (key hj.1).symm).trans (Category.assoc _ _ _)
    · simp only [a, b, Category.assoc, pullback.lift_snd]
  obtain ⟨F, hF⟩ := GlobalTheory.morphisms_eq_spread_to_subring S R₀ (pullback e.A.hom e.A.hom)
    (pullback d₀.A.hom d₀.A.hom) (pullback u.A.hom h₀) (e.A ⊗ e.A).hom f₀ (pullback.snd u.A.hom h₀)
    (pullback.map e.A.hom e.A.hom d₀.A.hom d₀.A.hom j j (spMap R₀.subtype) hj.1.w.symm hj.1.w.symm) a b
    (isPullback_pullbackMap hj.1) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) hab
  refine ⟨F, fun R₁ hle hFs A₁ _ φ₁ hφ ↦ ?_⟩
  have cart₁ := hφ.1.paste_horiz cart
  refine (GlobalTheory.PullDegCompare.isGrpPullback_iff cart₁).2 ?_
  have H := hF R₁ hle hFs (pullback A₁.hom A₁.hom) (A₁ ⊗ A₁).hom
    (pullback.map A₁.hom A₁.hom d₀.A.hom d₀.A.hom φ₁ φ₁ _ hφ.1.w.symm hφ.1.w.symm)
    (isPullback_pullbackMap hφ.1)
  have H' := congrArg (· ≫ pullback.fst u.A.hom h₀) H
  simp only [a, b, Category.assoc, pullback.lift_fst] at H'
  have m := (GlobalTheory.PullDegCompare.isGrpPullback_iff hφ.1).1 hφ
  rw [← Category.assoc, m, Category.assoc, H']
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (μ[u.A]).left) (key hφ.1))

end GlobalTheory.GrpMulSpread
end
end
