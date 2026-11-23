module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HaarFibreUniqueness.FibExGram
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle008
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle020
import Aesop.Main
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfCo
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.EventuallySmulSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoNuFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

section HermMod

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_algebraMap (σ : E →ₐ[F] E) (t : R) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.algebraMap_apply]

theorem hR_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : R)
    (x y : Fin M → R ⊗[F] E) : hR R σ J (t • x) y = t • hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : R)
    (x y : Fin M → R ⊗[F] E) : hR R σ J x (t • y) = t • hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

instance hermSMul (σ : E →ₐ[F] E) (n : ℕ) : SMul R (HermR R σ n) :=
  ⟨fun t S => ⟨t • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h := S.2 a b
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap]
    rw [h]⟩⟩

theorem coe_hermSMul (σ : E →ₐ[F] E) (n : ℕ) (t : R) (S : HermR R σ n) :
    ((t • S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = t • (S : Matrix _ _ _) := rfl

instance hermModule (σ : E →ₐ[F] E) (n : ℕ) : Module R (HermR R σ n) :=
  Function.Injective.module R (HermR R σ n).subtype Subtype.coe_injective (fun _ _ => rfl)

end HermMod

theorem exists_unif_Fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0) ∧
      π ∈ v.adicCompletionIntegers F := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  have h1 : Valued.v (π : v.adicCompletion F) < 1 := by
    rw [hv]
    decide
  refine ⟨π, fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖(π : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le

theorem gramFilt_of (hDx : DxOpen) : GramFilt := by
  intro F E _ _ _ _ σ hσ M J hJ hdet a ha1 _ v d b x hx
  letI : FiniteDimensional F E := Module.Finite.of_basis b
  letI : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  letI : NumberField E :=
    { to_charZero := inferInstance
      to_finiteDimensional := Module.Finite.trans F E }
  exact PI.VolStabSW.OmFibG.gramFilt_gen σ hσ M J hJ hdet a ha1 v d b x hx

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct ENNReal

def DetAdm : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  ∀ ν1 ν2 : Measure (Fin a → Fin M → AF F ⊗[F] E),
    (∀ K, IsCompact K → ν1 K < ⊤) → (∀ K, IsCompact K → ν2 K < ⊤) →
    (∀ Φ, IsAdm F E Φ → ∫ X, Φ X ∂ν1 = ∫ X, Φ X ∂ν2) → ν1 = ν2

def OmUniq : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ ν1 ν2, IsOmT F E σ M J ψ (gramE σ J X0) hT ν1 →
    IsOmT F E σ M J ψ (gramE σ J X0) hT ν2 → ν1 = ν2

def OmInv : Prop := InCtx fun F E _ _ _ _ _ σ M J _a X0 hT =>
  ∀ ψ, IsCharAF F ψ → ∀ νX, IsOmT F E σ M J ψ (gramE σ J X0) hT νX →
    ∀ g : HA (AF F) σ J, IsOmT F E σ M J ψ (gramE σ J X0) hT (νX.map fun y => g • y)

theorem continuous_smul_tup {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (σ : E →ₐ[F] E) {M a : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA (AF F) σ J) :
    Continuous (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) := by

  have hm : ∀ A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
      Continuous fun y : Fin a → Fin M → AF F ⊗[F] E => fun i => A.mulVec (y i) := fun A =>
    continuous_pi fun i => continuous_const.matrix_mulVec (continuous_apply i)
  first
  | exact hm _
  | exact hm ((HA.mat (AF F) σ J g : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _)

theorem nuInv_of (hU : OmUniq) (hI : OmInv) : NuInv := by

  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ νX hν g s hs
  haveI : FiniteDimensional F E := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℚ F E
    | exact FiniteDimensional.right ℚ F E
  have hm : Measurable (fun y : Fin a → Fin M → AF F ⊗[F] E => g • y) :=
    (continuous_smul_tup σ J g).measurable
  have heq := hU F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ _ _
    (hI F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ νX hν g) hν
  rw [← Measure.map_apply hm hs, heq]

theorem omUniq_of (hD : DetAdm) : OmUniq := by

  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ψ hψ ν1 ν2 hν1 hν2
  haveI : FiniteDimensional F E := by
    first
    | infer_instance
    | exact Module.Finite.of_restrictScalars_finite ℚ F E
    | exact FiniteDimensional.right ℚ F E
  refine hD F E σ hCM M J hJ h1 h2 a ha haM X0 hT hdet ν1 ν2
    (fun K hK => nuFin_gen σ J _ hT ψ ν1 hν1 K hK) (fun K hK => nuFin_gen σ J _ hT ψ ν2 hν2 K hK) ?_
  rintro Φ ⟨d, b, Φinf, Φf, Φv, hc, hcs, hpure, hprod⟩
  obtain ⟨-, ⟨μinf, hμinf⟩, A1⟩ := hν1
  obtain ⟨-, -, A2⟩ := hν2
  obtain ⟨⟨νinf, hνinf⟩, B1⟩ := A1 μinf hμinf
  obtain ⟨-, B2⟩ := A2 μinf hμinf
  obtain ⟨⟨μv, hμv⟩, C1⟩ := B1 νinf hνinf
  obtain ⟨-, C2⟩ := B2 νinf hνinf
  obtain ⟨⟨νv, hνv⟩, D1⟩ := C1 μv hμv
  obtain ⟨-, D2⟩ := C2 μv hμv
  obtain ⟨⟨fi, hfi⟩, E1⟩ := D1 νv hνv
  obtain ⟨-, E2⟩ := D2 νv hνv
  obtain ⟨⟨fv, hfv⟩, G1⟩ := E1 fi hfi
  obtain ⟨-, G2⟩ := E2 fi hfi
  obtain ⟨-, -, H1⟩ := G1 fv hfv d b Φ Φinf Φf Φv hc hcs hpure hprod
  obtain ⟨-, -, H2⟩ := G2 fv hfv d b Φ Φinf Φf Φv hc hcs hpure hprod
  rw [H1, H2]

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS.RestrProdA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem hasProd_compl_of_ne_zero {β : Type} {f : β → ℂ} {p : ℂ} (h : HasProd f p) (S : Finset β)
    (hS : ∀ b ∈ S, f b ≠ 0) :
    HasProd ({b | b ∉ S}.mulIndicator f) (p * ∏ b ∈ S, (f b)⁻¹) := by
  classical
  have h2 : HasProd (fun b => if b ∈ S then (f b)⁻¹ else 1)
      (∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1)) := hasProd_prod_of_ne_finset_one fun b hb => if_neg hb
  have e : ∏ b ∈ S, (if b ∈ S then (f b)⁻¹ else 1) = ∏ b ∈ S, (f b)⁻¹ :=
    Finset.prod_congr rfl fun b hb => if_pos hb
  rw [e] at h2
  convert h.mul h2 using 1
  funext b
  by_cases hb : b ∈ S
  · simp [Set.mulIndicator, hb, hS b hb]
  · simp [Set.mulIndicator, hb]

theorem hasProd_ofReal_of_complex {β : Type} {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) {q : ℂ}
    (h : HasProd (fun b => (f b : ℂ)) q) :
    HasProd (fun b => ENNReal.ofReal (f b)) (ENNReal.ofReal q.re) := by
  unfold HasProd at h ⊢
  have h1 := ((ENNReal.continuous_ofReal.comp Complex.continuous_re).tendsto q).comp h
  refine h1.congr fun s => ?_
  simp only [Function.comp_apply, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact ENNReal.ofReal_prod_of_nonneg fun b _ => hf b

theorem rpTail_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {a M d : ℕ} (b : Module.Basis (Fin d) F E)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin a → Fin M → Fv F v ⊗[F] E))
    (hSB : ∀ v (Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ), IsSB Φ → Integrable Φ (m v))
    (hmult : ∀ (Φf : (Fin a → Fin M → Af F ⊗[F] E) → ℂ)
      (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ),
      IsPureFin b Φf Φv → Multipliable (fun v => ∫ X, Φv v X ∂(m v))) :
    (∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ → ∫ X, Φ X ∂(m v) = 0) ∨
    ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ c : ENNReal, c ≠ ⊤ ∧
      HasProd (fun v : {v // v ∉ S} => m v.1 (latV b v.1)) c := by
  classical
  by_cases h0 : ∃ v, ∀ Φ : (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ, IsSB Φ → ∫ X, Φ X ∂(m v) = 0
  · exact Or.inl h0
  refine Or.inr fun S => ?_
  push_neg at h0
  choose g hgSB hg0 using h0
  let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin M → Fv F v ⊗[F] E) → ℂ :=
    fun v => if v ∈ S then g v else (latV b v).indicator 1
  have hpure : IsPureFin b (fun Y => ∏ᶠ v, Φv v (projV v Y)) Φv := by
    refine ⟨fun v => ?_, ?_, fun Y => rfl⟩
    · by_cases hv : v ∈ S
      · simp only [Φv, hv, if_true]; exact hgSB v
      · simp only [Φv, hv, if_false]; exact PositiveNearLattice.isSB_latV b v a M
    · refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
      by_contra h
      exact hv (if_neg h)
  have hP := (hmult _ Φv hpure).hasProd
  have hne : ∀ v ∈ S, ∫ X, Φv v X ∂(m v) ≠ 0 := fun v hv => by
    simp only [Φv, hv, if_true]; exact hg0 v
  have h1 := hasProd_compl_of_ne_zero hP S hne
  have hL : ∀ v, MeasurableSet (latV (M := M) (n := a) b v) := fun v =>
    (PositiveNearLattice.isClopen_latV b v a M).isOpen.measurableSet
  have hfin : ∀ v, m v (latV b v) ≠ ⊤ := fun v => by
    have h := hSB v _ (PositiveNearLattice.isSB_latV b v a M)
    rw [integrable_indicator_iff (hL v)] at h
    exact (((integrableOn_const_iff (C := (1 : ℂ))).1 h).resolve_left (by simp)).ne
  have e : {v | v ∉ S}.mulIndicator (fun v => ∫ X, Φv v X ∂(m v)) =
      fun v => (({v | v ∉ S}.mulIndicator (fun v => (m v (latV b v)).toReal) v : ℝ) : ℂ) := by
    funext v
    by_cases hv : v ∈ S
    · simp [Set.mulIndicator, hv]
    · simp only [Set.mulIndicator, Set.mem_setOf_eq, hv, not_false_eq_true, if_true, Φv, if_false]
      rw [integral_indicator (hL v)]
      simp [Measure.real]
  rw [e] at h1
  have h2 := hasProd_ofReal_of_complex (fun v => by
    by_cases hv : v ∈ S <;> simp [Set.mulIndicator, hv]) h1
  have e2 : (fun v => ENNReal.ofReal ({v | v ∉ S}.mulIndicator
      (fun v => (m v (latV b v)).toReal) v)) = {v | v ∉ S}.mulIndicator (fun v => m v (latV b v)) := by
    funext v
    by_cases hv : v ∈ S
    · simp [Set.mulIndicator, hv]
    · simp [Set.mulIndicator, hv, ENNReal.ofReal_toReal (hfin v)]
  rw [e2] at h2
  exact ⟨_, ENNReal.ofReal_ne_top, (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ S})).2 h2⟩

theorem repr_change {F E : Type} [Field F] [Field E] [Algebra F E] {d d' : ℕ}
    (R : Type) [CommRing R] [Algebra F R] (b : Module.Basis (Fin d) F E)
    (b' : Module.Basis (Fin d') F E) (y : R ⊗[F] E) (k' : Fin d') :
    (Algebra.TensorProduct.basis R b').repr y k' =
      ∑ k, (Algebra.TensorProduct.basis R b).repr y k * algebraMap F R (b'.repr (b k) k') := by
  have hE : ∀ e : E, b'.repr e k' = ∑ k, b.repr e k * b'.repr (b k) k' := fun e => by
    conv_lhs => rw [← b.sum_repr e]

    simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>

    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, hE,
    map_sum, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_mul, mul_assoc]
  | add x y hx hy =>
    rw [map_add (f := _), Finsupp.add_apply, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add (f := _), Finsupp.add_apply, add_mul]

theorem latCofin_holds : LatCofin := by
  intro F E _ _ _ _ a M d d' b b'
  have key : ∀ x : F, ∀ᶠ v in Filter.cofinite,
      algebraMap F (Fv F v) x ∈ (v.adicCompletionIntegers F : Set (Fv F v)) := fun x =>
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2
  have h1 : ∀ᶠ v in Filter.cofinite, ∀ k k', algebraMap F (Fv F v) (b'.repr (b k) k') ∈
      (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun k' => key _
  have h2 : ∀ᶠ v in Filter.cofinite, ∀ k' k, algebraMap F (Fv F v) (b.repr (b' k') k) ∈
      (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Filter.eventually_all.2 fun k' => Filter.eventually_all.2 fun k => key _
  filter_upwards [h1, h2] with v hv1 hv2
  ext Y
  simp only [latV, Set.mem_setOf_eq]
  constructor
  · intro hY x i k'
    rw [repr_change (Fv F v) b b']
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hY x i k) (hv1 k k')
  · intro hY x i k
    rw [repr_change (Fv F v) b' b]
    exact Subring.sum_mem _ fun k' _ => Subring.mul_mem _ (hY x i k') (hv2 k' k)

theorem rpTail_holds : RPTail := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet fibV d b hSB hmult
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact rpTail_gen b (fun v => fibV v (hermOf (Fv F v) σ (gramE σ J X0) hT)) hSB hmult

end PI.VolStabS.RestrProdA
end
end

section

noncomputable section

namespace PI.VolStabS.RestrProdG

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Maps

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S]

theorem map_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ z) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR S σ (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

theorem map_inclR (f : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR, Algebra.TensorProduct.map_tmul]

theorem map_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (x y : Fin n) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (gramR R σ J X x y) =
      gramR S σ J (fun x i => Algebra.TensorProduct.map f (AlgHom.id F E) (X x i)) x y := by

  simp only [gramR, hR, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, map_sigR,
  map_inclR]

end Maps

theorem t2_tensor_product {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type)
    [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    T2Space (R ⊗[F] E) := by
  let b := Module.finBasis F E
  refine T2Space.of_injective_continuous
    (f := fun y : R ⊗[F] E => fun k => PositiveNearLattice.crd b R y k) ?_
    (continuous_pi fun k => PositiveNearLattice.continuous_crd b R k)
  intro y y' h
  have h' : ∀ k, PositiveNearLattice.crd b R y k = PositiveNearLattice.crd b R y' k := fun k => congrFun h k
  rw [PositiveNearLattice.eq_sum_crd b R y, PositiveNearLattice.eq_sum_crd b R y']
  simp only [h']

theorem rpGram_holds : RPGram := by
  intro F E _ _ _ _ _ σ M J a T
  let b := Module.finBasis F E
  refine ⟨?_, ?_, fun v => ?_, ?_⟩
  · have : T2Space (AF F ⊗[F] E) := t2_tensor_product (AF F)
    have : T2Space (Matrix (Fin a) (Fin a) (AF F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → AF F ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (AF F) σ J)).isOpen_compl.measurableSet
  · have : T2Space (Ainf F ⊗[F] E) := t2_tensor_product (Ainf F)
    have : T2Space (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Ainf F ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (Ainf F) σ J)).measurableSet
  · have : LocallyCompactSpace (Fv F v) := locallyCompact_Fv F v
    have : T2Space (Fv F v ⊗[F] E) := t2_tensor_product (Fv F v)
    have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (Fv F v) σ J)).measurableSet
  · intro X hI hV
    have key : ∀ w w' : AF F ⊗[F] E,
        Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) w =
          Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) w' →
        (∀ v, Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
            (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w) =
          Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
            (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w')) → w = w' := by
      intro w w' h1 h2
      rw [PositiveNearLattice.eq_sum_crd b (AF F) w, PositiveNearLattice.eq_sum_crd b (AF F) w']
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      have e1 := congrArg (fun u => PositiveNearLattice.crd b (Ainf F) u k) h1
      simp only [PositiveNearLattice.crd_map] at e1
      refine Prod.ext e1 (FiniteAdeleRing.ext (K := F) fun v => ?_)
      have e2 := congrArg (fun u => PositiveNearLattice.crd b (Fv F v) u k) (h2 v)
      simp only [PositiveNearLattice.crd_map] at e2
      exact e2
    funext x y
    refine key _ _ ?_ fun v => ?_
    · rw [map_gramR, Matrix.map_apply, map_inclR]
      exact congrFun (congrFun hI x) y
    · rw [map_gramR, map_gramR, Matrix.map_apply, map_inclR, map_inclR]
      exact congrFun (congrFun (hV v) x) y

end PI.VolStabS.RestrProdG
end
end
