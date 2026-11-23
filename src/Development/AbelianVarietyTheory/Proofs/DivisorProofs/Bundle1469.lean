module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodingerOper
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

open scoped RestrictedProduct

namespace GlobalTheory.InvIdem

variable {F : Type} [Field F] [NumberField F]

def ci (w : InfinitePlace F) : AF F →+* w.Completion :=
  (Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (fstA F).toRingHom

def cf (v : HeightOneSpectrum (𝓞 F)) : AF F →+* Fv F v :=
  (evalV F v).toRingHom.comp (sndA F).toRingHom

theorem continuous_ci (w : InfinitePlace F) : Continuous (ci (F := F) w) :=
  (continuous_apply w).comp continuous_fst

theorem continuous_cf (v : HeightOneSpectrum (𝓞 F)) : Continuous (cf (F := F) v) :=
  (RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) v).comp
    continuous_snd

theorem ext_c {a b : AF F} (h1 : ∀ w, ci w a = ci w b) (h2 : ∀ v, cf v a = cf v b) : a = b :=
  Prod.ext (funext h1) (RestrictedProduct.ext _ _ h2)


open Classical in
def sglI (w : InfinitePlace F) (c : w.Completion) : AF F :=
  ((Pi.single w c : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

def sglF (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) : AF F :=
  ((0 : InfiniteAdeleRing F), singleV F v c)

theorem ci_apply (w : InfinitePlace F) (a : AF F) : ci w a = a.1 w := rfl
theorem cf_apply (v : HeightOneSpectrum (𝓞 F)) (a : AF F) : cf v a = a.2 v := rfl

theorem ci_sglI_self (w : InfinitePlace F) (c : w.Completion) : ci w (sglI w c) = c := by
  classical
  rw [ci_apply]; simp [sglI]

theorem ci_sglI_ne {w u : InfinitePlace F} (h : u ≠ w) (c : w.Completion) : ci u (sglI w c) = 0 := by
  classical
  rw [ci_apply]; simp [sglI, Pi.single_apply, h]

theorem cf_sglI (w : InfinitePlace F) (c : w.Completion) (v : HeightOneSpectrum (𝓞 F)) :
    cf v (sglI w c) = 0 := by
  rw [cf_apply]; rfl

theorem ci_sglF (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) (w : InfinitePlace F) :
    ci w (sglF v c) = 0 := by
  rw [ci_apply]; rfl

theorem cf_sglF_self (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) : cf v (sglF v c) = c := by
  classical
  show (singleV F v c) v = c
  unfold singleV
  exact RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v c

theorem cf_sglF_ne {v u : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (c : Fv F v) : cf u (sglF v c) = 0 := by
  classical
  show (singleV F v c) u = 0
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) c h

open Classical in
theorem continuous_sglI (w : InfinitePlace F) : Continuous (sglI (F := F) w) := by
  unfold sglI
  exact (continuous_single w).prodMk continuous_const

open Classical in
theorem continuous_sglF (v : HeightOneSpectrum (𝓞 F)) : Continuous (sglF (F := F) v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion F → Πʳ w : HeightOneSpectrum (𝓞 F),
      [w.adicCompletion F, w.adicCompletionIntegers F]_[Filter.principal ({v}ᶜ : Set _)] :=
    fun x => ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v x, by
      intro w hw
      have hw' : w ≠ v := hw
      simp only [Set.mem_ofPred_eq, Pi.single_eq_of_ne hw', SetLike.mem_coe]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2 (continuous_single v)
  exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hS).comp hf)

def invS (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (y : AF F) : AF F :=
  (∑ w ∈ S₁, sglI w (ci w y)⁻¹) + ∑ v ∈ S₂, sglF v (cf v y)⁻¹

variable {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))}

open Classical in
theorem ci_invS (y : AF F) (u : InfinitePlace F) :
    ci u (invS S₁ S₂ y) = if u ∈ S₁ then (ci u y)⁻¹ else 0 := by

  rw [invS, map_add (f := _), map_sum, map_sum]
  simp only [ci_sglF, Finset.sum_const_zero, add_zero]
  split_ifs with hu
  · rw [Finset.sum_eq_single_of_mem u hu (fun w _ hw => ci_sglI_ne (Ne.symm hw) _), ci_sglI_self]
  · exact Finset.sum_eq_zero fun w hw => ci_sglI_ne (fun h : u = w => hu (h ▸ hw)) _

open Classical in
theorem cf_invS (y : AF F) (u : HeightOneSpectrum (𝓞 F)) :
    cf u (invS S₁ S₂ y) = if u ∈ S₂ then (cf u y)⁻¹ else 0 := by

  rw [invS, map_add (f := _), map_sum, map_sum]
  simp only [cf_sglI, Finset.sum_const_zero, zero_add]
  split_ifs with hu
  · rw [Finset.sum_eq_single_of_mem u hu (fun w _ hw => cf_sglF_ne (Ne.symm hw) _), cf_sglF_self]
  · exact Finset.sum_eq_zero fun w hw => cf_sglF_ne (fun h : u = w => hu (h ▸ hw)) _

theorem invS_mul {ε : AF F} (hε : IsPlacesIdem S₁ S₂ ε) {y z : AF F} (hyz : y * z = 1) :
    invS S₁ S₂ (ε * y) = ε * z := by
  obtain ⟨h1, h2, h3, h4⟩ := hε
  have hi : ∀ w, ci w y * ci w z = 1 := fun w => by rw [← map_mul (ci w), hyz, map_one]
  have hf : ∀ v, cf v y * cf v z = 1 := fun v => by rw [← map_mul (cf v), hyz, map_one]
  refine ext_c (fun w => ?_) (fun v => ?_)
  · rw [ci_invS, map_mul, map_mul]
    have e1 : ci w ε = fstA F ε w := rfl
    split_ifs with hw
    · rw [e1, h1 w hw, one_mul, one_mul]; exact inv_eq_of_mul_eq_one_right (hi w)
    · rw [e1, h2 w hw, zero_mul]
  · rw [cf_invS, map_mul, map_mul]
    have e1 : cf v ε = evalV F v (sndA F ε) := rfl
    split_ifs with hv
    · rw [e1, h3 v hv, one_mul, one_mul]; exact inv_eq_of_mul_eq_one_right (hf v)
    · rw [e1, h4 v hv, zero_mul]

theorem continuousAt_invS {y : AF F} (h1 : ∀ w ∈ S₁, ci w y ≠ 0) (h2 : ∀ v ∈ S₂, cf v y ≠ 0) :
    ContinuousAt (invS S₁ S₂) y := by
  unfold invS
  refine ContinuousAt.add ?_ ?_
  · exact tendsto_finsetSum S₁ fun w hw =>
      ((continuous_sglI w).continuousAt.comp ((continuousAt_inv₀ (h1 w hw)).comp (continuous_ci w).continuousAt))
  · exact tendsto_finsetSum S₂ fun v hv =>
      ((continuous_sglF v).continuousAt.comp ((continuousAt_inv₀ (h2 v hv)).comp (continuous_cf v).continuousAt))

end GlobalTheory.InvIdem

namespace GlobalTheory.InvIdem

theorem inv_cont : ∀ (F : Type) [Field F] [NumberField F] (S₁ : Finset (InfinitePlace F))
    (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ∀ x : (AF F)ˣ, ∀ U : Set (AF F),
    U ∈ 𝓝 (ε * ((x⁻¹ : (AF F)ˣ) : AF F)) → ∃ V : Set (AF F), V ∈ 𝓝 (ε * (x : AF F)) ∧
      ∀ t : F, ε * algebraMap F (AF F) t ∈ V → (ε ≠ 0 → t ≠ 0) ∧ ε * algebraMap F (AF F) t⁻¹ ∈ U := by
  intro F _ _ S₁ S₂ ε hε x U hU
  have hx : invS S₁ S₂ (ε * (x : AF F)) = ε * ((x⁻¹ : (AF F)ˣ) : AF F) := invS_mul hε x.mul_inv
  have hci : ∀ w ∈ S₁, ci w (ε * (x : AF F)) ≠ 0 := by
    intro w hw h
    rw [map_mul, show ci w ε = fstA F ε w from rfl, hε.1 w hw, one_mul] at h
    have e := congrArg (ci w) x.mul_inv
    rw [map_mul, h, zero_mul, map_one] at e
    exact zero_ne_one e
  have hcf : ∀ v ∈ S₂, cf v (ε * (x : AF F)) ≠ 0 := by
    intro v hv h
    rw [map_mul, show cf v ε = evalV F v (sndA F ε) from rfl, hε.2.2.1 v hv, one_mul] at h
    have e := congrArg (cf v) x.mul_inv
    rw [map_mul, h, zero_mul, map_one] at e
    exact zero_ne_one e
  have hV1 : invS S₁ S₂ ⁻¹' U ∈ 𝓝 (ε * (x : AF F)) :=
    (continuousAt_invS hci hcf).preimage_mem_nhds (by rw [hx]; exact hU)
  have hV2 : {y : AF F | (∀ w ∈ S₁, ci w y ≠ 0) ∧ ∀ v ∈ S₂, cf v y ≠ 0} ∈ 𝓝 (ε * (x : AF F)) :=
    ((Filter.eventually_all_finset S₁).2 fun w hw => (continuous_ci w).continuousAt.eventually_ne (hci w hw)).and
      ((Filter.eventually_all_finset S₂).2 fun v hv => (continuous_cf v).continuousAt.eventually_ne (hcf v hv))
  refine ⟨_, Filter.inter_mem hV1 hV2, fun t ht => ?_⟩
  have htne : ε ≠ 0 → t ≠ 0 := by
    intro hε0 ht0
    subst ht0
    apply hε0
    have hB := ht.2
    simp only [Set.mem_setOf_eq, map_zero, mul_zero] at hB
    refine ext_c (fun w => ?_) (fun v => ?_)
    · rw [map_zero]
      exact hε.2.1 w fun hw => hB.1 w hw rfl
    · rw [map_zero]
      exact hε.2.2.2 v fun hv => hB.2 v hv rfl
  refine ⟨htne, ?_⟩
  by_cases hε0 : ε = 0
  · subst hε0
    have e := mem_of_mem_nhds hU
    rw [zero_mul] at e
    rwa [zero_mul]
  · have ht0 := htne hε0
    have e := invS_mul (y := algebraMap F (AF F) t) (z := algebraMap F (AF F) t⁻¹) hε
      (by rw [← map_mul, mul_inv_cancel₀ ht0, map_one])
    rw [← e]
    exact ht.1

end GlobalTheory.InvIdem
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section
namespace GlobalTheory

open Filter

theorem placesIdem_mem_nhds_one (F : Type) [Field F] [NumberField F] (U : Set (AF F)) (hU : U ∈ 𝓝 (1 : AF F)) :
    ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F),
      IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U := by
  classical
  let x : Finset (HeightOneSpectrum (𝓞 F)) → Π v : HeightOneSpectrum (𝓞 F),
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun T v => if v ∈ T then ⟨1, (v.adicCompletionIntegers F).one_mem⟩ else ⟨0, (v.adicCompletionIntegers F).zero_mem⟩
  let one' : Π v : HeightOneSpectrum (𝓞 F), ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => ⟨1, (v.adicCompletionIntegers F).one_mem⟩
  let sm := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  let e : Finset (HeightOneSpectrum (𝓞 F)) → AF F := fun T => ((1 : Ainf F), (sm (x T) : Af F))
  have hx : Tendsto x atTop (𝓝 one') := by
    rw [tendsto_pi_nhds]
    intro v
    apply tendsto_atTop_of_eventually_const (i₀ := {v})
    intro T hT
    simp [x, one', hT (Finset.mem_singleton_self v)]
  have h1 : (sm one' : Af F) = 1 := by
    ext v; rfl
  have he : Tendsto e atTop (𝓝 (1 : AF F)) := by
    have hc : Continuous sm := RestrictedProduct.isEmbedding_structureMap.continuous
    have h2 : Tendsto (fun T => (sm (x T) : Af F)) atTop (𝓝 (1 : Af F)) := by
      have h3 := (hc.tendsto one').comp hx
      rw [h1] at h3
      exact h3
    exact Tendsto.prodMk_nhds tendsto_const_nhds h2
  obtain ⟨T, hT⟩ := (he.eventually hU).exists
  refine ⟨Finset.univ, T, e T, ⟨?_, ?_, ?_, ?_⟩, hT⟩
  · intro w _; rfl
  · intro w hw; exact absurd (Finset.mem_univ w) hw
  · intro v hv
    show ((x T v : v.adicCompletion F)) = 1
    simp [x, hv]
  · intro v hv
    show ((x T v : v.adicCompletion F)) = 0
    simp [x, hv]

theorem placesIdem_tendsto_one : ∀ (F : Type) [Field F] [NumberField F], ∀ U : Set (AF F), U ∈ 𝓝 (1 : AF F) →
    ∃ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F),
      IsPlacesIdem S₁ S₂ ε ∧ ε ∈ U :=
  fun F _ _ U hU => placesIdem_mem_nhds_one F U hU

end GlobalTheory
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open GlobalTheory.Published.StrongApprox
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NormFin

variable {F : Type} [Field F] [NumberField F]

theorem af_ext {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y :=
  by
  apply RestrictedProduct.ext
  intro w
  exact h w

def iotaL (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] AF F where
  toFun a := pairA F 0 (singleV F v a)
  map_add' a b := by
    refine Prod.ext (by change (0 : Ainf F) = 0 + 0; simp) ?_
    change singleV F v (a + b) = singleV F v a + singleV F v b
    refine af_ext fun w => ?_
    rw [map_add (f := _)]
    by_cases hw : w = v
    · subst hw; simp only [evalV_single_same]
    · simp only [evalV_single_ne hw, add_zero]
  map_smul' c a := by
    refine Prod.ext (by change (0 : Ainf F) = c • 0; simp) ?_
    change singleV F v (c • a) = c • singleV F v a
    refine af_ext fun w => ?_
    rw [map_smul]
    by_cases hw : w = v
    · subst hw; simp only [evalV_single_same]
    · simp only [evalV_single_ne hw, smul_zero]

theorem iotaL_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    iotaL v (a * b) = iotaL v a * iotaL v b := by
  refine Prod.ext (by change (0 : Ainf F) = 0 * 0; simp) ?_
  change singleV F v (a * b) = singleV F v a * singleV F v b
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; simp only [evalV_single_same]
  · simp only [evalV_single_ne hw, mul_zero]

theorem idem_mul_iotaL (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) (a : Fv F v) :
    ε * iotaL v a = iotaL v a := by
  refine Prod.ext (by change fstA F ε * 0 = 0; simp) ?_
  change sndA F ε * singleV F v a = singleV F v a
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [hε.2.2.1 w (Finset.mem_singleton_self w), one_mul]
  · simp only [evalV_single_ne hw, mul_zero]

theorem iotaL_one (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) :
    iotaL v 1 = ε := by
  refine Prod.ext ?_ ?_
  · funext w
    exact (hε.2.1 w (Finset.notMem_empty w)).symm
  · change singleV F v 1 = sndA F ε
    refine af_ext fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [evalV_single_same, hε.2.2.1 w (Finset.mem_singleton_self w)]
    · rw [evalV_single_ne hw, hε.2.2.2 w (fun h => hw (Finset.mem_singleton.1 h))]

section Tensor

variable {E : Type} [Field E] [Algebra F E]

def phi (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  TensorProduct.map (iotaL v) LinearMap.id

theorem phi_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) :
    phi v (a ⊗ₜ[F] e) = iotaL v a ⊗ₜ[F] e := TensorProduct.map_tmul _ _ _ _

theorem phi_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v ⊗[F] E) :
    phi v (x * y) = phi v x * phi v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b f =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, phi_tmul, phi_tmul, phi_tmul, iotaL_mul,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => rw [mul_add, map_add (f := _), hy, hz, map_add (f := _), mul_add]
  | add x z hx hz => rw [add_mul, map_add (f := _), hx, hz, map_add (f := _), add_mul]

theorem phi_sig (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E) :
    phi v (sigR (Fv F v) σ x) = sigR (AF F) σ (phi v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, phi_tmul]
  | add x z hx hz => rw [map_add (f := _), map_add (f := _), hx, hz, map_add (f := _), map_add (f := _)]

theorem idem_mul_phi (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε)
    (x : Fv F v ⊗[F] E) : algebraMap (AF F) (AF F ⊗[F] E) ε * phi v x = phi v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, phi_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, idem_mul_iotaL v ε hε]
  | add x z hx hz => rw [map_add (f := _), mul_add, hx, hz]

theorem phi_inclR (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) (c : E) :
    phi v (inclR (Fv F v) c) = algebraMap (AF F) (AF F ⊗[F] E) ε * inclR (AF F) c := by
  change phi v ((1 : Fv F v) ⊗ₜ[F] c) = algebraMap (AF F) (AF F ⊗[F] E) ε * ((1 : AF F) ⊗ₜ[F] c)
  rw [phi_tmul, iotaL_one v ε hε, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Tensor

theorem idem_norm_eq_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlacesIdem ∅ {v} ε → ∀ c : E,
    (∃ t : Fv F v ⊗[F] E, t * sigR (Fv F v) σ t + inclR (Fv F v) c = 0) →
    ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  intro F E _ _ _ _ σ v ε hε c ⟨t, ht⟩
  refine ⟨phi v t, ?_⟩
  rw [← phi_sig, ← phi_mul, mul_add, idem_mul_phi v ε hε, ← phi_inclR v ε hε, ← map_add (f := _), ht, map_zero]

end GlobalTheory.NormFin
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

namespace GlobalTheory.SUSuppClosed

theorem isClosed_SUSupp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) : IsClosed (SUSupp σ J ε) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have hv : Continuous fun g : HA (AF F) σ J =>
      ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :=
    Units.continuous_val.comp (GlobalTheory.AdelicU.isEmbedding_matHom (AF F) σ J).continuous
  have h1 : IsClosed {g : HA (AF F) σ J | g ∈ SUAdelic σ J} := by
    simp only [StrongApprox.mem_SUAdelic]
    exact isClosed_eq hv.matrix_det continuous_const
  have h2 : IsClosed {g : HA (AF F) σ J | ∀ i j,
      algebraMap (AF F) (AF F ⊗[F] E) ε * (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j =
        (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    have hc : Continuous fun g : HA (AF F) σ J =>
        (((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j :=
      (hv.sub continuous_const).matrix_elem i j
    exact isClosed_eq (continuous_const.mul hc) hc
  exact h1.inter h2

end GlobalTheory.SUSuppClosed
end

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

theorem _root_.GlobalTheory.T.exists_symplecticLie_of_indefiniteUnitaryLie_rightAction : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) ∧
      ∀ (t : ℝ) c, NormedSpace.exp (t • Z) *ᵥ φ c = φ fun w => c w * (NormedSpace.exp (t • Y w))ᵀ := by
  first | exact @GlobalTheory.RealLift.SpLie.exists_sp_rightAct | exact GlobalTheory.RealLift.SpLie.exists_sp_rightAct | (intros; apply GlobalTheory.RealLift.SpLie.exists_sp_rightAct <;> assumption)
end

section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

theorem _root_.GlobalTheory.T.exists_oscillator_action_normalising_schrodingerOperators : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  first | exact @GlobalTheory.SchrodOsc.exists_osc | exact GlobalTheory.SchrodOsc.exists_osc | (intros; apply GlobalTheory.SchrodOsc.exists_osc <;> assumption)
end
