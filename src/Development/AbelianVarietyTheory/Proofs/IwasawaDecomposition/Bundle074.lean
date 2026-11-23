module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle069
public import Formalism.ConjugateSelfDual.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle067
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle049
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Formalism.SharpRestriction.LevelLetterCocycles.DataN

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx Matrix
open scoped TensorProduct NNReal ENNReal Pointwise Kronecker

namespace GlobalTheory.GaugeEx.ModDet

theorem induction_pi {S : Type} [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι] {K : ι → Type}
    [∀ k, Field (K k)] (e : S ≃+* ∀ k, K k) {κ : Type} [Fintype κ] [DecidableEq κ]
    (P : Matrix κ κ S → Prop) (hd : ∀ d : κ → S, (∀ i, IsUnit (d i)) → P (diagonal d))
    (ht : ∀ (i j : κ) (c : S), i ≠ j → P (transvection i j c))
    (hm : ∀ A B, P A → P B → P (A * B)) (g : Matrix κ κ S) (hg : IsUnit g.det) : P g := by
  let E : Matrix κ κ S ≃+* ∀ k, Matrix κ κ (K k) := e.mapMatrix.trans Matrix.piRingEquiv
  have hE : ∀ A k i j, E A k i j = e (A i j) k := fun _ _ _ _ => rfl
  have h1 : ∀ k (A : Matrix κ κ (K k)), A.det ≠ 0 → P (E.symm (Pi.mulSingle k A)) := by
    intro k A hA
    apply diagonal_transvection_induction_of_det_ne_zero
      (fun A => P (E.symm (Pi.mulSingle k A))) A hA
    · intro D hD
      rw [det_diagonal] at hD
      have : E.symm (Pi.mulSingle k (diagonal D)) =
          diagonal fun i => e.symm (Pi.mulSingle k (D i)) := by
        rw [RingEquiv.symm_apply_eq]
        funext k'
        ext i j
        rw [hE]
        by_cases hk : k' = k
        · subst hk
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij]
        · by_cases hij : i = j
          · subst hij; simp [hk]
          · simp [hij, hk]
      rw [this]
      refine hd _ fun i => ?_
      have : IsUnit (D i) := (Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)).isUnit
      exact (this.map (MonoidHom.mulSingle K k)).map e.symm
    · intro t
      obtain ⟨a, b, hab, c⟩ := t
      have : E.symm (Pi.mulSingle k (transvection a b c)) =
          transvection a b (e.symm (Pi.single k c)) := by
        rw [RingEquiv.symm_apply_eq]
        funext k'
        ext i j
        rw [hE]
        by_cases hk : k' = k
        · subst hk
          simp [transvection, Matrix.one_apply, Matrix.single, apply_ite e, ite_apply]
        · simp [transvection, Matrix.one_apply, Matrix.single, apply_ite e, ite_apply, hk]
      rw [TransvectionStruct.toMatrix_mk, this]
      exact ht _ _ _ hab
    · intro A B _ _ hA hB
      rw [Pi.mulSingle_mul, map_mul]
      exact hm _ _ hA hB
  have hdet : ∀ k, (E g k).det ≠ 0 := by
    intro k
    have : E g k = ((Pi.evalRingHom K k).comp e.toRingHom).mapMatrix g := rfl
    rw [this, ← RingHom.map_det]
    exact (hg.map _).ne_zero
  have h2 : ∀ s : Finset ι, P (E.symm fun k => if k ∈ s then E g k else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (fun k => if k ∈ (∅ : Finset ι) then E g k else 1) = 1 := by funext k; simp
      rw [this, map_one, ← diagonal_one]
      exact hd _ fun _ => isUnit_one
    | insert a s ha ih =>
      have : (fun k => if k ∈ insert a s then E g k else 1) =
          Pi.mulSingle a (E g a) * fun k => if k ∈ s then E g k else 1 := by
        funext k
        by_cases hk : k = a
        · subst hk; simp [ha]
        · simp [hk]
      rw [this, map_mul]
      exact hm _ _ (h1 a _ (hdet a)) ih
  simpa using h2 Finset.univ

section

variable {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [LocallyCompactSpace S]

theorem modu_coe (u : Sˣ) : modu S u = distribHaarChar S u := by
  simp [modu]

theorem modu_mul {a b : S} (ha : IsUnit a) (hb : IsUnit b) : modu S (a * b) = modu S a * modu S b := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  rw [← Units.val_mul, modu_coe, modu_coe, modu_coe, map_mul]

theorem modu_pow {a : S} (ha : IsUnit a) (n : ℕ) : modu S (a ^ n) = modu S a ^ n := by
  obtain ⟨a, rfl⟩ := ha
  rw [← Units.val_pow_eq_pow_val, modu_coe, modu_coe, map_pow]

variable [T2Space S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]

theorem smul_map_mulVec_pi [IsArtinianRing S] [IsReduced S] (ν : Measure S) [ν.IsAddHaarMeasure]
    {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ S) (hM : IsUnit M.det) :
    (modu S M.det : ℝ≥0∞) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) =
      Measure.pi fun _ : κ => ν := by
  classical
  have hm : ∀ A : Matrix κ κ S, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  letI := Fintype.ofFinite (MaximalSpectrum S)
  letI : ∀ m : MaximalSpectrum S, Field (S ⧸ m.asIdeal) := fun m =>
    haveI := m.isMaximal
    Ideal.Quotient.field m.asIdeal
  refine (induction_pi (IsArtinianRing.equivPi S).toRingEquiv (fun M : Matrix κ κ S => IsUnit M.det ∧
    (modu S M.det : ℝ≥0∞) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) =
      Measure.pi fun _ : κ => ν) ?_ ?_ ?_ M hM).2
  · intro D A
    have hu' : (diagonal D).det = ((∏ i, (A i).unit : Sˣ) : S) := by simp
    refine ⟨hu' ▸ Units.isUnit _, (Measure.pi_eq fun s hs => ?_).symm⟩
    rw [Measure.smul_apply, Measure.map_apply (hm _) (MeasurableSet.univ_pi hs)]
    have : ((diagonal D).mulVec ⁻¹' Set.pi Set.univ fun i : κ => s i) =
        Set.pi Set.univ fun i : κ => ((A i).unit)⁻¹ • s i := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi, mulVec_diagonal]
      exact forall_congr' fun i => (Set.mem_inv_smul_set_iff (a := (A i).unit)).symm
    rw [this, Measure.pi_pi, hu', modu_coe, map_prod, smul_eq_mul]
    change ENNReal.ofNNRealHom (∏ i, distribHaarChar S (A i).unit) * _ = _
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    change ((distribHaarChar S (A i).unit : ℝ≥0) : ℝ≥0∞) * _ = _
    rw [distribHaarChar_mul, smul_inv_smul]
  · intro a b c hab
    rw [det_transvection_of_ne _ _ hab]
    refine ⟨isUnit_one, ?_⟩
    rw [← Units.val_one, modu_coe, map_one, ENNReal.coe_one, one_smul]
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
    simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
    rw [lintegral_map (measurable_one.indicator h2s) (hm _)]
    refine lintegral_eq_of_lmarginal_eq {a} ((measurable_one.indicator h2s).comp (hm _))
      (measurable_one.indicator h2s) ?_
    simp_rw [lmarginal_singleton]
    ext x
    simp [transvection, add_mulVec, single_mulVec, hab.symm, ← Function.update_add,
      lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x a xᵢ)]
  · rintro A B ⟨hA, IHA⟩ ⟨hB, IHB⟩
    have e : (A * B).mulVec = A.mulVec ∘ B.mulVec := funext fun x => (mulVec_mulVec x A B).symm
    rw [det_mul]
    refine ⟨hA.mul hB, ?_⟩
    rw [modu_mul hA hB, ENNReal.coe_mul, mul_smul, e, ← Measure.map_map (hm _) (hm _),
      ← Measure.map_smul, IHB, IHA]
    exact (hm A).aemeasurable

end

theorem tupMeas_eq_map {S : Type} [MeasurableSpace S] (lam : Measure S) [SigmaFinite lam] (n M : ℕ) :
    tupMeas lam n M = (Measure.pi fun _ : Fin n × Fin M => lam).map Function.curry := by
  have hu : Measurable (Function.uncurry : (Fin n → Fin M → S) → Fin n × Fin M → S) :=
    Measurable.of_eval fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hc : Measurable (Function.curry : (Fin n × Fin M → S) → Fin n → Fin M → S) :=
    Measurable.of_eval fun a => Measurable.of_eval fun i => measurable_pi_apply (a, i)
  have : (Measure.pi fun _ : Fin n × Fin M => lam) = (tupMeas lam n M).map Function.uncurry := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hu (MeasurableSet.univ_pi hs)]
    have : (Function.uncurry ⁻¹' Set.pi Set.univ s : Set (Fin n → Fin M → S)) =
        Set.pi Set.univ fun a => Set.pi Set.univ fun i => s (a, i) := by
      ext X
      simp [Function.uncurry]
    rw [this, tupMeas, Measure.pi_pi, Fintype.prod_prod_type]
    simp_rw [Measure.pi_pi]
  rw [this, Measure.map_map hc hu]
  exact Measure.map_id.symm

theorem tupMeas_lrAct : ∀ (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S], IsArtinianRing S → IsReduced S → ∀ (lam : Measure S), lam.IsAddHaarMeasure → ∀ (n M : ℕ) (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S), IsUnit g.det → IsUnit γ.det → tupMeas lam n M = (modu S g.det ^ n * modu S γ.det ^ M) • (tupMeas lam n M).map (lrAct g γ) := by
  intro S _ _ _ _ _ _ _ _ _ _ lam _ n M g γ hg hγ
  have hc : Measurable (Function.curry : (Fin n × Fin M → S) → Fin n → Fin M → S) :=
    Measurable.of_eval fun a => Measurable.of_eval fun i => measurable_pi_apply (a, i)
  have hl : Measurable (lrAct g γ) := by
    refine Continuous.measurable (continuous_pi fun a => continuous_const.matrix_mulVec ?_)
    fun_prop
  have hdet : (γᵀ ⊗ₖ g).det = γ.det ^ M * g.det ^ n := by simp [det_kronecker]
  have key := smul_map_mulVec_pi lam (γᵀ ⊗ₖ g) (hdet ▸ (hγ.pow M).mul (hg.pow n))
  rw [hdet, modu_mul (hγ.pow M) (hg.pow n), modu_pow hγ, modu_pow hg, mul_comm] at key
  have hcomm : lrAct g γ ∘ Function.curry = Function.curry ∘ (γᵀ ⊗ₖ g).mulVec := by
    funext X a i
    simp only [Function.comp, lrAct, Function.curry, mulVec, dotProduct, Fintype.sum_prod_type,
      kroneckerMap_apply, transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hm : Measurable (γᵀ ⊗ₖ g).mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [tupMeas_eq_map, Measure.map_map hl hc, hcomm, ← Measure.map_map hc hm, ← Measure.map_smul]
  · exact congrArg _ key.symm
  · exact hc.aemeasurable

end GlobalTheory.GaugeEx.ModDet

end
end

section

noncomputable section

namespace GlobalTheory.GaugeEx

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct NNReal ENNReal

section BaseMap

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem qloc_trace_tmul [FiniteDimensional F E] (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  have h1 : (r ⊗ₜ[F] e : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

variable (φ : R →ₐ[F] R') (π : R ⊗[F] E →+* R' ⊗[F] E)
  (hπ : ∀ r e, π (r ⊗ₜ[F] e) = φ r ⊗ₜ[F] e)
include hπ

theorem qloc_trace [FiniteDimensional F E] (z : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (π z) = φ (Algebra.trace R (R ⊗[F] E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rw [hπ, qloc_trace_tmul, qloc_trace_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem qloc_sig (σ : E →ₐ[F] E) (z : R ⊗[F] E) : sigR R' σ (π z) = π (sigR R σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hπ]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem qloc_incl (e : E) : π (inclR R e) = inclR R' e := by
  simp [inclR, hπ]

theorem qloc_q [FiniteDimensional F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (z : Fin M → R ⊗[F] E) : qR R' σ J (fun i => π (z i)) = φ (qR R σ J z) := by
  have h : hR R' σ J (fun i => π (z i)) (fun i => π (z i)) = π (hR R σ J z z) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, qloc_sig φ π hπ,
      qloc_incl φ π hπ]
  rw [qR, qR, h, qloc_trace φ π hπ, map_mul, AlgHom.commutes]

theorem qloc_group (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) :
    ∃ g' : HA R' σ J, (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π := by
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val * JR R J * (HA.mat R σ J g).val = JR R J :=
    Subtype.property (p := fun x => x ∈ HR R σ J) g
  have hJ : (JR R J).map π = JR R' J := by
    ext i j
    exact qloc_incl φ π hπ _
  have hc : Formalism.UG.cT (sigR R' σ) ((HA.mat R σ J g).val.map π) =
      (Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val).map π := by
    ext i j
    exact qloc_sig φ π hπ σ _
  have hm : Formalism.UG.bc π (HA.mat R σ J g) ∈ HR R' σ J := by
    change Formalism.UG.cT (sigR R' σ) ((HA.mat R σ J g).val.map π) * JR R' J *
      ((HA.mat R σ J g).val.map π) = JR R' J
    rw [hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  exact ⟨(⟨_, hm⟩ : HR R' σ J), rfl⟩

end BaseMap

theorem qloc_adele_ext {F : Type} [Field F] [NumberField F] (a b : AF F)
    (h1 : fstA F a = fstA F b) (h2 : ∀ v, evalV F v (sndA F a) = evalV F v (sndA F b)) : a = b := by
  refine Prod.ext h1 ?_
  exact FiniteAdeleRing.ext F fun v => h2 v

theorem q_and_unitary_local_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), (∀ (z : Fin M → AF F ⊗[F] E) (β : F), qR (AF F) σ J z = algebraMap F (AF F) β ↔ qR (Ainf F) σ J (fun i => prInf (z i)) = algebraMap F (Ainf F) β ∧ ∀ v : HeightOneSpectrum (𝓞 F), qR (Fv F v) σ J (fun i => prV v (z i)) = algebraMap F (Fv F v) β) ∧ ∀ g : HA (AF F) σ J, (∃ gi : HA (Ainf F) σ J, (HA.mat (Ainf F) σ J gi).val = (HA.mat (AF F) σ J g).val.map prInf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∃ gv : HA (Fv F v) σ J, (HA.mat (Fv F v) σ J gv).val = (HA.mat (AF F) σ J g).val.map (prV v) := by
  intro F E _ _ _ _ _ σ M J
  have hI : ∀ (r : AF F) (e : E), prInf (r ⊗ₜ[F] e) = fstA F r ⊗ₜ[F] e := fun r e => rfl
  have hV : ∀ v (r : AF F) (e : E),
      prV v (r ⊗ₜ[F] e) = ((evalV F v).comp (sndA F)) r ⊗ₜ[F] e := fun v r e => rfl
  refine ⟨fun z β => ?_, fun g => ⟨qloc_group _ _ hI σ J g, fun v => qloc_group _ _ (hV v) σ J g⟩⟩
  simp only [qloc_q _ _ hI, qloc_q _ _ (hV _)]
  constructor
  · intro h
    rw [h]
    exact ⟨AlgHom.commutes _ _, fun v => AlgHom.commutes _ _⟩
  · rintro ⟨h1, h2⟩
    refine qloc_adele_ext _ _ (by rw [h1, AlgHom.commutes]) fun v => ?_
    rw [AlgHom.commutes, AlgHom.commutes]
    exact h2 v

end GlobalTheory.GaugeEx
end
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.ProdScale

theorem finite_mulSupport_sub {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite)
    (p : ι → Prop) : (Function.mulSupport fun v : {v // p v} => (r v.1 : ℝ)).Finite := by
  refine (hr.preimage (f := (Subtype.val : {v // p v} → ι)) Subtype.val_injective.injOn).subset ?_
  intro v hv h
  exact hv (by simp [h])

theorem summable_scale {ι : Type} (f : ι → ℝ) (r : ι → ℝ≥0) (hf : Summable fun v => |f v - 1|)
    (hr : (Function.mulSupport r).Finite) : Summable fun v => |r v * f v - 1| := by
  refine hf.congr_cofinite ?_
  filter_upwards [hr.compl_mem_cofinite] with v hv
  have : r v = 1 := by simpa using hv
  simp [this]

theorem finprod_eq {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite) (S : Finset ι) :
    ((∏ᶠ v, r v : ℝ≥0) : ℝ) = (∏ v ∈ S, (r v : ℝ)) * ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
  have h0 : (Function.mulSupport fun v => (r v : ℝ)).Finite :=
    hr.subset fun v hv h => hv (by simp [h])
  have h1 : ((∏ᶠ v, r v : ℝ≥0) : ℝ) = ∏ᶠ v, (r v : ℝ) :=
    NNReal.toRealHom.toMonoidHom.map_finprod hr
  rw [h1, ← tprod_eq_finprod (L := SummationFilter.unconditional ι) h0, ← Finset.tprod_subtype' S (fun v => (r v : ℝ))]
  exact (Multipliable.tprod_mul_tprod_compl (f := fun v => (r v : ℝ)) (s := (S : Set ι))
    (multipliable_of_hasFiniteMulSupport (finite_mulSupport_sub r hr _))
    (multipliable_of_hasFiniteMulSupport (finite_mulSupport_sub r hr _))).symm

theorem tprod_scale {ι : Type} (f : ι → ℝ) (r : ι → ℝ≥0) (hf : Summable fun v => |f v - 1|)
    (hr : (Function.mulSupport r).Finite) (S : Finset ι) :
    ∏' v : {v // v ∉ S}, ((r v.1 : ℝ) * f v.1) =
      (∏' v : {v // v ∉ S}, (r v.1 : ℝ)) * ∏' v : {v // v ∉ S}, f v.1 := by
  refine Multipliable.tprod_mul
    (multipliable_of_hasFiniteMulSupport (finite_mulSupport_sub r hr _)) ?_
  have h := multipliable_one_add_of_summable (f := fun v : {v // v ∉ S} => f v.1 - 1)
    (hf.subtype (fun v => v ∉ S))
  simpa using h

theorem finprod_ennreal {ι : Type} (r : ι → ℝ≥0) (hr : (Function.mulSupport r).Finite)
    (S : Finset ι) :
    ∃ c : ℝ≥0, (∏ᶠ v, r v) = (∏ v ∈ S, r v) * c ∧ (c : ℝ) = ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
  have h0 : 0 ≤ ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := by
    rw [tprod_eq_finprod (finite_mulSupport_sub r hr _)]
    exact finprod_nonneg fun v => (r v.1).2
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (c : ℝ) = ∏' v : {v // v ∉ S}, (r v.1 : ℝ) := ⟨⟨_, h0⟩, rfl⟩
  refine ⟨c, ?_, hc⟩
  apply NNReal.coe_injective
  rw [finprod_eq r hr S, ← hc]
  simp

theorem isProd_smul (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (ν : Measure (Fin n → Fin M → AF F ⊗[F] E)) (mi : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ri : ℝ≥0)
    (r : HeightOneSpectrum (𝓞 F) → ℝ≥0) (h : IsProd b ν mi mv)
    (hr : (Function.mulSupport r).Finite) :
    IsProd b ((ri * ∏ᶠ v, r v) • ν) (ri • mi) (fun v => r v • mv v) := by
  obtain ⟨⟨hi, hv, hs⟩, hf⟩ := h
  have key : ∀ v, ((r v • mv v) (latV b v)).toReal = r v * (mv v (latV b v)).toReal := by
    intro v
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]
  refine ⟨⟨inferInstance, fun v => inferInstance, ?_⟩, ?_⟩
  · simp only [key]
    exact summable_scale _ r hs hr
  · intro S fi fv hfi hfv
    obtain ⟨c, hc, hc'⟩ := finprod_ennreal r hr S
    have ht : tailProd b (fun v => r v • mv v) S = c * tailProd b mv S := by
      unfold tailProd
      simp only [key]
      rw [tprod_scale (fun v => (mv v (latV b v)).toReal) r hs hr S, ← hc',
        ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    rw [Measure.restrict_smul, lintegral_smul_measure, hf S fi fv hfi hfv, ht, hc]
    simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib]
    push_cast
    ring

end GlobalTheory.GaugeEx.ProdScale
end

section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem summable_abs_mul_sub_one {ι : Type} {a a' : ι → ℝ} (ha : Summable fun v => |a v - 1|)
    (ha' : Summable fun v => |a' v - 1|) : Summable fun v => |a v * a' v - 1| := by
  have h1 : Summable fun v => |a v - 1| * |a' v - 1| := by
    refine Summable.of_nonneg_of_le (fun v => by positivity) (fun v => ?_)
      (ha.mul_right (∑' w, |a' w - 1|))
    exact mul_le_mul_of_nonneg_left (ha'.le_tsum v fun w _ => abs_nonneg _) (abs_nonneg _)
  refine Summable.of_nonneg_of_le (fun v => abs_nonneg _) (fun v => ?_) ((h1.add ha).add ha')
  have : a v * a' v - 1 = (a v - 1) * (a' v - 1) + (a v - 1) + (a' v - 1) := by ring
  rw [this, ← abs_mul]
  exact abs_add_three _ _ _

theorem multipliable_subtype_of_summable_abs {ι : Type} {a : ι → ℝ}
    (ha : Summable fun v => |a v - 1|) (p : ι → Prop) :
    Multipliable fun v : {v // p v} => a v.1 := by
  have h : Summable fun v : {v // p v} => (a v.1 - 1) :=
    (Summable.of_abs ha).comp_injective Subtype.val_injective
  have := Real.multipliable_one_add_of_summable h
  simpa using this

theorem tprod_nonneg_of_multipliable {ι : Type} {a : ι → ℝ} (ha : Multipliable a)
    (h0 : ∀ v, 0 ≤ a v) : 0 ≤ ∏' v, a v :=
  ge_of_tendsto' ha.hasProd fun _ => Finset.prod_nonneg fun v _ => h0 v

theorem tailProd_mul_of_mass_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n₁ M₁ n₂ M₂ n₃ M₃ : ℕ) (mi : Measure (Fin n₁ → Fin M₁ → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₁ → Fin M₁ → Fv F v ⊗[F] E)) (mi' : Measure (Fin n₂ → Fin M₂ → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₂ → Fin M₂ → Fv F v ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₃ → Fin M₃ → Fv F v ⊗[F] E)) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → Conv b mi' mv' → (∀ v ∉ S₀, Nv v (latV b v) = mv v (latV b v) * mv' v (latV b v)) → (Summable fun v => |(Nv v (latV b v)).toReal - 1|) ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S → tailProd b Nv S = tailProd b mv S * tailProd b mv' S := by
  intro F E _ _ _ _ _ d b n₁ M₁ n₂ M₂ n₃ M₃ mi mv mi' mv' Nv S₀ h h' hN
  refine ⟨?_, fun S hS => ?_⟩
  · refine (summable_abs_mul_sub_one h.2.2 h'.2.2).congr_cofinite ?_
    filter_upwards [S₀.eventually_cofinite_notMem] with v hv
    rw [hN v hv, ENNReal.toReal_mul]
  · have m := multipliable_subtype_of_summable_abs h.2.2 (fun v => v ∉ S)
    have m' := multipliable_subtype_of_summable_abs h'.2.2 (fun v => v ∉ S)
    unfold tailProd
    rw [← ENNReal.ofReal_mul (tprod_nonneg_of_multipliable m fun _ => ENNReal.toReal_nonneg),
      ← m.tprod_mul m']
    congr 1
    refine tprod_congr fun v => ?_
    rw [hN v.1 (fun hv => v.2 (hS hv)), ENNReal.toReal_mul]

end GlobalTheory.GaugeEx
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

theorem _root_.GlobalTheory.T.character_globalArtin_units_trivial_uniformiser_power : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω] (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK → ∀ (ρ : Gab K Ω →* Gab E Ω), (∀ τ : G K Ω, ρ (toAb K Ω τ) = toAb E Ω (τ.restrictScalars E)) → ∀ (B : Type) [CommGroup B] (χ : Gab E Ω →* B) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → (∀ x, IsUnitAt v x → χ (art (localIdele E v x)) = 1) → (∀ x, IsUnitAt w x → χ (ρ (artK (localIdele K w x))) = 1) ∧ ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → χ (ρ (artK (localIdele K w x))) = χ (art (localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (𝓞 E) := by
  first | exact @GlobalTheory.NormCompat.chi_artin_restrict | exact GlobalTheory.NormCompat.chi_artin_restrict | (intros; apply GlobalTheory.NormCompat.chi_artin_restrict <;> assumption)
end

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

theorem _root_.GlobalTheory.T.exists_finset_image_mem_subring : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (iq : FractionRing O →+* Qbar l), (∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) → ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) → (↑T ⊆ (R : Set (Qbar l))) → ∀ x : O, iq (algebraMap O (FractionRing O) x) ∈ R := by
  first | exact @GlobalTheory.image_finite_mem_subring | exact GlobalTheory.image_finite_mem_subring | (intros; apply GlobalTheory.image_finite_mem_subring <;> assumption)
end
