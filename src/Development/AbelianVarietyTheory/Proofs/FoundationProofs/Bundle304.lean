module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle299
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle133
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90IntegralIdelesOfMovedPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDiagonalDataOfSelfDualNeighbourTriple
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.RelOp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem kmap_eq_self (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) (hφ : ∀ f, φ f = f)
    (x : X.Khat l) : X.kmap l φ x = x := by
  have h1 : Units.map φ.toMonoidHom = MonoidHom.id X.Kˣ := by
    ext u; simp [hφ]
  have h2 : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)) :
      Additive X.Kˣ →ₗ[ℤ] Additive X.Kˣ) = LinearMap.id := by
    rw [h1]; ext u; rfl
  unfold Tower.kmap
  rw [h2, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

theorem mob_one' (z : ℂ) : mob 1 z = z := by
  simp [mob, ent]

section Main

variable (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]

theorem rel_add {b b' : X.Fn l} {F F' : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (h : Rel X l b F) (h' : Rel X l b' F') :
    Rel X l (b + b') (F + F') := by
  intro u
  have := (GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws Ω ε X l).1 _ _ _ _ (h u) (h' u)
  convert this using 1 <;> first | rfl | (funext z; simp)

theorem rel_zero : Rel X l 0 0 := by
  intro u
  convert (GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws Ω ε X l).2.1 using 1 <;> first | rfl | (funext z; simp)

theorem rel_smul (c : ℤ_[l]) {b : X.Fn l} {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (h : Rel X l b F) :
    Rel X l (c • b) (c • F) := by
  intro u
  have := (GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws Ω ε X l).2.2.1 c _ _ (h u)
  convert this using 1 <;> first | rfl | (funext z; simp)

theorem rel_act (m : Matrix (Fin 2) (Fin 2) ℤ) {b : X.Fn l} {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (h : Rel X l b F) :
    Rel X l (X.act l m b) (opP ℤ_[l] m F) := by
  intro u
  have e : (fun z => MvPolynomial.eval u (opP ℤ_[l] m F z)) =
      fun z => (fun z => MvPolynomial.eval (mZl l m *ᵥ u) (F z)) (mob (toGQ m) z) := by
    funext z
    simp only [opP, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Betti.eval_slP]; rfl
  show R1 X l (X.kmap l (X.sl (toGQ m)).toRingEquiv (b (mZl l m *ᵥ u))) _
  rw [e]
  by_cases hm : 0 < m.det
  · exact (GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws Ω ε X l).2.2.2 m _ _ hm (h _)
  · have h1 : toGQ m = 1 := by unfold toGQ; rw [dite_eq_right hm]
    rw [h1, kmap_eq_self X l _ (fun f => X.sl_one f)]
    simp only [mob_one']
    exact h _

theorem rel_sum {ι : Type} (s : Finset ι) (m : ι → Matrix (Fin 2) (Fin 2) ℤ) {b : X.Fn l}
    {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (h : Rel X l b F) :
    Rel X l ((∑ j ∈ s, X.act l (m j)) b) ((∑ j ∈ s, opP ℤ_[l] (m j)) F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_zero X l
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply, LinearMap.add_apply]
    exact rel_add X l (rel_act X l _ h) ih

end Main

end GlobalTheory.KZ.H3.RelOp


open GlobalTheory.KZ.H3.RelOp in
theorem GlobalTheory.KZ.H3.rel_ops : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    (∀ b b' F F', Rel X l b F → Rel X l b' F' → Rel X l (b + b') (F + F')) ∧ Rel X l 0 0 ∧
    (∀ (c : ℤ_[l]) b F, Rel X l b F → Rel X l (c • b) (c • F)) ∧
    (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) b F, Rel X l b F → Rel X l (X.act l m b) (opP ℤ_[l] m F)) ∧
    (∀ (N : ℕ) (T : Letter) b F, Rel X l b F → Rel X l (X.op N l T b) (opL ℤ_[l] N l T F)) := by
  intro Ω _ _ ε X l _
  refine ⟨fun b b' F F' h h' => rel_add X l h h', rel_zero X l, fun c b F h => rel_smul X l c h,
    fun m b F h => rel_act X l m h, fun N T b F h => ?_⟩
  cases T with
  | T q =>
    simp only [Tower.op, Tower.heckeT, opL, LinearMap.add_apply]
    exact rel_add X l (rel_sum X l _ _ h) (rel_act X l _ h)
  | U =>
    simp only [Tower.op, Tower.heckeU, opL]
    exact rel_sum X l _ _ h
  | D d =>
    simp only [Tower.op, Tower.diam, opL]
    exact rel_act X l _ h
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.SplitCompletion

theorem continuous_of_valued_eq {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]
  intro γ _
  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    simp [ha]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hf, ← ha]
  exact hx


open scoped WithZeroTopology in
theorem exists_extension {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) (f : K →+* u.adicCompletion L)
    (hf : ∀ x, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K _ x) = f x) ∧ ∀ y, Valued.v (φ y) = Valued.v y := by
  first
  | exact @_root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension
  | exact _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension
  | (apply _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension ..)

theorem exists_ringEquiv_splitPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v),
    ∃ φ : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E ≃+* Fv F v, (∀ x : E, φ (algebraMap E _ x) = τ x) ∧
      (∀ y, Valued.v (φ y) = Valued.v y) ∧ Continuous φ ∧ Continuous φ.symm := by
  intro F E _ _ _ _ _ v τ
  obtain ⟨φ, hφc, hφ, hφv⟩ := exists_extension (GlobalTheory.AdelicU.splitPrime τ) v (τ : E →+* Fv F v)
    (GlobalTheory.AdelicU.valued_apply_eq_valuation τ)
  obtain ⟨ψ, hψc, hψ, -⟩ := exists_extension v (GlobalTheory.AdelicU.splitPrime τ)
    ((algebraMap E _).comp (algebraMap F E)) fun a =>
      (ReciprocityTheory.Aut.adic_valued_algebraMap _ _).trans ((GlobalTheory.AdelicU.valued_apply_eq_valuation τ _).symm.trans
        (GlobalTheory.AdelicU.valued_apply_algebraMap τ a))
  have hid : φ ∘ ψ = id := (HeightOneSpectrum.denseRange_algebraMap F v).equalizer (hφc.comp hψc) continuous_id
    (funext fun a => ((congrArg φ (hψ a)).trans (hφ _)).trans (τ.commutes a))
  let e := RingEquiv.ofBijective φ ⟨φ.injective, fun y => ⟨ψ y, congrFun hid y⟩⟩
  refine ⟨e, hφ, hφv, hφc, continuous_of_valued_eq (v.valuedAdicCompletion_surjective F) e.symm.toRingHom fun y => ?_⟩
  exact (hφv _).symm.trans (congrArg _ (e.apply_symm_apply y))

end GlobalTheory.SplitCompletion
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.NTheta IsDedekindDomain NumberField GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EmbChart

open GlobalTheory.AdelicU

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F))

def atPlace : Fv F v →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v)

theorem atPlace_apply (a : Fv F v) : atPlace v a = pairA F 0 (singleFin v a) := rfl

theorem atPlace_mul_right (a : Fv F v) (y : AF F) : atPlace v a * y = atPlace v (a * evFin F v y) := by
  refine Prod.ext (zero_mul _) ?_
  change singleFin v a * sndA F y = singleFin v (a * evalV F v (sndA F y))
  refine FiniteAdeleRing.ext _ fun u => ?_
  change evalV F u (singleFin v a * sndA F y) = evalV F u (singleFin v (a * evalV F v (sndA F y)))
  rw [map_mul]
  by_cases e : u = v
  · subst e; rw [evalV_singleFin_self, evalV_singleFin_self]
  · rw [evalV_singleFin_ne e, evalV_singleFin_ne e, zero_mul]

theorem evFin_atPlace (a : Fv F v) : evFin F v (atPlace v a) = a := evalV_singleFin_self v a


variable (E) in
def tensAt : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (atPlace v) LinearMap.id

theorem tensAt_tmul (a : Fv F v) (x : E) : tensAt E v (a ⊗ₜ[F] x) = atPlace v a ⊗ₜ[F] x := rfl

theorem compFin_tensAt (y : Fv F v ⊗[F] E) : compFin F E v (tensAt E v y) = y := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => exact congrArg (· ⊗ₜ[F] x) (evFin_atPlace v a)

theorem tensAt_eq_zero {y : Fv F v ⊗[F] E} : tensAt E v y = 0 ↔ y = 0 :=
  ⟨fun h => by rw [← compFin_tensAt v y, h, map_zero], fun h => by rw [h, map_zero]⟩

theorem tensAt_mul_right (y : Fv F v ⊗[F] E) (z : AF F ⊗[F] E) :
    tensAt E v y * z = tensAt E v (y * compFin F E v z) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), add_mul, hx, hy]
  | tmul a x =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add (f := _), mul_add, hx, hy]
    | tmul b x' =>
      change _ = tensAt E v (a ⊗ₜ[F] x * evFin F v b ⊗ₜ[F] x')
      rw [tensAt_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, tensAt_tmul,
        atPlace_mul_right]

theorem sigR_tensAt (σ : E →ₐ[F] E) (y : Fv F v ⊗[F] E) :
    sigR (AF F) σ (tensAt E v y) = tensAt E v (sigR _ σ y) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem map_evalV_map_sndA (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      compFin F E v z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem map_evalV_mem {z : Af F ⊗[F] E}
    (hz : z ∈ AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)}) :
    Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E) z ∈ intLoc F E v := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    exact tmul_mem_intLoc (hα v) o
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem map_sndA_tensAt_mem {y : Fv F v ⊗[F] E} (h : y ∈ intLoc F E v) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (tensAt E v y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  refine intLoc_induction (p := fun y => Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (tensAt E v y) ∈
      AddSubgroup.closure {y : Af F ⊗[F] E | ∃ a ∈ Formalism.MainNotions.StandardLattice.intAf F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)})
    (fun a ha x => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) h
  · refine AddSubgroup.subset_closure ⟨singleFin v a, fun u => ?_, x, rfl⟩
    by_cases e : u = v
    · subst e; rw [evalV_singleFin_self]; exact ha
    · rw [evalV_singleFin_ne e]; exact zero_mem _
  · rw [map_zero, map_zero]; exact zero_mem _
  · rw [map_add (f := _), map_add (f := _)]; exact add_mem hy hz
  · rw [map_neg, map_neg]; exact neg_mem hy

end General

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem finPart_tensAt_mem_iff (y : Fv D.host.F v ⊗[D.host.F] D.host.E) :
    finPart D (tensAt D.host.E v y) ∈ intAE D ↔ y ∈ intLoc D.host.F D.host.E v := by
  refine ⟨fun h => ?_, map_sndA_tensAt_mem v⟩
  have h3 := map_evalV_mem v h
  rwa [show finPart D (tensAt D.host.E v y) = _ from rfl, finPart, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_evalV_map_sndA, compFin_tensAt] at h3

def idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : AE D := tensAt D.host.E v (splitIdem (isCMExt_host D) τ)

theorem idem_mul (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (a : AE D) :
    idem τ * a = tensAt D.host.E v (splitIdem (isCMExt_host D) τ * compFin D.host.F D.host.E v a) :=
  tensAt_mul_right v _ a

theorem compFin_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    compFin D.host.F D.host.E v (idem τ) = splitIdem (isCMExt_host D) τ := compFin_tensAt v _

theorem cA_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    cA D (idem τ) = tensAt D.host.E v (1 - splitIdem (isCMExt_host D) τ) :=
  (sigR_tensAt v _ _).trans (congrArg _ (sigR_splitIdem _ τ))

theorem isSplitIdem_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : IsSplitIdem D (idem τ) := by
  refine ⟨?_, ?_, v, atPlace v 1, ⟨singleFin v 1, rfl, evalV_singleFin_self v 1, fun u hu => evalV_singleFin_ne hu 1⟩,
    ?_⟩
  · rw [idem_mul, compFin_idem, splitIdem_mul_self]; rfl
  · rw [idem_mul, cA_idem, compFin_tensAt, mul_sub, mul_one, splitIdem_mul_self, sub_self, LinearMap.map_zero]
  · rw [cA_idem, idem, ← LinearMap.map_add (f := _), add_sub_cancel]; rfl

theorem finPart_idem_mul_mem_iff (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (a : AE D) :
    finPart D (idem τ * a) ∈ intAE D ↔
      splitProj τ (compFin D.host.F D.host.E v a) ∈ v.adicCompletionIntegers D.host.F := by
  rw [idem_mul, finPart_tensAt_mem_iff, mem_intLoc_iff_split (isCMExt_host D) τ, map_mul, map_mul,
    splitProj_splitIdem, splitProj_comp_splitIdem, one_mul, zero_mul]
  exact and_iff_left (zero_mem _)

theorem chart_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : Chart (idem τ) v
    ((splitProj τ : Fv D.host.F v ⊗[D.host.F] D.host.E →+* Fv D.host.F v).comp (compFin D.host.F D.host.E v)) := by
  refine ⟨fun a => ⟨tensAt D.host.E v (a ⊗ₜ 1), ?_⟩, fun a => ?_, fun y => ?_, fun a => ?_⟩
  · change splitProj τ (compFin D.host.F D.host.E v (tensAt D.host.E v (a ⊗ₜ[D.host.F] 1))) = a
    rw [compFin_tensAt, splitProj_tmul, map_one, mul_one]
  · rw [idem_mul, tensAt_eq_zero]
    exact splitProj_eq_zero_iff _ τ _
  · change splitProj τ (evFin D.host.F v y ⊗ₜ 1) = _
    rw [splitProj_tmul, map_one, mul_one]; rfl
  · rw [finPart_idem_mul_mem_iff, isInt_Ov]; rfl

theorem isIdemAt_idem (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) : IsIdemAt (idem τ) (splitPrime τ) := by
  refine ⟨isSplitIdem_idem τ, fun x hx => ?_⟩
  have h0 : Valued.v (τ x) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero τ).2 (RingOfIntegers.coe_ne_zero_iff.2 hx))
  have h1 : splitProj τ (compFin D.host.F D.host.E v (incA D (x : D.host.E)⁻¹)) = τ (x : D.host.E)⁻¹ := by
    change splitProj τ (evFin D.host.F v 1 ⊗ₜ _) = _
    rw [splitProj_tmul, map_one, one_mul]; rfl
  rw [finPart_idem_mul_mem_iff, h1, mem_splitPrime, HeightOneSpectrum.mem_adicCompletionIntegers,
    map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 h0)]

theorem exists_isIdemAt_chart : ∀ {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), ∃ e : AE D, IsIdemAt e (GlobalTheory.AdelicU.splitPrime τ) ∧ Chart e v ((GlobalTheory.AdelicU.splitProj τ : Fv D.host.F v ⊗[D.host.F] D.host.E →+* Fv D.host.F v).comp (GlobalTheory.AdelicU.compFin D.host.F D.host.E v)) :=
  fun τ => ⟨idem τ, isIdemAt_idem τ, chart_idem τ⟩

end GlobalTheory.EmbChart

end
end

section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

namespace GlobalTheory.NormSum.VacInt

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {a d : ℕ} {e0 : VC D a d → ℂ}

theorem sd_std (D : D7) (N : ℕ) : SD D (stdL D N) := by
  obtain ⟨Lt, h, h1, -⟩ := exists_lattice_of_adelic_point D N
  exact h1 ▸ (h 1).2

theorem vac_mem_TT (hg : admG1 D) (crv : Crv D cc δ) (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) :
    e0 ∈ TT D (tor0 D cc δ) a d := by
  refine ⟨he.1, 1, one_pos, fun x hx => ?_⟩
  rw [one_smul, (GlobalTheory.ThetaLine.theta_line D hg cc δ crv a d _ (Or.inr ⟨_, _, sd_std D a, sd_std D d, rfl⟩)).2.1 x hx]
  exact funext (he.2 x hx)

theorem om_vac_norm (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) {k : GA D a} {k' : GA D d} (hk : k ∈ intG D a) (hk' : k' ∈ intG D d) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om k k' e0 = c • e0 := by
  obtain ⟨x, x', -, -, h⟩ := om_vac_of_mem he hT W (AdLattice.intG_of_mem D a k hk) (AdLattice.intG_of_mem D d k' hk')
  refine ⟨_, ?_, h⟩
  simp [W.chV.unitary, W.chV'.unitary]

theorem om_vac_fix (he : e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d)) (hT : e0 ∈ TT D (tor0 D cc δ) a d)
    (W : WeilO D cc δ a d e0) (hu : ∀ u, IntU D u → W.chV'.f u = 1) {k : GA D a} (hk : k ∈ intG D a) :
    W.Om k 1 e0 = e0 := by
  obtain ⟨x, hx, h⟩ := om_vac_left he hT W (AdLattice.intG_of_mem D a k hk)
  rw [h, hu x hx]
  simp

def sphericalPair (hg : admG1 D) (crv : Crv D cc δ) (pt0 : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (had : a ≤ d) (hd : Even d)
    (vac : oddE0 D cc δ t0 a d e0) (W : WeilO D cc δ a d e0) (n : D.what₂.Tau → ℕ)
    (wt : ∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ)) (hu : ∀ u, IntU D u → W.chV'.f u = 1) :
    Pair D cc δ t0 1 :=
  Pair.ofVacuum crv pt0 had hd vac W n wt (fun _ hk => om_vac_fix vac.1 (vac_mem_TT hg crv vac.1) W hu hk)
    (fun _ hj => om_vac_norm vac.1 (vac_mem_TT hg crv vac.1) W (one_mem _) hj)

theorem vacuum_eigen : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∀ (a d : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D a) (stdL D d), ∀ W : WeilO D cc δ a d e0,
      e0 ∈ TT D (tor0 D cc δ) a d ∧
      (∀ k ∈ intG D a, ∀ k' ∈ intG D d, ∃ x x' : (AE D)ˣ, IntU D x ∧ IntU D x' ∧
        W.Om k k' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f x ^ W.ep' : ℂˣ) : ℂ) • e0) ∧
      (∀ k ∈ intG D a, ∀ k' ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om k k' e0 = c • e0) ∧
      ((∀ u, IntU D u → W.chV'.f u = 1) → ∀ k ∈ intG D a, W.Om k 1 e0 = e0) ∧
      ((∀ u, IntU D u → W.chV'.f u = 1) → a ≤ d → Even d → ∀ t0 : ℂ, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
        oddE0 D cc δ t0 a d e0 → ∀ n : D.what₂.Tau → ℕ, (∀ τ, 2 * (n τ : ℤ) = W.ep' * W.chV'.n τ - (d : ℤ)) →
        ∃ P : Pair D cc δ t0 1, P.a = a ∧ P.d = d ∧ HEq P.e0 e0 ∧ HEq P.W W ∧ P.n = n ∧ P.F = P.e0 ∧ P.F ≠ 0 ∧
          P.J = intG D P.d) := by
  intro D hg cc δ crv a d e0 he W
  have hT := vac_mem_TT hg crv he
  exact ⟨hT, fun k hk k' hk' => om_vac_of_mem he hT W (AdLattice.intG_of_mem D a k hk) (AdLattice.intG_of_mem D d k' hk'),
    fun _ hk _ hk' => om_vac_norm he hT W hk hk', fun hu _ hk => om_vac_fix he hT W hu hk,
    fun hu had hd t0 pt0 vac n wt => ⟨sphericalPair hg crv pt0 had hd vac W n wt hu, rfl, rfl, HEq.rfl, HEq.rfl, rfl, rfl,
      W.nz, rfl⟩⟩

end GlobalTheory.NormSum.VacInt
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaTripleDiagonalData_of_selfDualNeighbourTriple : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∀ (N N' : ℕ) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) → ∀ A B C : Lat D N, Tri D P A B C → TriDat D (tor0 D cc δ) (La D (tor0 D cc δ) A (stdL D N')) (La D (tor0 D cc δ) B (stdL D N')) (La D (tor0 D cc δ) C (stdL D N')) P N' := by
  first | exact @GlobalTheory.TriangleRows.triDat_rows | exact GlobalTheory.TriangleRows.triDat_rows | (intros; apply GlobalTheory.TriangleRows.triDat_rows <;> assumption)
end
