module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle432
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConeD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem kugaSm_map {E : Type} [Field E] {a n : ℕ} (e : Fin n → Herm E a) {A A' : Type} [Ring A] [Module ℝ A]
    [Ring A'] [Module ℝ A'] (f : A →+* A') (L : Lie E a →ₗ[ℝ] A) (L' : Lie E a →ₗ[ℝ] A') (h : ∀ X, L' X = f (L X)) :
    cas L' e = f (cas L e) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cas, map_sum, map_sub, map_mul, h]

private theorem kugaSm_A {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a n : ℕ} (e : Fin n → Herm E a)
    (Ξ : AlgRep E a) (r : ℝ) :
    cas (shift (smA Ξ) r) e = (cas (shift (lie E a) r) e).rTensor (Fin Ξ.d → ℂ) := by
  refine kugaSm_map e (Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)).toRingHom _ _ fun X => ?_
  change _ = (Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)) _
  rw [shift_apply, shift_apply, map_add (f := _), ← algebraMap_smul ℂ (r * ell E a X) (1 : Module.End ℂ (Sm E a)), map_smul, map_one,
    algebraMap_smul]
  rfl

private theorem kugaSm_B {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a n : ℕ} (e : Fin n → Herm E a)
    (Ξ : AlgRep E a) (r c : ℝ) (h : HasCas Ξ r c e) :
    cas (shift (smB Ξ) (-r)) e = (c : ℂ) • 1 := by
  let f : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ →ₐ[ℂ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
    (Module.End.lTensorAlgHom ℂ (Fin Ξ.d → ℂ) (Sm E a)).comp
      (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] _).toAlgHom
  have h1 : cas (shift (smB Ξ) (-r)) e = f (cas (shift Ξ.dmat (-r)) e) := by
    refine kugaSm_map e f.toRingHom _ _ fun X => ?_
    change _ = f _
    rw [shift_apply, shift_apply, map_add (f := _), ← algebraMap_smul ℂ (-r * ell E a X) (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ), map_smul,
      map_one, algebraMap_smul, smB_apply]
    rfl
  rw [h1, show cas (shift Ξ.dmat (-r)) e = _ from h, map_smul, map_one]

theorem UpperTheory.V.Cj.H.kugaSm :
    UpperTheory.V.Cj.H.KugaSm := by
  intro E _ _ _ a n e he Ξ r c hc
  obtain ⟨a1, b1, hab, -, -, hinf⟩ := smAB E a Ξ
  obtain ⟨-, -, -, l4⟩ := ellFacts E a
  have hA := l4 _ _ r a1
  have hB := l4 _ _ (-r) b1
  have hsum : shift (smA Ξ) r + shift (smB Ξ) (-r) = smLie Ξ := by
    rw [shift_add_shift]
    exact LinearMap.ext fun X => add_sub_cancel (smA Ξ X) (smLie Ξ X)
  have hcom : ∀ X Y, Commute (shift (smA Ξ) r X) (shift (smB Ξ) (-r) Y) := fun X Y => by
    rw [shift_apply, shift_apply]
    exact ((hab X Y).add_right ((Commute.one_right _).smul_right _)).add_left ((Commute.one_left _).smul_left _)
  have hcas : cas (shift (smB Ξ) (-r)) e - cas (shift (smA Ξ) r) e = -(casA r c e).rTensor (Fin Ξ.d → ℂ) := by
    rw [kugaSm_A, kugaSm_B e Ξ r c hc, casA, LinearMap.rTensor_sub, LinearMap.rTensor_smul, neg_sub, Module.End.one_eq_id,
      Module.End.one_eq_id, LinearMap.rTensor_id]
  have hdel : ∀ (q : ℕ) (X : Fin q → Herm E a),
      del (shift (smB Ξ) (-r) - shift (smA Ξ) r) e (0 : Co Ξ (q + 1)) X = 0 := fun q X => by
    simp [del_apply]
  refine ⟨fun ω hω hd => ?_, fun q ω hω hd => ?_⟩
  · refine AlternatingMap.ext fun X => ?_
    have h := kugaZero E a n e _ _ _ hcom ω (by rw [hsum]; exact hinf _ ω hω) X
    rw [hsum, hd, hdel, hcas, LinearMap.neg_apply] at h
    rw [app_apply]
    exact neg_eq_zero.1 h.symm
  · refine AlternatingMap.ext fun X => ?_
    have h := kugaSucc E a n e he _ _ _ hA hB hcom q ω (by rw [hsum]; exact hinf _ ω hω) X
    rw [hsum, hd, hdel, hcas, LinearMap.neg_apply, add_zero] at h
    rw [app_apply, AlternatingMap.neg_apply]
    exact (neg_eq_iff_eq_neg.1 h.symm)
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped ContDiff

section General

variable {P Q α : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [TopologicalSpace α]

private def Loc (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : P → α → V) (x : P) (y : α) : Prop :=
  ∃ (h : P × Q → V) (A : α → Q), ContinuousAt A y ∧ ContDiffAt ℝ ∞ h (x, A y) ∧
    ∀ᶠ p : P × α in 𝓝 (x, y), H p.1 p.2 = h (p.1, A p.2)

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : P → α → V} {x : P} {y : α}

private theorem Loc.cont (h : Loc Q H x y) : ContinuousAt (fun p : P × α => H p.1 p.2) (x, y) := by
  obtain ⟨h, A, hA, hh, e⟩ := h
  refine ContinuousAt.congr ?_ (EventuallyEq.symm e)
  exact ContinuousAt.comp (f := fun p : P × α => (p.1, A p.2)) hh.continuousAt
    (continuousAt_fst.prodMk (ContinuousAt.comp (f := Prod.snd) hA continuousAt_snd))

private theorem Loc.diff (h : Loc Q H x y) : DifferentiableAt ℝ (fun x => H x y) x := by
  obtain ⟨h, A, -, hh, e⟩ := h
  have e' : (fun x => H x y) =ᶠ[𝓝 x] fun x => h (x, A y) :=
    (Continuous.prodMk_left y).continuousAt.eventually e
  exact DifferentiableAt.congr_of_eventuallyEq
    ((hh.differentiableAt (by simp)).comp x (differentiableAt_id.prodMk (differentiableAt_const _))) e'

private theorem Loc.fderiv (h : Loc Q H x y) : Loc Q (fun x y => fderiv ℝ (fun x => H x y) x) x y := by
  obtain ⟨h, A, hA, hh, e⟩ := h
  refine ⟨fun q => (_root_.fderiv ℝ h q).comp (ContinuousLinearMap.inl ℝ P Q), A, hA,
    (hh.fderiv_right (by simp)).clm_comp contDiffAt_const, ?_⟩
  have hc : ContinuousAt (fun p : P × α => (p.1, A p.2)) (x, y) :=
    continuousAt_fst.prodMk (ContinuousAt.comp (f := Prod.snd) hA continuousAt_snd)
  have hd : ∀ᶠ q in 𝓝 (x, A y), ContDiffAt ℝ 1 h q := (hh.of_le (by simp)).eventually (by simp)
  filter_upwards [e.eventually_nhds, hc.eventually hd] with p hp hq
  have e' : (fun x => H x p.2) =ᶠ[𝓝 p.1] fun x => h (x, A p.2) :=
    (Continuous.prodMk_left p.2).continuousAt.eventually hp
  rw [e'.fderiv_eq]
  exact ((hq.differentiableAt (by simp)).hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left p.1 (A p.2))).fderiv

variable [FiniteDimensional ℝ P] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
  {μ : Measure α} {f : α → ℂ} {S : Set P}

omit [FiniteDimensional ℝ P] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α] in
private theorem supp_fderiv (hs : ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, H x' y = 0) :
    ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, fderiv ℝ (fun x => H x y) x' = 0 := by
  obtain ⟨C, hC, h⟩ := hs
  refine ⟨C, hC, h.eventually_nhds.mono fun x' hx' y hy => ?_⟩
  have e : (fun x => H x y) =ᶠ[𝓝 x'] fun _ => 0 := hx'.mono fun z hz => hz y hy
  rw [e.fderiv_eq, fderiv_fun_const]
  rfl

private theorem dom [NormedSpace ℂ V] (hf : LocallyIntegrable f μ) (hS : IsOpen S) (hx : x ∈ S)
    (hH : ∀ x ∈ S, ∀ y, Loc Q H x y) (hs : ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, H x' y = 0) :
    ∃ b : α → ℝ, Integrable b μ ∧ ∀ᶠ x' in 𝓝 x, AEStronglyMeasurable (fun y => f y • H x' y) μ ∧
      ∀ y, ‖f y • H x' y‖ ≤ b y := by
  obtain ⟨C, hC, h⟩ := hs
  obtain ⟨K, hK, hKS, hKc⟩ := local_compact_nhds (hS.mem_nhds hx)
  obtain ⟨M, hM⟩ := (hKc.prod hC).exists_bound_of_continuousOn (f := fun p : P × α => H p.1 p.2)
    fun p hp => (hH p.1 (hKS hp.1) p.2).cont.continuousWithinAt
  refine ⟨C.indicator fun y => ‖f y‖ * M,
    (integrable_indicator_iff hC.measurableSet).2 ((hf.integrableOn_isCompact hC).norm.mul_const M), ?_⟩
  filter_upwards [h, hK] with x' h1 h2
  refine ⟨hf.aestronglyMeasurable.smul (Continuous.aestronglyMeasurable (continuous_iff_continuousAt.2 fun y => ?_)),
    fun y => ?_⟩
  · exact ContinuousAt.comp (f := fun y => (x', y)) (hH x' (hKS h2) y).cont (Continuous.prodMk_right x').continuousAt
  · by_cases hy : y ∈ C
    · rw [Set.indicator_of_mem hy, norm_smul]
      exact mul_le_mul_of_nonneg_left (hM (x', y) ⟨h2, hy⟩) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy, h1 y hy, smul_zero, norm_zero]

private theorem hasFD [NormedSpace ℂ V] [SMulCommClass ℝ ℂ V] (hf : LocallyIntegrable f μ) (hS : IsOpen S) (hx : x ∈ S)
    (hH : ∀ x ∈ S, ∀ y, Loc Q H x y) (hs : ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, H x' y = 0) :
    HasFDerivAt (fun x => ∫ y, f y • H x y ∂μ) (∫ y, f y • fderiv ℝ (fun x => H x y) x ∂μ) x := by
  obtain ⟨b, hb, h⟩ := dom hf hS hx hH hs
  obtain ⟨b', hb', h'⟩ := dom hf hS hx (fun x hx y => (hH x hx y).fderiv) (supp_fderiv hs)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := b')
    (F' := fun x y => f y • fderiv ℝ (fun x => H x y) x) (h'.and (hS.eventually_mem hx)) (h.mono fun _ h => h.1)
    (hb.mono' h.self_of_nhds.1 (.of_forall h.self_of_nhds.2)) h'.self_of_nhds.1
    (.of_forall fun y x' hx' => hx'.1.2 y) hb' (.of_forall fun y x' hx' => ?_)
  exact (hH x' hx'.2 y).diff.hasFDerivAt.const_smul (f y)

private theorem smooth_nat (hf : LocallyIntegrable f μ) (hS : IsOpen S) (n : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [SMulCommClass ℝ ℂ V] (H : P → α → V),
      (∀ x ∈ S, ∀ y, Loc Q H x y) → (∀ x ∈ S, ∃ C : Set α, IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, H x' y = 0) →
      ContDiffOn ℝ n (fun x => ∫ y, f y • H x y ∂μ) S := by
  induction n with
  | zero =>
    intro V _ _ _ _ H hH hs
    exact contDiffOn_zero.2 fun x hx => (hasFD hf hS hx hH (hs x hx)).continuousAt.continuousWithinAt
  | succ n ih =>
    intro V _ _ _ _ H hH hs
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hS]
    refine ⟨fun x hx => (hasFD hf hS hx hH (hs x hx)).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih _ _ (fun x hx y => (hH x hx y).fderiv) fun x hx => supp_fderiv (hs x hx)).congr
      fun x hx => (hasFD hf hS hx hH (hs x hx)).fderiv

end General

section Adelic

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

omit [_root_.NumberField.IsTotallyComplex E] in
private theorem contDiff_mulL :
    ContDiff ℝ ∞ fun q : Lie E a × Lie E a => toL (Matrix.of q.2 * Matrix.of q.1) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  change ContDiff ℝ ∞ fun q : Lie E a × Lie E a => ∑ k, q.2 i k * q.1 k j
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ ?_
  · exact contDiff_pi.1 (contDiff_pi.1 contDiff_snd i) k
  · exact contDiff_pi.1 (contDiff_pi.1 contDiff_fst k) j

private theorem loc_chart {ψ : Sm E a} (hψ : HasLev ψ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) (y : GA E a) :
    Loc (Lie E a) (fun x y => chart ψ.1 (y⁻¹ * g) x) x y := by
  have hc : Continuous fun w : GA E a => (y⁻¹ * g)⁻¹ * (w⁻¹ * g) :=
    continuous_const.mul (continuous_inv.mul continuous_const)
  have hA : Continuous fun w : GA E a => (GeneralLinearGroup.map (pInf E) ((y⁻¹ * g)⁻¹ * (w⁻¹ * g))).val :=
    Units.continuous_val.comp (GlobalTheory.CompanionTheory.AffglAssembly.continuous_mapInf.comp hc)
  refine ⟨fun q => chart ψ.1 (y⁻¹ * g) (toL (Matrix.of q.2 * Matrix.of q.1)),
    fun w => toL (GeneralLinearGroup.map (pInf E) ((y⁻¹ * g)⁻¹ * (w⁻¹ * g))).val, hA.continuousAt, ?_, ?_⟩
  · refine ContDiffAt.comp _ (contDiffAt_chart ψ.2 _ ?_) contDiff_mulL.contDiffAt
    exact IsUnit.mul (Units.isUnit _) hx
  · have h1 : ∀ᶠ w in 𝓝 y, act (.fin (GeneralLinearGroup.map (pFin E) ((y⁻¹ * g)⁻¹ * (w⁻¹ * g)))) ψ = ψ :=
      (GlobalTheory.CompanionTheory.AffglAssembly.continuous_mapFin.comp hc).continuousAt.eventually_mem (hψ.mem_nhds (by
        change finRep E a _ ψ = ψ
        simp))
    rw [nhds_prod_eq]
    filter_upwards [prod_mem_prod (isOpen_invSet.mem_nhds hx) h1]
    rintro ⟨x', w⟩ ⟨⟨u, hu⟩, hw⟩
    obtain rfl : x' = toL u.val := hu.symm
    set t := (y⁻¹ * g)⁻¹ * (w⁻¹ * g) with ht
    have e1 := congrFun (congrArg Subtype.val hw) (y⁻¹ * g * infGL E a (GeneralLinearGroup.map (pInf E) t * u))
    change ψ.1 (_ * finGL E a _) = _ at e1
    change chart ψ.1 (w⁻¹ * g) (toL u.val) = chart ψ.1 (y⁻¹ * g) (toL (GeneralLinearGroup.map (pInf E) t * u).val)
    rw [chart_val, chart_val, ← e1, map_mul, mul_assoc (y⁻¹ * g), mul_assoc (infGL E a _), infGL_comm u,
      ← mul_assoc (infGL E a _), infGL_mul_finGL, ← mul_assoc (y⁻¹ * g), ht, mul_inv_cancel_left]

open scoped Matrix.Norms.Operator in
omit [_root_.NumberField.IsTotallyComplex E] in
private theorem isOpenMap_val : IsOpenMap fun u : GL (Fin a) (Cinf E) => toL u.val :=
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).isOpenMap

open scoped Matrix.Norms.Operator in
omit [_root_.NumberField.IsTotallyComplex E] in
private theorem locCpt : LocallyCompactSpace (GL (Fin a) (Cinf E)) :=
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  haveI : ProperSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.proper ℝ _
  (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).locallyCompactSpace

private theorem supp_chart {ψ : GA E a → ℂ} (hψ : HasCompactSupport ψ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    ∃ C : Set (GA E a), IsCompact C ∧ ∀ᶠ x' in 𝓝 x, ∀ y ∉ C, chart ψ (y⁻¹ * g) x' = 0 := by
  obtain ⟨u, hu⟩ := hx
  obtain rfl : x = toL u.val := hu.symm
  haveI := locCpt (E := E) (a := a)
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds u
  have hc : Continuous fun p : GL (Fin a) (Cinf E) × GA E a => g * infGL E a p.1 * p.2⁻¹ :=
    (continuous_const.mul ((GlobalTheory.CompanionTheory.LieSkew.continuous_infGL_map E a).comp continuous_fst)).mul continuous_snd.inv
  refine ⟨_, (hKc.prod hψ.isCompact).image hc, ?_⟩
  filter_upwards [isOpenMap_val.image_mem_nhds hK]
  rintro _ ⟨v, hv, rfl⟩ y hy
  rw [chart_val]
  by_contra h
  exact hy ⟨(v, y⁻¹ * g * infGL E a v), ⟨hv, subset_tsupport _ h⟩, by simp only; group⟩

end Adelic

theorem UpperTheory.V.Cj.H.cvSm :
    UpperTheory.V.Cj.H.CvSm := by
  intro E _ _ _ a μ _ _ ψ hψ F g
  have hf := (UpperTheory.V.Cj.H.locInt (GA E a) (latticeGL E a) μ).1 F
  have h : ContDiffOn ℝ ∞ (fun x => ∫ y, GlobalTheory.AutomorphicL2Unitary.lift _ F y • chart ψ.1 (y⁻¹ * g) x ∂μ) (invSet E a) :=
    contDiffOn_infty.2 fun n => smooth_nat hf isOpen_invSet n ℂ _ (fun _ hx y => loc_chart hψ.2 g hx y)
      fun _ hx => supp_chart hψ.1 g hx
  refine h.congr ?_
  rintro x ⟨u, hu⟩
  obtain rfl : x = toL u.val := hu.symm
  simp only [chart_val, cv, mul_assoc, smul_eq_mul]
end

section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} (G : Dr.Geo Γ V S d)

private theorem tr_tr (q : ℕ) (γ δ : Γ) (h : γ * δ = 1) (m : V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :
    G.tr q γ (G.tr q δ m) = m := by
  have hδ : δ = γ⁻¹ := eq_inv_of_mul_eq_one_right h
  subst hδ
  ext v
  rw [Geo.tr_apply, Geo.tr_apply, Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one,
    Matrix.one_mulVec]
  have hv : (fun i => (G.ρ γ⁻¹⁻¹) ((G.ρ γ⁻¹) (v i))) = v := by
    funext i
    exact Geo.ρ_inv_apply G γ⁻¹ (v i)
  rw [hv]

private theorem tr_coneOp (q : ℕ) (γ : Γ) (w : V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) (p x : V) :
    G.tr q γ (coneOp p w (G.ρ γ⁻¹ x)) = coneOp (G.ρ γ p) (fun y => G.tr (q + 1) γ (w (G.ρ γ⁻¹ y))) x := by
  let L : (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) ≃L[ℝ] (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :=
    ContinuousLinearEquiv.equivOfInverse (G.tr q γ) (G.tr q γ⁻¹)
      (fun m => tr_tr G q γ⁻¹ γ (inv_mul_cancel γ) m)
      (fun m => tr_tr G q γ γ⁻¹ (mul_inv_cancel γ) m)
  have hL : ∀ m, L m = G.tr q γ m := fun m => rfl
  have key : ∀ f : ℝ → (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)),
      L (∫ t in (0:ℝ)..1, f t) = ∫ t in (0:ℝ)..1, L (f t) := by
    intro f
    simp only [intervalIntegral, map_sub, L.integral_comp_comm]
  have hpt : ∀ t : ℝ, G.ρ γ⁻¹ (G.ρ γ p + t • (x - G.ρ γ p)) = p + t • (G.ρ γ⁻¹ x - p) := by
    intro t
    simp [map_add (f := _), map_smul, map_sub, Geo.ρ_inv_apply]
  rw [← hL]
  unfold coneOp
  rw [key]
  congr 1
  funext t
  rw [map_smul]
  beta_reduce
  rw [hpt]
  congr 1
  ext v
  rw [hL, Geo.tr_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply, Geo.tr_apply]
  congr 2
  funext i
  refine Fin.cases ?_ ?_ i
  · simp [Geo.ρ_inv_apply]
  · intro j
    simp

end

theorem UpperTheory.V.Cj.H.poinOp :
    UpperTheory.V.Cj.H.PoinOp := by
  intro Γ V S _ _ _ _ d G hconv q
  classical
  have hD := coneD V (Fin d → ℂ) G.Y G.isOpen hconv
  let f : V → G.Om (q + 1) → S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
    fun p w s x => if x ∈ G.Y then coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) x else 0
  have hwm : ∀ (w : G.Om (q + 1)) (s : S),
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
        ∀ x ∉ G.Y, (w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s x = 0 := fun w => w.2
  have hf : ∀ p ∈ G.Y, ∀ w, f p w ∈ G.Om q := by
    intro p hp w
    refine fun s => ⟨?_, ?_⟩
    · exact ((hD p hp q _ (hwm w s).1).1).congr (fun x hx => if_pos hx)
    · intro x hx
      exact if_neg hx
  let K : V → G.Om (q + 1) → G.Om q := fun p w => if hp : p ∈ G.Y then ⟨f p w, hf p hp w⟩ else 0
  have hK : ∀ p (hp : p ∈ G.Y) w, ((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) = f p w := by
    intro p hp w
    simp [K, hp]
  refine ⟨K, ?_, ?_, ?_⟩
  · intro p hp w hw0
    apply Subtype.ext
    funext s x
    by_cases hx : x ∈ G.Y
    · rw [Geo.dOm_apply G (K p w) s hx, hK p hp w]
      have hclosed : ∀ y ∈ G.Y, extDeriv ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) y = 0 := by
        intro y hy
        have h0 := congrArg
          (fun u : G.Om (q + 1 + 1) => (u : S → V → V [⋀^Fin (q + 1 + 1)]→L[ℝ] (Fin d → ℂ)) s y) hw0
        rw [Geo.dOm_apply G w s hy] at h0
        simpa using h0
      have hloc : extDeriv (f p w s) x =
          extDeriv (coneOp p ((w : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)) x := by
        rw [← extDerivWithin_univ, ← extDerivWithin_univ]
        apply Filter.EventuallyEq.extDerivWithin_eq_of_mem _ (Set.mem_univ x)
        rw [nhdsWithin_univ]
        exact Filter.eventually_of_mem (G.isOpen.mem_nhds hx) (fun y hy => if_pos hy)
      rw [hloc]
      exact (hD p hp q _ (hwm w s).1).2 hclosed x hx
    · have h1 := ((G.dOm q (K p w)).2 s).2 x hx
      have h2 := (hwm w s).2 x hx
      rw [h1, h2]
  · intro γ p hp w
    have hp' : G.ρ γ p ∈ G.Y := G.maps γ p hp
    apply Subtype.ext
    funext s x
    show G.tr q γ (((K p w : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (G.σ γ⁻¹ s) (G.ρ γ⁻¹ x)) =
      ((K (G.ρ γ p) (G.act (q + 1) γ w) : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x
    rw [hK p hp, hK _ hp']
    by_cases hx : x ∈ G.Y
    · have hx' : G.ρ γ⁻¹ x ∈ G.Y := G.maps γ⁻¹ x hx
      simp only [f, if_pos hx, if_pos hx']
      exact tr_coneOp G q γ _ p x
    · have hx' : G.ρ γ⁻¹ x ∉ G.Y := by
        intro h
        apply hx
        have h2 := G.maps γ _ h
        have h3 := Geo.ρ_inv_apply G γ⁻¹ x
        rw [inv_inv] at h3
        rwa [h3] at h2
      simp only [f, if_neg hx, if_neg hx', map_zero]
  · intro p hp w hw s C hC hCc
    have h := coneLim V (Fin d → ℂ) G.Y hconv p hp q
      (fun k => ((w k : G.Om (q + 1)) : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s)
      (fun C' hC' hC'c => hw s C' hC' hC'c) C hC hCc
    refine h.congr ?_
    filter_upwards with k
    intro x hx
    rw [hK p hp]
    simp [f, hC hx]
end
