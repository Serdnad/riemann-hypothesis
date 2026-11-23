module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle070
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle075
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle074
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle072
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling

namespace GlobalTheory.ZonalCellDecomposition

def blkEquiv (l t : ℕ) : Fin (l * t) ≃ GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.Blocks l t :=
  finProdFinEquiv.symm.trans (Equiv.sigmaEquivProd (Fin l) (Fin t)).symm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def mtor {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    GL (A ⊕ D) k :=
  torusElt k (A ⊕ D) ϖ (Sum.elim 0 e)

def dcell {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    Set (GL (A ⊕ D) k) :=
  DoubleCoset.doubleCoset (mtor ϖ e) (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D : Set (GL (A ⊕ D) k))
    (GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D)

def IsBiType {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ)
    (φ : GL (A ⊕ D) k → ℂ) : Prop :=
  ∀ j ∈ GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection.parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    ∀ g, φ (j * g) = (ξ d : ℂ) * φ g ∧ φ (g * j) = (ξ d : ℂ) * φ g

def sumAbs {D : Type} [Fintype D] (e : D → ℤ) : ℤ := ∑ i, |e i|

def zonalInt {N : ℕ} [MeasurableSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) (ψ : GL (Fin N) k → ℂ)
    (g : GL (Fin N) k) : ℂ :=
  ∫ κ in (KO k (Fin N) : Set (GL (Fin N) k)), ψ (κ * g) ∂μK

def borelParam {N : ℕ} (q : ℕ) (α : Fin N → ℂˣ) (x : Fin N) : ℂ :=
  (α x : ℂ) * (q : ℂ) ^ (((x : ℕ) : ℂ) - ((N : ℂ) - 1) / 2)

end GlobalTheory.ZonalCellDecomposition
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier

theorem _root_.GlobalTheory.T.partialColumnFourier_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ m P Ξ ∈ SB (Matrix A C k) := by
  first | exact @GlobalTheory.ColFourier.fourierInt_mem_SB | exact GlobalTheory.ColFourier.fourierInt_mem_SB | (intros; apply GlobalTheory.ColFourier.fourierInt_mem_SB <;> assumption)
end

section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

theorem _root_.GlobalTheory.T.isAdmissible_contra_and_smoothTrace_inv : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsInvInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsAdmissible π → IsAdmissible (contra π) ∧ ∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace (contra π) μ f = smoothTrace π μ (fun g => f g⁻¹) := by
  first | exact @GlobalTheory.SmGL.ContraTrace.contra_admissible_trace | exact GlobalTheory.SmGL.ContraTrace.contra_admissible_trace | (intros; apply GlobalTheory.SmGL.ContraTrace.contra_admissible_trace <;> assumption)
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct Pointwise

namespace GlobalTheory.ModuPiLocal

theorem distribHaarChar_pi {ι : Type} [Fintype ι] (A : ι → Type) [∀ i, CommRing (A i)]
    [∀ i, TopologicalSpace (A i)] [∀ i, IsTopologicalRing (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, T2Space (A i)] [∀ i, SecondCountableTopology (A i)] (u : (∀ i, A i)ˣ) :
    distribHaarChar (∀ i, A i) u = ∏ i, distribHaarChar (A i) (Units.map (Pi.evalRingHom A i).toMonoidHom u) := by
  classical
  letI : ∀ i, MeasurableSpace (A i) := fun i => borel (A i)
  haveI : ∀ i, BorelSpace (A i) := fun i => ⟨rfl⟩
  let μ : ∀ i, Measure (A i) := fun i => Measure.addHaar
  let S : ∀ i, TopologicalSpace.PositiveCompacts (A i) := fun i => Classical.choice inferInstance
  have h0 : ∀ i, μ i (S i : Set (A i)) ≠ 0 := fun i =>
    (Measure.measure_pos_of_nonempty_interior (μ i) (S i).interior_nonempty).ne'
  have h1 : ∀ i, μ i (S i : Set (A i)) ≠ ⊤ := fun i => (S i).isCompact.measure_lt_top.ne
  have hp : ∀ T : ∀ i, Set (A i), (Measure.pi μ) (Set.univ.pi T) = ∏ i, μ i (T i) := fun T =>
    Measure.pi_pi _ _
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := Measure.pi μ)
    (s := Set.univ.pi fun i => (S i : Set (A i)))
    (by rw [hp]; exact Finset.prod_ne_zero_iff.2 fun i _ => h0 i)
    (by rw [hp]; exact ENNReal.prod_ne_top fun i _ => h1 i) ?_
  have e : u • (Set.univ.pi fun i => (S i : Set (A i))) =
      Set.univ.pi fun i => Units.map (Pi.evalRingHom A i).toMonoidHom u • (S i : Set (A i)) := by
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_pi, Set.mem_univ, forall_true_left]
    refine forall_congr' fun i => ?_
    rw [← map_inv]
    rfl
  rw [e, hp, hp]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [distribHaarChar_mul]

end GlobalTheory.ModuPiLocal

namespace GlobalTheory.ModuPiLocal

theorem modu_sPart : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (x : SPart F S), IsUnit x → (modu (SPart F S) x : ℝ) = ∏ v : S, ‖x v‖ := by
  intro F _ _ S x hx
  rw [modu, dite_eq_left hx, distribHaarChar_pi (fun v : S => Fv F v.1), NNReal.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  have hv : IsUnit (x v) := (Pi.isUnit_iff.1 hx) v
  have h := GlobalTheory.GaugeProdFormula.modu_finite F v.1 (x v) hv.ne_zero
  rw [modu, dite_eq_left hv] at h
  rw [← h]
  congr 2
  ext
  rfl

end GlobalTheory.ModuPiLocal
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.ModuArtin

theorem addEquivAddHaarChar_mulVecCE (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [LocallyCompactSpace B] [T2Space B] [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B] :
    IsArtinianRing B → IsReduced B → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [MeasurableSpace (κ → B)]
      [BorelSpace (κ → B)] (M : Matrix κ κ B) (hM : IsUnit M.det),
      addEquivAddHaarChar (mulVecCE M hM) = modu B M.det := by
  intro hA hR κ _ _ inst hB M hM
  have heq : inst = MeasurableSpace.pi := by
    exact hB.measurable_eq.trans (@BorelSpace.measurable_eq (κ → B) _ MeasurableSpace.pi Pi.borelSpace).symm
  subst heq
  set ν : Measure B := Measure.addHaar
  set μ : Measure (κ → B) := Measure.pi fun _ : κ => ν
  have h1 := addEquivAddHaarChar_smul_map μ (mulVecCE M hM)
  have h2 : (modu B M.det : ℝ≥0∞) • Measure.map M.mulVec μ = μ :=
    GlobalTheory.GaugeEx.ModDet.smul_map_mulVec_pi ν M hM
  have hfun : ⇑(mulVecCE M hM) = M.mulVec := funext fun x => mulVecCE_apply M hM x
  rw [hfun] at h1
  obtain ⟨K⟩ := (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (κ → B)))
  have hpos : μ K ≠ 0 := ((isOpen_interior.measure_pos μ K.interior_nonempty).trans_le
    (measure_mono interior_subset)).ne'
  have hfin : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  set m := (Measure.map M.mulVec μ) (K : Set (κ → B))
  have e1 : (addEquivAddHaarChar (mulVecCE M hM) : ℝ≥0∞) * m = μ K := by
    conv_rhs => rw [← h1]
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have e2 : (modu B M.det : ℝ≥0∞) * m = μ K := by
    conv_rhs => rw [← h2]
    rw [Measure.smul_apply, smul_eq_mul]
  have hm0 : m ≠ 0 := by
    intro h; rw [h, mul_zero] at e1; exact hpos e1.symm
  have hmt : m ≠ ⊤ := by
    intro h
    rw [h] at e1
    have hc : (addEquivAddHaarChar (mulVecCE M hM) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (addEquivAddHaarChar_pos (mulVecCE M hM)).ne'
    rw [ENNReal.mul_top hc] at e1
    exact hfin e1.symm
  have := (ENNReal.mul_left_inj hm0 hmt).1 (e1.trans e2.symm)
  exact_mod_cast this

end GlobalTheory.ModuArtin
end
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.exists_restrictScalars_matrix_leftRightMul_adeleTensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (m n : ℕ) [LocallyCompactSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [SecondCountableTopology (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [MeasurableSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] [BorelSpace (Matrix (Fin m) (Fin n) (AF F ⊗[F] E))] (g : GL (Fin m) (AF F ⊗[F] E)) (a : GL (Fin n) (AF F ⊗[F] E)), ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (Λ : Matrix κ κ (AF F)) (hΛ : IsUnit Λ.det), Λ.det = Algebra.norm (AF F) ((Matrix.GeneralLinearGroup.det g ^ n * Matrix.GeneralLinearGroup.det a ^ m : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) ∧ addEquivAddHaarChar (lrCE g a) = addEquivAddHaarChar (mulVecCE Λ hΛ) := by
  first | exact @GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE | exact GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE | (intros; apply GlobalTheory.ModuLR.exists_matrix_restrictScalars_lrCE <;> assumption)
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.UnipCompact

variable {n : Type}

theorem conc_mul_sub (c : n → ℤ) (m : ℕ) : GlobalTheory.IwahoriInj.Conc fun i j => (m : ℤ) * (c i - c j) :=
  ⟨fun i => by simp, fun i j l => le_of_eq (by ring)⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Fintype n] [DecidableEq n]

theorem isClosed_unipOf (c : n → ℤ) : IsClosed (GlobalTheory.InertSupp.unipOf k c : Set (GL n k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (GlobalTheory.InertSupp.unipOf k c : Set (GL n k)) =
      ⋂ i, ⋂ j, ⋂ (_ : ¬ c i < c j), {g : GL n k | (g : Matrix n n k) i j = (1 : Matrix n n k) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipOf, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

theorem eventually_mem_grp {c : n → ℤ} {u : GL n k} (hu : u ∈ GlobalTheory.InertSupp.unipOf k c) :
    ∀ᶠ m : ℕ in Filter.atTop, u ∈ GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) := by
  have key : ∀ u ∈ GlobalTheory.InertSupp.unipOf k c, ∀ᶠ m : ℕ in Filter.atTop,
      ∀ i j, Deep ((m : ℤ) * (c i - c j)) (u.val i j) := by
    intro u hu
    simp only [Filter.eventually_all]
    intro i j
    by_cases h : c i < c j
    · filter_upwards [GlobalTheory.IwahoriInj.eventually_deep (u.val i j)] with m hm
      refine hm.mono ?_
      nlinarith [Int.natCast_nonneg m]
    · rw [GlobalTheory.InertSupp.mem_unipOf.1 hu i j h]
      refine Filter.Eventually.of_forall fun m => ?_
      by_cases hij : i = j
      · subst hij
        simp [GlobalTheory.IwahoriInj.deep_zero_iff]
      · simp [one_apply_ne hij, GlobalTheory.IwahoriInj.deep_zero]
  exact (key u hu).and (key _ (inv_mem hu))

theorem exists_compact_subgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : n → ℤ) (S : Finset (GL n k))
    (hS : ∀ u ∈ S, u ∈ GlobalTheory.InertSupp.unipOf k c) :
    ∃ H : Subgroup (GL n k), H ≤ GlobalTheory.InertSupp.unipOf k c ∧ IsCompact (H : Set (GL n k)) ∧ ∀ u ∈ S, u ∈ H := by
  obtain ⟨m, hm⟩ := ((Filter.eventually_all_finset S).2 fun u hu => eventually_mem_grp (hS u hu)).exists
  refine ⟨GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) ⊓ GlobalTheory.InertSupp.unipOf k c, inf_le_right, ?_,
    fun u hu => ⟨hm u hu, hS u hu⟩⟩
  rw [Subgroup.coe_inf]
  let f : n → n → ℤ := fun i j => (m : ℤ) * (c i - c j)
  have hK : IsCompact {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} := by
    have h : IsCompact (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n =>
        {x : k | Deep (f i j) x}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
        IsNonarchimedeanLocalField.isCompact_closedBall k _
    have e : {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} =
        (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n =>
          {x : k | Deep (f i j) x}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]
    exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  have hgrp : IsCompact (GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) : Set (GL n k)) := by
    convert h using 1
    ext g
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply,
      Set.mem_prod, (MulOpposite.op_injective).mem_set_image]
    rfl
  exact hgrp.inter_right (isClosed_unipOf c)

end GlobalTheory.UnipCompact
end
end

section

open Matrix

namespace GlobalTheory.RegSS

private theorem aeval_mul_mulVec {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f g : Polynomial K) (v : n → K) :
    Polynomial.aeval M (f * g) *ᵥ v = Polynomial.aeval M f *ᵥ (Polynomial.aeval M g *ᵥ v) := by
  rw [map_mul, Matrix.mulVec_mulVec]

private theorem det_aeval_eq_zero_of_irreducible_dvd_charpoly {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) {q : Polynomial K} (hq : Irreducible q)
    (hd : q ∣ M.charpoly) : (Polynomial.aeval M q).det = 0 := by
  have : Fact (Irreducible q) := ⟨hq⟩
  obtain ⟨s, hs⟩ := hd
  have hα : Polynomial.aeval (AdjoinRoot.root q) q = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hroot : (q.map (algebraMap K (AdjoinRoot q))).IsRoot (AdjoinRoot.root q) := by
    rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, hα]
  obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hN : (Matrix.scalar n (AdjoinRoot.root q) - M.map (algebraMap K (AdjoinRoot q))).det = 0 := by
    rw [← Matrix.eval_charpoly, Matrix.charpoly_map, hs, Polynomial.map_mul, Polynomial.eval_mul,
      Polynomial.eval_map_algebraMap, hα, zero_mul]
  have hmap : Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) q =
      (Polynomial.aeval M q).map (algebraMap K (AdjoinRoot q)) := by
    exact Polynomial.aeval_algHom_apply ((Algebra.ofId K (AdjoinRoot q)).mapMatrix (m := n)) M q
  have hfac : Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) q =
      (M.map (algebraMap K (AdjoinRoot q)) - Matrix.scalar n (AdjoinRoot.root q)) *
        Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) g := by
    rw [← Polynomial.aeval_map_algebraMap (AdjoinRoot q), hg, map_mul, map_sub, Polynomial.aeval_X,
      Polynomial.aeval_C]
    congr 2
  have h2 : (Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) q).det = 0 := by
    rw [hfac, Matrix.det_mul, ← neg_sub, Matrix.det_neg, hN, mul_zero, zero_mul]
  have h3 : algebraMap K (AdjoinRoot q) (Polynomial.aeval M q).det = 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hmap, h2]
  exact (map_eq_zero_iff _ (algebraMap K (AdjoinRoot q)).injective).mp h3

private theorem exists_vec_annihilator_eq_of_dvd_charpoly {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hsq : Squarefree M.charpoly) (q : Polynomial K) :
    q ∣ M.charpoly → ∃ w : n → K, Polynomial.aeval M q *ᵥ w = 0 ∧
      ∀ f : Polynomial K, Polynomial.aeval M f *ᵥ w = 0 → q ∣ f := by
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro h
    exact absurd (zero_dvd_iff.mp h) M.charpoly_monic.ne_zero
  · intro x hx _
    exact ⟨0, Matrix.mulVec_zero _, fun _ _ => hx.dvd⟩
  · intro r π _ hπ ih hd
    obtain ⟨wr, hwr0, hwr⟩ := ih (dvd_trans (dvd_mul_left r π) hd)
    obtain ⟨wp, hwpne, hwp0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
      (det_aeval_eq_zero_of_irreducible_dvd_charpoly M hπ.irreducible (dvd_trans (dvd_mul_right π r) hd))
    have hcop : IsCoprime π r := by
      rw [hπ.coprime_iff_not_dvd]
      rintro ⟨t, rfl⟩
      exact hπ.not_isUnit (hsq π (dvd_trans ⟨t, by ring⟩ hd))
    have hwp : ∀ f : Polynomial K, Polynomial.aeval M f *ᵥ wp = 0 → π ∣ f := by
      intro f hf
      by_contra hn
      obtain ⟨a, b, hab⟩ := hπ.coprime_iff_not_dvd.mpr hn
      apply hwpne
      have h0 : Polynomial.aeval M (a * π + b * f) *ᵥ wp = 0 := by
        rw [map_add (f := _), Matrix.add_mulVec, aeval_mul_mulVec, aeval_mul_mulVec, hwp0, hf,
          Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
      rwa [hab, map_one, Matrix.one_mulVec] at h0
    refine ⟨wr + wp, ?_, ?_⟩
    · have e1 : Polynomial.aeval M (π * r) *ᵥ wr = 0 := by
        rw [aeval_mul_mulVec, hwr0, Matrix.mulVec_zero]
      have e2 : Polynomial.aeval M (π * r) *ᵥ wp = 0 := by
        rw [mul_comm π r, aeval_mul_mulVec, hwp0, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, e1, e2, add_zero]
    · intro f hf
      have hfp : Polynomial.aeval M (f * π) *ᵥ wp = 0 := by
        rw [aeval_mul_mulVec, hwp0, Matrix.mulVec_zero]
      have hfw : Polynomial.aeval M (f * π) *ᵥ (wr + wp) = 0 := by
        rw [mul_comm f π, aeval_mul_mulVec, hf, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, hfp, add_zero] at hfw
      have hrw : Polynomial.aeval M (f * r) *ᵥ wr = 0 := by
        rw [aeval_mul_mulVec, hwr0, Matrix.mulVec_zero]
      have hgw : Polynomial.aeval M (f * r) *ᵥ (wr + wp) = 0 := by
        rw [mul_comm f r, aeval_mul_mulVec, hf, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, hrw, zero_add] at hgw
      exact hcop.mul_dvd (hcop.dvd_of_dvd_mul_right (hwp _ hgw))
        (hcop.symm.dvd_of_dvd_mul_right (hwr _ hfw))

theorem cyclicField : GlobalTheory.RegSS.CyclicField := by
  intro K _ n _ _ M hsep
  obtain ⟨v, -, hv⟩ := exists_vec_annihilator_eq_of_dvd_charpoly M hsep.squarefree M.charpoly dvd_rfl
  refine ⟨v, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hc0
  set e := Fintype.equivFin n
  set f : Polynomial K := ∑ i : Fin (Fintype.card n),
    Polynomial.C (c (e.symm i)) * Polynomial.X ^ (i : ℕ) with hfdef
  have haeval : Polynomial.aeval M f = ∑ j : n, c j • M ^ ((e j : ℕ)) := by
    rw [hfdef, ← Equiv.sum_comp e]
    simp [Algebra.smul_def]
  have hf : Polynomial.aeval M f *ᵥ v = 0 := by
    rw [← hc, haeval]
    ext k
    simp only [krylov, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hf0 : f = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt (hv f hf) ?_
    rw [Matrix.charpoly_degree_eq_dim]
    exact Polynomial.degree_sum_fin_lt _
  funext j
  have hcoef := congrArg (fun g : Polynomial K => g.coeff (e j : ℕ)) hf0
  simpa [hfdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using hcoef

end GlobalTheory.RegSS
end

section

noncomputable section

namespace GlobalTheory.RegSS

def monomialChar (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (s : ℕ) (a : Fin s → ℤ) :
    (Fin s → Fˣ) →* Ω where
  toFun t := algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)
  map_one' := by simp
  map_mul' x y := by
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, map_mul]

theorem characterMonomial : CharacterMonomial := by
  classical
  intro F Ω _ _ _ s f S c hf
  by_contra hno

  have hdiff : ∀ a, monomialChar F Ω s a ≠ f := by
    intro a hEq
    refine hno ⟨a, fun t => ?_⟩
    rw [← hEq]
    rfl

  let l : ((Fin s → Fˣ) →* Ω) →₀ Ω :=
    Finsupp.single f 1 - ∑ a ∈ S, Finsupp.single (monomialChar F Ω s a) (c a)
  have hvanish : Finsupp.linearCombination Ω
      (fun φ : (Fin s → Fˣ) →* Ω => (φ : (Fin s → Fˣ) → Ω)) l = 0 := by
    funext t

    simp only [l, map_sub, map_sum, Finsupp.linearCombination_single, one_smul,
    Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hf t]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    show _ = c a * algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)
    rw [Algebra.smul_def, mul_comm]
  have hl0 : l = 0 := (linearIndependent_iff.mp (linearIndependent_monoidHom _ Ω)) l hvanish
  have hlf : l f = 1 := by
    simp only [l, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_zero fun a _ => Finsupp.single_eq_of_ne' (hdiff a), sub_zero]
  rw [hl0, Finsupp.zero_apply] at hlf
  exact zero_ne_one hlf

end GlobalTheory.RegSS
end
end
