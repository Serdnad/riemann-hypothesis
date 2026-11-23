module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.HeckeRepresentationSatake
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
public import GroundTheory.LocalFields.Unramified
public import GroundTheory.LocalFields.UnramifiedGalois
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle004
public import GroundTheory.LocalFields.Interface
public import GroundTheory.LocalFields.Uniqueness

@[expose] public section

section

open ValuativeRel UpperTheory.ConvolutionTheory.Loc

section

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private theorem bd_mul {a b : ValueGroupWithZero E} {M N : Matrix (Fin n) (Fin n) E} (h : ∀ i j, valuation E (M i j) ≤ a)
    (h' : ∀ i j, valuation E (N i j) ≤ b) (i j : Fin n) : valuation E ((M * N) i j) ≤ a * b := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (h i k) (h' k j)

private theorem bd_one (i j : Fin n) : valuation E ((1 : Matrix (Fin n) (Fin n) E) i j) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

private theorem bd_inv {r : ValueGroupWithZero E} (hr : r < 1) {A H : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, valuation E (A i j) ≤ r)
    (hH : H = 1 - H * A) (i j : Fin n) : valuation E (H i j) ≤ 1 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun p : Fin n × Fin n => valuation E (H p.1 p.2)) ⟨(i, j), Finset.mem_univ _⟩
  refine (hp (i, j) (Finset.mem_univ _)).trans ?_
  by_contra hc
  push Not at hc
  have h1 := bd_mul (fun a b => hp (a, b) (Finset.mem_univ _)) hA p.1 p.2
  have h2 : valuation E ((H * A) p.1 p.2) < valuation E (H p.1 p.2) :=
    h1.trans_lt (mul_lt_of_lt_one_right (zero_lt_one.trans hc) hr)
  have h3 : valuation E ((1 - H * A) p.1 p.2) < valuation E (H p.1 p.2) :=
    Valuation.map_sub_lt _ ((bd_one _ _).trans_lt hc) h2
  rw [← hH] at h3
  exact lt_irrefl _ h3

end

theorem UpperTheory.ConvolutionTheory.Loc.ballSub :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (r : ValueGroupWithZero E), 0 < r → r < 1 →
      ∃ K : Subgroup (GL (Fin n) E), (K : Set (GL (Fin n) E)) = ball n r ∧ IsOpen (K : Set (GL (Fin n) E)) ∧ IsCompact (K : Set (GL (Fin n) E)) := by
  intro E _ _ _ _ n r h0 h1
  have mb : ∀ {g : GL (Fin n) E}, g ∈ ball n r → ∀ i j, valuation E (((g : Matrix (Fin n) (Fin n) E) - 1) i j) ≤ r := fun hg i j => hg i j
  have hinv : ∀ g ∈ ball (E := E) n r, g⁻¹ ∈ ball n r := by
    intro g hg i j
    have e : ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 - (g⁻¹ : GL (Fin n) E) * ((g : Matrix (Fin n) (Fin n) E) - 1) := by
      rw [mul_sub, Units.inv_mul]; simp
    have h := bd_mul (bd_inv h1 (mb hg) e) (mb hg) i j
    rw [one_mul] at h
    rw [e, Matrix.sub_apply, sub_sub_cancel_left, Valuation.map_neg]
    exact h
  let K : Subgroup (GL (Fin n) E) :=
    { carrier := ball n r
      one_mem' := fun i j => by simp
      inv_mem' := fun {g} hg => hinv g hg
      mul_mem' := fun {a b} ha hb i j => by
        have e : ((a * b : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1 =
            ((a : Matrix (Fin n) (Fin n) E) - 1) * ((b : Matrix (Fin n) (Fin n) E) - 1) + ((a : Matrix (Fin n) (Fin n) E) - 1) +
              ((b : Matrix (Fin n) (Fin n) E) - 1) := by
          rw [Units.val_mul]; noncomm_ring
        rw [← Matrix.sub_apply, e]
        refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ (ha i j)) (hb i j)
        exact (bd_mul (mb ha) (mb hb) i j).trans
          (mul_le_of_le_one_right' h1.le) }
  have hent : ∀ i j, Continuous fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j :=
    fun i j => (Units.continuous_val.matrix_elem i j).sub continuous_const
  refine ⟨K, rfl, K.isOpen_of_mem_nhds (g := 1) ?_, ?_⟩
  · have hb : {x : E | valuation E x < r} ∈ nhds (0 : E) :=
      (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 r h0.ne', subset_rfl⟩
    have : ∀ᶠ g : GL (Fin n) E in nhds 1, ∀ i j,
        valuation E ((g : Matrix (Fin n) (Fin n) E) i j - (1 : Matrix (Fin n) (Fin n) E) i j) < r := by
      refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      exact (hent i j).continuousAt.preimage_mem_nhds (t := {x : E | valuation E x < r}) (by simpa using hb)
    exact this.mono fun g hg i j => (hg i j).le
  · have hc : IsCompact {M : Matrix (Fin n) (Fin n) E | ∀ i j, valuation E (M i j) ≤ r} :=
      isCompact_pi_infinite (s := fun _ : Fin n => {x : Fin n → E | ∀ j, x j ∈ {y | valuation E y ≤ r}})
        fun _ => isCompact_pi_infinite fun _ => IsNonarchimedeanLocalField.isCompact_closedBall E r
    have hc' := hc.image (f := fun M => M + 1) (by fun_prop)
    have h := (UpperTheory.V.Z.Tf.Orb.gLTop E n).2.2.2.2 _ _ hc' hc'
    convert h using 1
    ext g
    constructor
    · intro hg
      exact ⟨⟨_, mb hg, sub_add_cancel _ _⟩, ⟨_, mb (hinv g hg), sub_add_cancel _ _⟩⟩
    · rintro ⟨⟨M, hM, e⟩, -⟩ i j
      rw [← e]
      simpa using hM i j
end

section

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc

private theorem iter_eq {k E : Type} [Field k] [Field E] [Algebra k E] (σ : E ≃ₐ[k] E) (j : ℕ) (x : E) :
    (σ : E ≃+* E)^[j] x = (σ ^ j) x := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, pow_succ']; rfl

private theorem mem_range_incl {k E : Type} [Field k] [Field E] [Algebra k E] {n : ℕ} (g : GL (Fin n) E) :
    (∃ y : GL (Fin n) k, incl y = g) ↔
      ∀ i j, (g : Matrix (Fin n) (Fin n) E) i j ∈ Set.range (algebraMap k E) := by
  constructor
  · rintro ⟨y, rfl⟩ i j
    exact ⟨(y : Matrix (Fin n) (Fin n) k) i j, rfl⟩
  · intro h
    choose M hM using h
    have e : (algebraMap k E).mapMatrix (Matrix.of M) = (g : Matrix (Fin n) (Fin n) E) := by
      ext i j
      exact hM i j
    have hd : (Matrix.of M).det ≠ 0 := by
      intro h0
      have h1 := RingHom.map_det (algebraMap k E) (Matrix.of M)
      rw [h0, map_zero, e] at h1
      exact (Matrix.GeneralLinearGroup.det g).ne_zero h1.symm
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩
    ext i j
    exact hM i j

section

variable (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]

private theorem closedEmb_alg : Topology.IsClosedEmbedding (algebraMap k E) := by
  let _ := GroundTheory.LocalField.nontriviallyNormedField k
  have := GroundTheory.LocalField.completeSpace_nontriviallyNormedField k
  have := GroundTheory.LocalField.t2Space_of_isNonarchimedeanLocalField E
  exact LinearMap.isClosedEmbedding_of_injective (f := Algebra.linearMap k E)
    (LinearMap.ker_eq_bot.mpr (algebraMap k E).injective)

private theorem closedEmb_incl (n : ℕ) :
    Topology.IsClosedEmbedding (incl : GL (Fin n) k → GL (Fin n) E) := by
  have h := closedEmb_alg k E
  have hM : Topology.IsEmbedding
      ((algebraMap k E).mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) k →* Matrix (Fin n) (Fin n) E) :=
    Topology.IsEmbedding.piMap (f := fun _ : Fin n => Pi.map fun _ : Fin n => algebraMap k E)
      fun _ => Topology.IsEmbedding.piMap fun _ => h.isEmbedding
  refine ⟨hM.units_map, ?_⟩
  have e : Set.range (incl : GL (Fin n) k → GL (Fin n) E) =
      ⋂ i, ⋂ j, (fun g : GL (Fin n) E => (g : Matrix (Fin n) (Fin n) E) i j) ⁻¹' Set.range (algebraMap k E) := by
    ext g
    simp only [Set.mem_iInter, Set.mem_preimage]
    exact mem_range_incl g
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => h.isClosed_range.preimage ?_
  exact Units.continuous_val.matrix_elem i j

private theorem ram_one (h : IsUnramifiedLoc k E) : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation k))) = 1 := by
  obtain ⟨π, hπ, hmax⟩ := h
  have key : ∀ x : 𝒪[E], x ∈ IsLocalRing.maximalIdeal 𝒪[E] ↔ valuation E (x : E) < 1 := by
    intro x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩
  have hπk : π ∈ 𝒪[k] := (GroundTheory.LocalField.algebraMap_mem_integer_iff k E π).1 hπ.le
  have hm : (⟨π, hπk⟩ : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro hu
    exact (key _).2 hπ (hu.map (algebraMap 𝒪[k] 𝒪[E]))
  rw [← GroundTheory.LocalField.isUnramified_iff, ← GroundTheory.LocalField.map_maximalIdeal_eq_iff]
  refine le_antisymm ?_ fun x hx => ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy hu
    exact hy (isUnit_of_map_unit _ _ hu)
  · have hd : algebraMap 𝒪[k] 𝒪[E] ⟨π, hπk⟩ ∣ x :=
      (Valuation.integer.integers (valuation E)).dvd_of_le (hmax _ ((key x).1 hx))
    exact Ideal.mem_of_dvd _ hd (Ideal.mem_map_of_mem _ hm)

private theorem res_move (h : IsUnramifiedLoc k E) (τ : E ≃ₐ[k] E) (hτ : τ ≠ 1) :
    ∃ x, valuation E x ≤ 1 ∧ valuation E (τ x - x) = 1 := by
  by_contra hc
  push Not at hc
  apply hτ
  apply GroundTheory.LocalField.residueAlgEquiv_injective_of_unramified k E (ram_one k E h)
  rw [map_one]
  ext z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  rw [GroundTheory.LocalField.residueAlgEquiv_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one]
  exact hc x x.2

end

theorem UpperTheory.ConvolutionTheory.Loc.bridge :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
        [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
        [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), Cyc (σ : E ≃+* E) (Module.finrank k E) ∧
      (IsUnramifiedLoc k E → (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → Unram (σ : E ≃+* E) (Module.finrank k E)) ∧
      ∀ n : ℕ, (∀ g : GL (Fin n) E, sg (σ : E ≃+* E) g = sigmaGL σ g) ∧ (∀ g : GL (Fin n) E, nrm (σ : E ≃+* E) (Module.finrank k E) g = normGL σ g) ∧
        ((∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ g : GL (Fin n) E, sigmaGL σ g = g ↔ ∃ y : GL (Fin n) k, incl y = g) ∧
        Topology.IsClosedEmbedding (incl : GL (Fin n) k → GL (Fin n) E) ∧
        iwahori (m := n) E = (GlobalTheory.SmGL.iwahori E (Fin n) : Set (GL (Fin n) E)) := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ
  have hc : Cyc (σ : E ≃+* E) (Module.finrank k E) := by
    refine ⟨fun x => GroundTheory.LocalField.valuation_algEquiv_apply k E σ x, Module.finrank_pos, fun x => ?_⟩
    rw [iter_eq, ← IsGalois.card_aut_eq_finrank, pow_card_eq_one']
    rfl
  refine ⟨hc, fun hu hgen => ⟨hc, fun j hj hj' => ?_⟩, fun n => ⟨fun g => rfl, fun g => ?_, fun hgen g => ?_,
    closedEmb_incl k E n, ?_⟩⟩
  · simp only [iter_eq]
    refine res_move k E hu _ (pow_ne_one_of_lt_orderOf hj.ne' ?_)
    rwa [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  · unfold nrm normGL twNorm
    congr 2
  · rw [mem_range_incl]
    constructor
    · intro h i j
      have hσ : σ ∈ MulAction.stabilizer (E ≃ₐ[k] E) ((g : Matrix (Fin n) (Fin n) E) i j) :=
        congrArg (fun x : GL (Fin n) E => (x : Matrix (Fin n) (Fin n) E) i j) h
      have := (IsGalois.mem_bot_iff_fixed ((g : Matrix (Fin n) (Fin n) E) i j)).mpr fun τ =>
        (Subgroup.zpowers_le.mpr hσ) (hgen τ)
      rwa [IntermediateField.mem_bot] at this
    · intro h
      ext i j
      obtain ⟨y, hy⟩ := h i j
      show σ ((g : Matrix (Fin n) (Fin n) E) i j) = _
      rw [← hy, AlgEquiv.commutes]
  · ext g
    rw [SetLike.mem_coe, GlobalTheory.SmGL.mem_iwahori]
    rfl
end
