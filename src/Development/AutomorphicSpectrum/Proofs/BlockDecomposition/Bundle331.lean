module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle297
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle345
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle124
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle302
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle312
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
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
import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.EPGFalseEqLastIff
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle125
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto.Topo

open GlobalTheory.SplitWeil Topology

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def nearSet (s : kˣ) (m : ℕ) : Set (Matrix (Fin m) (Fin m) k) := {A | NearOne s A}

def ballMat (s : kˣ) (m : ℕ) : Set (Matrix (Fin m) (Fin m) k) := {B | ∀ a b, B a b ∈ cball s}

theorem ballMat_eq (s : kˣ) (m : ℕ) : ballMat (k := k) s m =
    (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => cball s : Set (Fin m → Fin m → k)) :=
  Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩

theorem isOpen_ballMat (s : kˣ) (m : ℕ) : IsOpen (ballMat (k := k) s m) := by
  simp only [ballMat, Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact (isOpen_cball s).preimage (f := fun A : Matrix (Fin m) (Fin m) k => A i j) (by fun_prop)

theorem isCompact_ballMat (s : kˣ) (m : ℕ) : IsCompact (ballMat (k := k) s m) := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m => cball s :
      Set (Fin m → Fin m → k)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball s
  rw [ballMat_eq]; exact h

theorem nearSet_eq (s : kˣ) (m : ℕ) : nearSet (k := k) s m =
    (Homeomorph.subRight (1 : Matrix (Fin m) (Fin m) k)) ⁻¹' ballMat s m := by
  ext A
  simp only [nearSet, NearOne, ballMat, Set.mem_setOf_eq, Set.mem_preimage, Homeomorph.subRight_apply,
    Matrix.sub_apply]

theorem isOpen_nearSet (s : kˣ) (m : ℕ) : IsOpen (nearSet (k := k) s m) := by
  rw [nearSet_eq]
  exact (isOpen_ballMat s m).preimage (Homeomorph.continuous _)

theorem isCompact_nearSet (s : kˣ) (m : ℕ) : IsCompact (nearSet (k := k) s m) := by
  rw [nearSet_eq]
  exact (Homeomorph.subRight (1 : Matrix (Fin m) (Fin m) k)).isCompact_preimage.2 (isCompact_ballMat s m)

theorem congGL_eq (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (m : ℕ) :
    (congGL k s hs m : Set (GL (Fin m) k)) =
      (fun g : GL (Fin m) k => (g : Matrix (Fin m) (Fin m) k)) ⁻¹' nearSet s m ∩
        (fun g : GL (Fin m) k => ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)) ⁻¹' nearSet s m :=
  rfl

theorem isOpen_congGL (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (m : ℕ) :
    IsOpen (congGL k s hs m : Set (GL (Fin m) k)) := by
  rw [congGL_eq]
  exact ((isOpen_nearSet s m).preimage Units.continuous_val).inter
    ((isOpen_nearSet s m).preimage Units.continuous_coe_inv)

theorem isCompact_congGL (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (m : ℕ) :
    IsCompact (congGL k s hs m : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hK := isCompact_nearSet (k := k) s m
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin m) (Fin m) k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  convert h using 1
  ext g
  simp only [congGL_eq, Set.mem_inter_iff, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, (MulOpposite.op_injective).mem_set_image]

end GlobalTheory.CompanionTheory.BZPhiPG.Onto.Topo

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

theorem congM_isOpen_isCompact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1),
  IsOpen (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) ∧ IsCompact (GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n : Set (Mir k n)) := by
  intro k _ _ _ _ n s hs
  have e : (congM k s hs n : Set (Mir k n)) =
      (Subtype.val : Mir k n → GL (Fin (n + 1)) k) ⁻¹' (congGL k s hs (n + 1) : Set (GL (Fin (n + 1)) k)) := rfl
  rw [e]
  exact ⟨(Topo.isOpen_congGL s hs (n + 1)).preimage continuous_subtype_val,
    (GlobalTheory.CompanionTheory.BZMirOnto.isClosed_Mir k n).isClosedEmbedding_subtypeVal.isCompact_preimage
      (Topo.isCompact_congGL s hs (n + 1))⟩

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
end

section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
open MeasureTheory GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl
open scoped Topology

namespace GlobalTheory.CompanionTheory.ThetaInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_ball (n : ℕ) (s : kˣ) :
    IsOpen {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} :=
  (isOpen_polyBall n s).preimage continuous_ofAdd

theorem isCompact_ball (n : ℕ) (s : kˣ) :
    IsCompact {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} := by
  have e : {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} =
      Multiplicative.toAdd '' (polyBall (k := k) n s : Set (Multiplicative (Fin n → k))) := by
    ext a
    constructor
    · intro h
      exact ⟨Multiplicative.ofAdd a, h, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [e]
  exact (isCompact_polyBall n s).image continuous_toAdd

theorem isLocallyConstant_of_periodic {n : ℕ} {Y : Type} (g : (Fin n → k) → Y) (s : kˣ)
    (h : ∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → g (v + a) = g v) :
    IsLocallyConstant g := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have h0 : (fun z : Fin n → k => -x + z) ⁻¹'
      {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} ∈ 𝓝 x :=
    ((isOpen_ball n s).preimage (by fun_prop)).mem_nhds (by
      show Multiplicative.ofAdd (-x + x) ∈ polyBall (k := k) n s
      rw [neg_add_cancel]
      exact one_mem _)
  filter_upwards [h0] with z hz
  have e : z = x + (-x + z) := by abel
  rw [e]
  exact h x _ hz

theorem hasCompactSupport_of_ball {n : ℕ} {E : Type} [AddCommGroup E] (g : (Fin n → k) → E) (S : kˣ)
    (h : ∀ v, g v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) : HasCompactSupport g := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine HasCompactSupport.intro (isCompact_ball n S) fun x hx => ?_
  by_contra h1
  exact hx (h x h1)

def tw (ψ : AddChar k Circle) {N : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]
    (g : (Fin (N + 1) → k) → E) : (Fin (N + 1) → k) → E :=
  fun v => ((ψ (-(v (Fin.last N))) : Circle) : ℂ) • g v

variable {N : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

theorem isLocallyConstant_tw (ψ : AddChar k Circle) (hψ : Continuous ψ)
    {g : (Fin (N + 1) → k) → E} (hg : IsLocallyConstant g) : IsLocallyConstant (tw ψ g) := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  have h1 : IsLocallyConstant fun v : Fin (N + 1) → k => ((ψ (-(v (Fin.last N))) : Circle) : ℂ) := by
    refine isLocallyConstant_of_periodic _ s fun v a ha => ?_
    have h2 : ψ (a (Fin.last N)) = 1 := hs _ (ha (Fin.last N))
    rw [Pi.add_apply, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv (a := a (Fin.last N)), h2,
      inv_one, mul_one]
  exact h1.comp₂ hg fun c x => c • x

theorem hasCompactSupport_tw (ψ : AddChar k Circle) {g : (Fin (N + 1) → k) → E} (S : kˣ)
    (h : ∀ v, g v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) :
    HasCompactSupport (tw ψ g) := by
  refine hasCompactSupport_of_ball _ S fun v hv => h v fun h0 => hv ?_
  simp [tw, h0]

section Int

variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (ν : Measure k)
  [ν.IsAddHaarMeasure]

theorem smInt_comp_inv_mulVec (g : GL (Fin (N + 1)) k) {φ : (Fin (N + 1) → k) → E}
    (l : IsLocallyConstant φ) :
    smInt (Measure.pi fun _ : Fin (N + 1) => ν) (φ ∘ ((g⁻¹ : GL (Fin (N + 1)) k) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) •
        smInt (Measure.pi fun _ : Fin (N + 1) => ν) φ := by
  have hm : ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) k, Measurable B.mulVec := fun B =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have key : ∀ B : Set (Fin (N + 1) → k), MeasurableSet B →
      (Measure.pi fun _ : Fin (N + 1) => ν)
          (((g⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec ⁻¹' B) =
        (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ENNReal) *
          (Measure.pi fun _ : Fin (N + 1) => ν) B := by
    intro B hB
    have h1 := GlobalTheory.WeilM.smul_map_mulVec_pi ν g.val (Matrix.GeneralLinearGroup.det g) rfl
    conv_lhs => rw [← h1]
    rw [Measure.smul_apply, Measure.map_apply (hm _) ((hm _) hB), smul_eq_mul]
    congr 2
    ext x
    simp only [Set.mem_preimage, mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  unfold smInt
  rw [smul_finsum]
  refine finsum_congr fun v => ?_
  rw [Set.preimage_comp, key (φ ⁻¹' {v}) (l.isOpen_fiber v).measurableSet, ENNReal.toReal_mul, smul_smul]
  congr 1
  simp [nabs]

end Int

theorem exists_twisted_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) (X E : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E] (r : X →ₗ[ℂ] (Fin (N + 1) → k) → E), (∀ f, ∃ s : kˣ, ∀ (v a : Fin (N + 1) → k), Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → r f (v + a) = r f v) → (∀ f, ∃ S : kˣ, ∀ v : Fin (N + 1) → k, r f v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) → ∀ (tr : (Fin (N + 1) → k) → X → X), (∀ a f v, r (tr a f) v = r f (v + a)) → ∀ (lev : GL (Fin (N + 1)) k → X → X) (A : GL (Fin (N + 1)) k → E →ₗ[ℂ] E), (∀ m f v, r (lev m f) v = A m (r f (((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec v))) → ∃ T : X →ₗ[ℂ] E, (∀ a f, T (tr a f) = ((ψ (a (Fin.last N)) : Circle) : ℂ) • T f) ∧ (∀ m : GL (Fin (N + 1)) k, m ∈ Mir k N → ∀ f, T (lev m f) = ((nabs k (Matrix.GeneralLinearGroup.det m) : ℝ) : ℂ) • A m (T f)) ∧ (∀ s : kˣ, (∀ a : Fin (N + 1) → k, Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → ψ (a (Fin.last N)) = 1) → ∃ c : ℂ, c ≠ 0 ∧ ∀ (b : X) (e : E), (∀ v, r b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s) (Classical.propDecidable _) e 0) → T b = c • e) := by
  intro k _ _ _ _ ψ hψ N X E _ _ _ _ r hper hsup tr htr lev A hlev
  borelize k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ : ∃ ν : Measure k, ν.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  let μ : Measure (Fin (N + 1) → k) := Measure.pi fun _ => ν
  haveI hμ : μ.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hl : ∀ f, IsLocallyConstant (tw ψ (r f)) := fun f => by
    obtain ⟨s, hs⟩ := hper f
    exact isLocallyConstant_tw ψ hψ (isLocallyConstant_of_periodic _ s fun v a ha => hs v a ha)
  have hc : ∀ f, HasCompactSupport (tw ψ (r f)) := fun f => by
    obtain ⟨S, hS⟩ := hsup f
    exact hasCompactSupport_tw ψ S hS
  let T : X →ₗ[ℂ] E :=
    { toFun := fun f => smInt μ (tw ψ (r f))
      map_add' := fun f g => by
        have e : tw ψ (r (f + g)) = tw ψ (r f) + tw ψ (r g) := by
          funext v
          simp [tw, map_add (f := _), smul_add]
        show smInt μ (tw ψ (r (f + g))) = smInt μ (tw ψ (r f)) + smInt μ (tw ψ (r g))
        rw [e, smInt_add μ (hl f) (hc f) (hl g) (hc g)]
      map_smul' := fun c f => by
        have e : tw ψ (r (c • f)) = (c • LinearMap.id : E →ₗ[ℂ] E) ∘ tw ψ (r f) := by
          funext v
          simp only [tw, Function.comp, map_smul, Pi.smul_apply, LinearMap.smul_apply, LinearMap.id_apply]
        show smInt μ (tw ψ (r (c • f))) = c • smInt μ (tw ψ (r f))
        rw [e, smInt_linear μ _ (hl f) (hc f)]
        rfl }
  have hT : ∀ f, T f = smInt μ (tw ψ (r f)) := fun _ => rfl
  refine ⟨T, ?_, ?_, ?_⟩
  · intro a f
    let L : E →ₗ[ℂ] E := ((ψ (a (Fin.last N)) : Circle) : ℂ) • LinearMap.id
    have e : tw ψ (r (tr a f)) = (L ∘ tw ψ (r f)) ∘ fun v => v + a := by
      funext v
      simp only [tw, Function.comp, htr, L, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      congr 1
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [Pi.add_apply]
      abel
    rw [hT, hT, e, smInt_comp_measurePreserving μ (measurePreserving_add_right μ a) ((hl f).comp _),
      smInt_linear μ L (hl f) (hc f)]
    rfl
  · intro m hm f
    have e : tw ψ (r (lev m f)) = (A m ∘ tw ψ (r f)) ∘
        ((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec := by
      funext v
      simp only [tw, Function.comp, hlev, map_smul]
      rw [mulVec_last_of_mem k _ (inv_mem hm) v]
    rw [hT, hT, e]
    refine (smInt_comp_inv_mulVec ν m ((hl f).comp _)).trans ?_
    congr 1
    exact smInt_linear μ (A m) (hl f) (hc f)
  · intro s hs
    have hLo := isOpen_ball (k := k) (N + 1) s
    have hLc := isCompact_ball (k := k) (N + 1) s
    refine ⟨(((μ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s}).toReal : ℝ) : ℂ), ?_, fun b e hb => ?_⟩
    · have h0 := (hLo.measure_pos μ ⟨0, one_mem (polyBall (k := k) (N + 1) s)⟩).ne'
      exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨h0, hLc.measure_lt_top.ne⟩)
    · have e' : tw ψ (r b) = Set.indicator {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} fun _ => e := by
        funext v
        by_cases hv : Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s
        · have h1 : ψ (v (Fin.last N)) = 1 := hs v hv
          simp only [tw]
          rw [hb v, if_pos hv, Set.indicator_of_mem (show v ∈ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} from hv),
            AddChar.map_neg_eq_inv, h1]
          simp
        · simp only [tw]
          rw [hb v, if_neg hv, Set.indicator_of_notMem (show v ∉ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} from hv),
            smul_zero]
      rw [hT, e', smInt_indicator]

end GlobalTheory.CompanionTheory.ThetaInt
end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.continuous_mirabolic_embedding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (embedding₂ k n) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM | exact GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.continuous_iotaM <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_parabolic_iff_mem_embedded : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (y : Mir k (m + j)), y ∈ MirabolicParabolic k m j ↔ embedding₂ k (m + j) y ∈ MirabolicParabolic k m (j + 1) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff_iotaM_mem | exact GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff_iotaM_mem | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.mem_mirabolicParabolic_iff_iotaM_mem <;> assumption)
end

section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

noncomputable section

namespace GlobalTheory.CompanionTheory.MirPair

section Alg

variable {k : Type} [Field k]

theorem uM_mul_uM (n : ℕ) (x y : Fin n → k) : uM n x * uM n y = uM n (x + y) := by
  unfold uM
  rw [← map_mul]
  rfl

theorem det_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) : (glEmbMat k n A).det = A.det := by
  have hrow : ∀ j : Fin n, GlobalTheory.BZMir.glEmbMat k n A (Fin.last n) (Fin.castSucc j) = 0 := by
    intro j
    simp [GlobalTheory.BZMir.glEmbMat]
  have hcorner : GlobalTheory.BZMir.glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
    simp [GlobalTheory.BZMir.glEmbMat]
  have hminor : (GlobalTheory.BZMir.glEmbMat k n A).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = A := by
    ext i j
    simp [GlobalTheory.BZMir.glEmbMat, Fin.succAbove_last]
  have hsign : ((-1 : k) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [Matrix.det_succ_row (GlobalTheory.BZMir.glEmbMat k n A) (Fin.last n), Fin.sum_univ_castSucc]
  simp only [hrow, hcorner, hminor, hsign, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, one_mul]

theorem det_one_add_colMat (n : ℕ) (v : Fin n → k) : (1 + colMat k n v).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · apply Finset.prod_eq_one
    intro i _
    by_cases hi : i = Fin.last n
    · subst hi
      simp [GlobalTheory.BZMir.colMat]
    · simp [GlobalTheory.BZMir.colMat, hi]
  · intro i j hji
    change j < i at hji
    have hj : j ≠ Fin.last n := by
      intro h
      subst h
      exact absurd hji (not_lt.mpr (Fin.le_last i))
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    simp [GlobalTheory.BZMir.colMat, hj]

theorem det_uM (n : ℕ) (y : Fin n → k) :
    GeneralLinearGroup.det ((uM n y : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact GlobalTheory.CompanionTheory.MirPair.det_one_add_colMat n y

theorem det_levi (n : ℕ) (g : GL (Fin n) k) :
    GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = GeneralLinearGroup.det g := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact GlobalTheory.CompanionTheory.MirPair.det_glEmbMat n (g : Matrix (Fin n) (Fin n) k)

theorem uM_mul_levi (n : ℕ) (g : GL (Fin n) k) (x : Fin n → k) :
    uM n x * levi k n g =
      levi k n g * uM n (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x) := by
  have h := GlobalTheory.BZMir.glEmb_mul_unip' k n g
    (Multiplicative.ofAdd (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x))
  have hx : (g : Matrix (Fin n) (Fin n) k) *ᵥ (Multiplicative.toAdd
      (Multiplicative.ofAdd (((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ x))) = x := by
    rw [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  rw [hx] at h
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact h.symm

end Alg

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem coef_rules (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ) (hB : TwInv T T' B s) :
    (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B (T (uM (n + 1) y) v) v' x = coef T B v v' (x + y)) ∧
    (∀ (y x : Fin (n + 1) → k) (v : V) (v' : V'), coef T B v (T' (uM (n + 1) y) v') x = coef T B v v' (x - y)) ∧
    (∀ (g : GL (Fin (n + 1)) k) (x : Fin (n + 1) → k) (v : V) (v' : V'),
      coef T B (T (levi k (n + 1) g) v) (T' (levi k (n + 1) g) v') x =
        ((detChar (Fin (n + 1)) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) *
          coef T B v v' (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x)) := by
  unfold GlobalTheory.CompanionTheory.MirPair.TwInv at hB
  have hT : ∀ (a b : GlobalTheory.BZMir.Mir k (n + 1)) (w : V), T a (T b w) = T (a * b) w := by
    intro a b w
    rw [map_mul, Module.End.mul_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro y x v v'
    simp only [GlobalTheory.CompanionTheory.MirPair.coef]
    rw [hT, GlobalTheory.CompanionTheory.MirPair.uM_mul_uM]
  · intro y x v v'
    simp only [GlobalTheory.CompanionTheory.MirPair.coef]
    have hxy : y + (x - y) = x := by abel
    have h := hB (GlobalTheory.CompanionTheory.MirPair.uM (n + 1) y) (T (GlobalTheory.CompanionTheory.MirPair.uM (n + 1) (x - y)) v) v'
    rw [GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.det_uM, map_one, Units.val_one, one_mul,
      hT, GlobalTheory.CompanionTheory.MirPair.uM_mul_uM, hxy] at h
    exact h
  · intro g x v v'
    simp only [GlobalTheory.CompanionTheory.MirPair.coef]
    rw [hT, GlobalTheory.CompanionTheory.MirPair.uM_mul_levi, ← hT, hB, GlobalTheory.SmGL.detChar_apply,
      GlobalTheory.SmGL.detChar_apply, GlobalTheory.CompanionTheory.MirPair.det_levi]

end Rep

end GlobalTheory.CompanionTheory.MirPair

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem exists_Qp_mul_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (g : GL (Fin (i + t)) k), ∃ q : Qp k i t, ∃ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), g = (q : GL (Fin (i + t)) k) * κ := by
  intro k _ _ _ _ i t g
  obtain ⟨u, l, w, hw, hg⟩ := GlobalTheory.SmGL.UnitInd.exists_iwasawa
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : i + t = i + t))) g
  refine ⟨⟨(u : GL (Fin (i + t)) k) * GlobalTheory.SmGL.leviEmb k _ l, ?_⟩, w, hw, hg⟩
  exact Subgroup.mul_mem _ (GlobalTheory.SmGL.unipRad_le_parab k _ u.2)
    (GlobalTheory.SmGL.leviEmb_mem_parab k _ l)

end GlobalTheory.CompanionTheory.BZPsiPG
end
