module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle050
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSplitCongruenceIdelesOfFinPartEqOne
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeylFour

theorem schr_fourV_loc : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl (F := F)) (κ : Type) [Fintype κ]
    (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    fourV ψ v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (w.2, -w.1) (fourV ψ v φ) := by
  intro F _ _ ψ _ v κ _ w φ
  haveI hOc : CompactSpace (v.adicCompletionIntegers F) :=
    GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  haveI : LocallyCompactSpace (Fv F v) :=
    (isCompact_iff_compactSpace.2 hOc).locallyCompactSpace_of_mem_nhds_of_addGroup
      ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem (v.adicCompletionIntegers F)))
  haveI : SecondCountableTopology (Fv F v) := by
    have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    have : TopologicalSpace.SeparableSpace (Fv F v) :=
      ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
        IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
    exact UniformSpace.secondCountable_of_separable (Fv F v)
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hinv : (measV ψ v).IsAddLeftInvariant ∧ SigmaFinite (measV ψ v) := by
    unfold measV
    split_ifs with h
    · haveI := h.choose_spec.1
      exact ⟨inferInstance, inferInstance⟩
    · exact ⟨⟨fun g => by simp⟩, inferInstance⟩
  haveI := hinv.1
  haveI := hinv.2
  have h2 : (⅟2 : Fv F v) + ⅟2 = 1 := by rw [← two_mul, mul_invOf_self]
  funext y
  simp only [fourV, schr]
  set χ := GlobalTheory.LatVac.psiAt ψ v
  set μ := Measure.pi fun _ : κ => measV ψ v
  let g : (κ → Fv F v) → ℂ := fun x =>
    χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ x * χ ((x - w.1) ⬝ᵥ y)
  have hg : ∀ x, χ (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ (x + w.1) * χ (x ⬝ᵥ y) = g (x + w.1) := by
    intro x; simp only [g, add_sub_cancel_right]
  simp_rw [hg]
  rw [integral_add_right_eq_self g w.1, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [g]
  have key : (x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) + (x - w.1) ⬝ᵥ y =
      y ⬝ᵥ (-w.1) + ⅟(2 : Fv F v) * (w.2 ⬝ᵥ (-w.1)) + x ⬝ᵥ (y + w.2) := by
    simp only [sub_dotProduct, dotProduct_add, dotProduct_neg]
    rw [dotProduct_comm y w.1, dotProduct_comm w.2 w.1]
    linear_combination (w.1 ⬝ᵥ w.2) * h2
  calc χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * φ x * χ ((x - w.1) ⬝ᵥ y)
      = φ x * (χ ((x - w.1) ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * χ ((x - w.1) ⬝ᵥ y)) := by ring
    _ = φ x * χ (y ⬝ᵥ (-w.1) + ⅟(2 : Fv F v) * (w.2 ⬝ᵥ (-w.1)) + x ⬝ᵥ (y + w.2)) := by
      rw [← AddChar.map_add_eq_mul, key]
    _ = _ := by rw [AddChar.map_add_eq_mul]; ring

end GlobalTheory.WeylFour
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F]

theorem exists_circle_conductor (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F)) (h1 : ∃ x, psiLoc ψ v x ≠ 1) :
    ∃ (χ : AddChar (Fv F v) Circle) (c : (Fv F v)ˣ), GlobalTheory.SplitWeil.HasConductor χ c ∧
      ∀ x, (χ x : ℂ) = GlobalTheory.LatVac.psiAt ψ v x := by
  have hc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hψ v
  let χ : AddChar (Fv F v) Circle :=
    { toFun := fun x => ⟨GlobalTheory.LatVac.psiAt ψ v x, mem_sphere_zero_iff_norm.2 (GlobalTheory.norm_addChar_nonarch _ hc x)⟩
      map_zero_eq_one' := Circle.ext (by simp)
      map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul _ a b) }
  have hχ : ∀ x, (χ x : ℂ) = GlobalTheory.LatVac.psiAt ψ v x := fun _ => rfl
  have hχc : Continuous χ := continuous_induced_rng.2 hc
  have hχ1 : χ ≠ 1 := fun h => by
    obtain ⟨x, hx⟩ := h1
    refine hx ?_
    rw [← GlobalTheory.LatVac.psiAt_apply, ← hχ, h]
    simp
  obtain ⟨c, hc0⟩ := GlobalTheory.SplitWeil.exists_hasConductor_of_continuous χ hχc hχ1
  exact ⟨χ, c, hc0, hχ⟩

theorem isSelfDualFor_measV (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl (F := F)) (h1 : ∃ x, psiLoc ψ v x ≠ 1) :
    IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) (measV ψ v) := by
  obtain ⟨χ, c, hc, hχ⟩ := exists_circle_conductor ψ hψ v h1
  have h : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isSelfDual_of_hasConductor hc
    refine ⟨ν, hν.1, fun f hf => ?_⟩
    simpa only [hχ] using hν.2 f hf
  rw [measV, dite_eq_left h]
  exact h.choose_spec

theorem fourV_sb : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl (F := F), (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ],
    (∀ φ ∈ SB (κ → Fv F v), fourV ψ v φ ∈ SB (κ → Fv F v)) ∧
    (∀ φ ∈ SB (κ → Fv F v), ∀ χ ∈ SB (κ → Fv F v), fourV ψ v (φ + χ) = fourV ψ v φ + fourV ψ v χ) ∧
    ∀ (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v), schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ SB (κ → Fv F v) := by
  intro F _ _ ψ hψ v h1 κ _
  classical
  have hcont : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hψ.1 v
  obtain ⟨χ, c, hc, hχ⟩ := exists_circle_conductor ψ hψ.1 v h1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : SecondCountableTopology (Fv F v) := GlobalTheory.SplitWeil.secondCountable _
  haveI := (isSelfDualFor_measV ψ hψ.1 v h1).1
  refine ⟨fun φ hφ => ?_, fun φ hφ φ' hφ' => ?_, fun w φ hφ => GlobalTheory.SchrSBFin.schr_mem_SB v _ hcont w φ hφ⟩
  · have h := GlobalTheory.SplitWeil.FourierPi.fourier_mem_SB (Measure.pi fun _ : κ => measV ψ v) hc hφ
    simp only [hχ] at h
    exact h
  · have hint : ∀ f ∈ SB (κ → Fv F v), ∀ y : κ → Fv F v,
        Integrable (fun x => f x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y)) (Measure.pi fun _ : κ => measV ψ v) := fun f hf y =>
      Continuous.integrable_of_hasCompactSupport
        (hf.1.continuous.mul (hcont.comp (continuous_id.dotProduct continuous_const))) hf.2.mul_right
    funext y
    simp only [fourV, Pi.add_apply, add_mul]
    exact integral_add (hint φ hφ y) (hint φ' hφ' y)

end GlobalTheory.WeylFour

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

theorem sumElim_weylM_map {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R]
    [Algebra F R] (a b a' b' : κ → R) :
    Sum.elim a b ⬝ᵥ ((weylM : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R)) *ᵥ Sum.elim a' b' =
      a ⬝ᵥ b' - a' ⬝ᵥ b := by
  simp only [weylM, Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec]
  simp [Matrix.map_neg, Matrix.neg_mulVec, dotProduct_comm b a', sub_eq_add_neg]




theorem darboux_change_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ)
    (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (c₁ c₂ : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin d)),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      c₂.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ G : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F,
      GlobalTheory.SympChange.IsSymp G ∧ ∀ w, c₂.e w = GlobalTheory.SympChange.spAct G (c₁.e w) := by
  intro F E _ _ _ _ _ σ n d JX JW c₁ c₂ h₁ h₂
  classical
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  have hAinj : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective _ _

  have honto : ∀ y z : Fin n × Fin d → F, ∃ x : Matrix (Fin n) (Fin d) E,
      c₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := by
    intro y z
    let I : Matrix (Fin n) (Fin d) E →ₗ[F] Matrix (Fin n) (Fin d) (AE F E) :=
      (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix
    let L : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      (c₁.e.toLinearMap.restrictScalars F).comp I
    have hL : ∀ x, L x = c₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) := fun x => rfl
    let r : (Fin n × Fin d → F) →ₗ[F] (Fin n × Fin d → AF F) :=
      LinearMap.pi fun i => (Algebra.linearMap F (AF F)).comp (LinearMap.proj i)
    let R : ((Fin n × Fin d → F) × (Fin n × Fin d → F)) →ₗ[F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      LinearMap.prodMap r r
    have hR : ∀ y z, R (y, z) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) :=
      fun _ _ => rfl
    have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
    have hRinj : Function.Injective R := fun a b h =>
      Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
    have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
      Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
    have hLinj : Function.Injective L := c₁.e.injective.comp hIinj
    have hle : LinearMap.range L ≤ LinearMap.range R := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y', z', h⟩ := h₁ x
      exact ⟨(y', z'), by rw [hR, hL, h]⟩
    have hdim : Fintype.card (Fin n) * Fintype.card (Fin d) * Module.finrank F E =
        Fintype.card (Fin n × Fin d) + Fintype.card (Fin n × Fin d) := by
      have h1 := c₁.e.finrank_eq
      rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fintype_fun_eq_card] at h1
      exact h1
    have hfin : Module.finrank F (LinearMap.range L) = Module.finrank F (LinearMap.range R) := by
      rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
        Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hdim]
    have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
    obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
    exact ⟨x, by rw [← hL, hx, hR]⟩

  let g : ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) ≃ₗ[AF F]
      ((Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) := c₁.e.symm.trans c₂.e
  have hgrat : ∀ y z : Fin n × Fin d → F, ∃ y' z' : Fin n × Fin d → F,
      g (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) =
        (fun i => algebraMap F (AF F) (y' i), fun i => algebraMap F (AF F) (z' i)) := by
    intro y z
    obtain ⟨x, hx⟩ := honto y z
    obtain ⟨y', z', h⟩ := h₂ x
    exact ⟨y', z', by rw [← hx]; simp only [g, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, h]⟩
  let S := LinearEquiv.sumArrowLequivProdArrow (Fin n × Fin d) (Fin n × Fin d) (AF F) (AF F)
  let φ : ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) →ₗ[AF F] ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) :=
    (S.symm.toLinearMap.comp g.toLinearMap).comp S.toLinearMap
  have hφ : ∀ s, φ s = S.symm (g (S s)) := fun s => rfl
  have hent : ∀ i j, ∃ c : F, LinearMap.toMatrix' φ i j = algebraMap F (AF F) c := by
    intro i j
    rw [LinearMap.toMatrix'_apply]
    obtain ⟨y', z', h⟩ := hgrat (fun k => (Pi.single j (1 : F) : _ → F) (Sum.inl k))
      (fun k => (Pi.single j (1 : F) : _ → F) (Sum.inr k))
    have hS : S (Pi.single j 1) = (fun k => algebraMap F (AF F) ((Pi.single j (1 : F) : _ → F) (Sum.inl k)),
        fun k => algebraMap F (AF F) ((Pi.single j (1 : F) : _ → F) (Sum.inr k))) := by
      ext k <;> simp [S, Pi.single_apply, apply_ite]
    refine ⟨Sum.elim y' z' i, ?_⟩
    rw [hφ, hS, h]
    cases i <;> simp [S]
  obtain ⟨G, hG⟩ : ∃ G : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F,
      ∀ i j, LinearMap.toMatrix' φ i j = algebraMap F (AF F) (G i j) :=
    ⟨Matrix.of fun i j => (hent i j).choose, fun i j => (hent i j).choose_spec⟩
  have hGm : G.map (algebraMap F (AF F)) = LinearMap.toMatrix' φ := Matrix.ext fun i j => (hG i j).symm
  have hact : ∀ u, g u = spAct G u := by
    intro u
    have h1 : spAct G u = S (LinearMap.toMatrix' φ *ᵥ S.symm u) := by
      rw [← hGm]; rfl
    rw [h1, LinearMap.toMatrix'_mulVec, hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

  have hstd : ∀ u u' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F),
      S.symm u ⬝ᵥ (weylM.map (algebraMap F (AF F))) *ᵥ S.symm u' = u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 := by
    intro u u'
    obtain ⟨a, b⟩ := u
    obtain ⟨a', b'⟩ := u'
    have hs : ∀ p q : Fin n × Fin d → AF F, S.symm (p, q) = Sum.elim p q := fun p q => funext fun k => by
      cases k <;> simp [S]
    rw [hs, hs]
    exact sumElim_weylM_map a b a' b'
  have hkeep : ∀ u u' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F),
      (g u).1 ⬝ᵥ (g u').2 - (g u').1 ⬝ᵥ (g u).2 = u.1 ⬝ᵥ u'.2 - u'.1 ⬝ᵥ u.2 := by
    intro u u'
    have e2 := c₂.form (c₁.e.symm u) (c₁.e.symm u')
    have e1 := c₁.form (c₁.e.symm u) (c₁.e.symm u')
    simp only [LinearEquiv.apply_symm_apply] at e1
    simp only [g, LinearEquiv.trans_apply]
    rw [← e2, e1]
  refine ⟨G, ?_, fun w => ?_⟩
  · unfold IsSymp
    refine Matrix.map_injective hAinj ?_
    beta_reduce
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hGm]
    ext i j
    have key : ∀ s s' : (Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F,
        s ⬝ᵥ ((LinearMap.toMatrix' φ)ᵀ * weylM.map (algebraMap F (AF F)) * LinearMap.toMatrix' φ) *ᵥ s' =
          s ⬝ᵥ (weylM.map (algebraMap F (AF F))) *ᵥ s' := by
      intro s s'
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
        LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, hφ, hφ, hstd, hkeep,
        ← hstd, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    have := key (Pi.single i 1) (Pi.single j 1)
    simpa [single_dotProduct, Matrix.mulVec_single_one] using this
  · have := hact (c₁.e w)
    simpa [g] using this

end GlobalTheory.SympChange
end
end

section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.RatWeilOp

theorem ind_fourier_self : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ),
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    μ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 → (fun y : κ → Fv F v => ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ) = ind κ v := by
  intro F _ _ v ψ hψ κ _ _ _ μ _ hμ
  classical
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hSo : IsOpen {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := by
    have e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} =
        ⋂ i, (fun x : κ → Fv F v => x i) ⁻¹' (v.adicCompletionIntegers F : Set (Fv F v)) := by
      ext; simp
    rw [e]; exact isOpen_iInter_of_finite fun i => hO.preimage (continuous_apply i)
  have hSm := hSo.measurableSet
  have hψO : ∀ z ∈ v.adicCompletionIntegers F, ψ z = 1 := fun z hz => by
    simpa using (hψ 1).2 (v.adicCompletionIntegers F).one_mem z hz
  have hdot : ∀ x y : κ → Fv F v, (∀ i, x i ∈ v.adicCompletionIntegers F) → (∀ i, y i ∈ v.adicCompletionIntegers F) →
      x ⬝ᵥ y ∈ v.adicCompletionIntegers F := fun x y hx hy =>
    (v.adicCompletionIntegers F).sum_mem fun i _ => mul_mem (hx i) (hy i)
  funext y
  by_cases hy : ∀ i, y i ∈ v.adicCompletionIntegers F
  · have e : (fun x => ind κ v x * ψ (x ⬝ᵥ y)) =
        Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
      · have hx' : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_mem hx', Pi.one_apply, one_mul, hψO _ (hdot x y hx hy)]
      · have hx' : x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_notMem hx', zero_mul]
    have hy' : y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hy
    rw [e, integral_indicator hSm, setIntegral_const, Measure.real, hμ]
    simp [ind, Set.indicator_of_mem hy']
  · have hy' : y ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hy
    have h0 : ind κ v y = 0 := by simp only [ind, Set.indicator_of_notMem hy']
    rw [h0]
    push_neg at hy
    obtain ⟨i, hi⟩ := hy
    have : ¬ ∀ t ∈ v.adicCompletionIntegers F, ψ (y i * t) = 1 := fun h => hi ((hψ (y i)).1 h)
    push_neg at this
    obtain ⟨t, ht, hne⟩ := this
    have hs : ∀ j, (Pi.single i t : κ → Fv F v) j ∈ v.adicCompletionIntegers F := fun j => by
      by_cases hj : j = i
      · subst hj; simpa using ht
      · simp [Pi.single_apply, hj]
    have hind : ∀ x, ind κ v (Pi.single i t + x) = ind κ v x := fun x => by
      have : (∀ j, ((Pi.single i t : κ → Fv F v) + x) j ∈ v.adicCompletionIntegers F) ↔ ∀ j, x j ∈ v.adicCompletionIntegers F := by
        constructor
        · intro h j
          have := sub_mem (h j) (hs j)
          simpa using this
        · intro h j
          exact add_mem (hs j) (h j)
      by_cases hx : ∀ j, x j ∈ v.adicCompletionIntegers F
      · have h1 : Pi.single i t + x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := this.2 hx
        have h2 : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.one_apply]
      · have h1 : Pi.single i t + x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := fun h => hx (this.1 h)
        have h2 : x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} := hx
        simp only [ind, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    have key : ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ = ψ (y i * t) * ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ := by
      rw [← integral_const_mul]
      conv_lhs => rw [← integral_add_left_eq_self (μ := μ) (fun x => ind κ v x * ψ (x ⬝ᵥ y)) (Pi.single i t)]
      congr 1
      funext x
      rw [hind, add_dotProduct, single_dotProduct, AddChar.map_add_eq_mul, mul_comm t (y i)]
      ring
    have h1 : (1 - ψ (y i * t)) * ∫ x, ind κ v x * ψ (x ⬝ᵥ y) ∂μ = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 (Ne.symm hne))

end GlobalTheory.RatWeilOp
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SchASpan

theorem mem_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    Φ ∈ Submodule.span ℂ {Ψ : (κ → AF F) → ℂ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ),
      GlobalTheory.RatWeilOp.IsFam φ ∧ Ψ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ} := by
  intro F _ _ κ _ Φ hΦ
  refine (Submodule.span_le.2 ?_) hΦ
  rintro _ ⟨f, g, hg, rfl⟩
  let L : ((κ → Af F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun g => pureA F f g
      map_add' := fun a b => by funext x; simp only [pureA, Pi.add_apply, mul_add]
      map_smul' := fun c a => by
        funext x; simp only [pureA, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have h : L g ∈ Submodule.map L (Submodule.span ℂ _) :=
    Submodule.mem_map_of_mem (GlobalTheory.SBSpan.mem_span_restrictedProd F κ g hg)
  rw [Submodule.map_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨p, ⟨φ, hφ1, hφ2, rfl⟩, rfl⟩
  exact ⟨f, φ, ⟨hφ1, hφ2⟩, rfl⟩

end GlobalTheory.SchASpan

end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_domains_of_dim_lt : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → (∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → HInv q D) → ∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R ≤ d → HInv q R := by
  first | (exact @GlobalTheory.hInv_of_domains_of_dim_lt) | (exact GlobalTheory.hInv_of_domains_of_dim_lt) | (intros; apply GlobalTheory.hInv_of_domains_of_dim_lt  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.hInv_quot_iInf_ker_retractions : ∀ (q : ℕ) [NeZero q] (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], IsUnit (q : D) → HInv q T → (∀ (E' : Type) [CommRing E'] [Algebra D E'] [Algebra.IsIntegral D E'] (s : D), s ≠ 0 → algebraMap D E' s = 0 → HInv q E') → ∀ (ι : T →ₐ[D] E) (X : Finset (E →ₐ[D] T)), (∀ χ ∈ X, χ.comp ι = AlgHom.id D T) → HInv q (E ⧸ ⨅ χ ∈ X, RingHom.ker χ) := by
  first | (exact @GlobalTheory.homotopyInv_quot_iInf_ker_retractions) | (exact GlobalTheory.homotopyInv_quot_iInf_ker_retractions) | (intros; apply GlobalTheory.homotopyInv_quot_iInf_ker_retractions  <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_finPart_eq_one_mul_inv_mem_split_congruence_ideles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ), 0 < N → ∀ x : (AF F ⊗[F] E)ˣ, ∃ z : (AF F ⊗[F] E)ˣ, finPartF F E (z : AF F ⊗[F] E) = 1 ∧ x * z⁻¹ ∈ GlobalTheory.HeckeSplitGen.grpHF σ N := by
  first | exact @GlobalTheory.HeckeSplitGen.FinF.exists_finPart_eq_one_mul_inv_mem | exact GlobalTheory.HeckeSplitGen.FinF.exists_finPart_eq_one_mul_inv_mem | (intros; apply GlobalTheory.HeckeSplitGen.FinF.exists_finPart_eq_one_mul_inv_mem <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_closure_split_congruence_ideles_of_finPart_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ), 0 < N → ∀ z : (AF F ⊗[F] E)ˣ, finPartF F E (z : AF F ⊗[F] E) = 1 → z ∈ closure (GlobalTheory.HeckeSplitGen.grpHF σ N : Set (AF F ⊗[F] E)ˣ) := by
  first | exact @GlobalTheory.HeckeSplitGen.mem_closure_grpHF_of_finPart_eq_one | exact GlobalTheory.HeckeSplitGen.mem_closure_grpHF_of_finPart_eq_one | (intros; apply GlobalTheory.HeckeSplitGen.mem_closure_grpHF_of_finPart_eq_one <;> assumption)
end
