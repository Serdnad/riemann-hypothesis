module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle651
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle063
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001

@[expose] public section

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.StdCharWeilDatum
section Char
variable {F : Type} [Field F] [NumberField F]
end Char
section Trace
variable {F : Type} [Field F] [NumberField F]
end Trace
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem isStdCharF_of_isGood_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) := by
  intro F E _ _ _ _ _ σ B hB
  haveI : IsTotallyReal F := hB.cm.1
  refine ⟨isCharAF hB.std, ⟨?_, fun θ hθ x => ?_⟩⟩
  · choose θ hθ using fun w : InfinitePlace F =>
      GlobalTheory.DualPairCompare.gen_inf_exists (B.emb w).1 w (B.emb w).2.symm
    exact ⟨θ, hθ⟩
  · show B.ψ (pairA F x 0) = _
    rw [psi_pairA hB.std, sum_infFam B θ hθ x]
    congr 1
    push_cast
    ring
end GlobalTheory.StdCharWeilDatum
end
end
end

section



section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP
theorem UpperTheory.exists_finite_unramified_outside_of_isHecke :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}, _root_.UpperTheory.TP.W.GoodK σ B → ∀ {χ : Chr F E}, IsHecke F E χ → ∃ S : Finset (Pl F), UnrOff χ (S : Set (Pl F)) := by
  intro F E _ _ _ _ _ σ B hB χ hχ
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ UnrAt χ w}.Finite :=
    Filter.eventually_cofinite.1 (GlobalTheory.PairVac.eventually_unrAt_of_isHecke σ hB.cm χ hχ)
  refine ⟨(hfin.image fun w => w.under (𝓞 F)).toFinset, fun w hw => ?_⟩
  by_contra hu
  exact hw (by
    show w.under (𝓞 F) ∈ (((hfin.image fun w => w.under (𝓞 F)).toFinset : Finset (Pl F)) : Set (Pl F))
    rw [Set.Finite.coe_toFinset]
    exact ⟨w, hu, rfl⟩)
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ComplexConjugate
noncomputable section
namespace GlobalTheory.DblThetaProd
theorem thetaTr_coDbl_boxFun_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JT JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (hA : JA = JTᵀ) (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ,
        GlobalTheory.WeilSchrodinger.thetaTr F (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) B.ψ (boxFun φ₁ φ₂) =
          GlobalTheory.DblTargetDelta.deltaT (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro F E _ _ _ _ _ σ B hB hstd nS nT JT JA JB ξ hA κ _ co φ₁ _ φ₂ _
  have hψ : ∀ x, ‖B.ψ x‖ = 1 := hstd.1.2.1
  have hc : ∀ x, starRingEnd ℂ (B.ψ x) = B.ψ (-x) := fun x => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ x)]
  funext w
  rw [GlobalTheory.DblTargetDelta.deltaT_apply]
  have he : (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co).e w =
      (Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).1 (co.e (GlobalTheory.DblTargetDelta.botR w)).1,
        Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).2 (-(co.e (GlobalTheory.DblTargetDelta.botR w)).2)) := rfl
  have hn : co.e (-GlobalTheory.DblTargetDelta.botR w) = -(co.e (GlobalTheory.DblTargetDelta.botR w)) := map_neg _ _
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, he, hn]
  generalize co.e (GlobalTheory.DblTargetDelta.topR w) = p₁
  generalize co.e (GlobalTheory.DblTargetDelta.botR w) = p₂
  obtain ⟨x₁, y₁⟩ := p₁
  obtain ⟨x₂, y₂⟩ := p₂
  simp only
  set A : (κ → F) → (κ → AdeleRing (𝓞 F) F) := fun b i => algebraMap F (AdeleRing (𝓞 F) F) (b i) with hAdef
  have key : ∀ q : (κ → F) × (κ → F),
      schr B.ψ (Sum.elim x₁ x₂, Sum.elim y₁ (-y₂)) (boxFun φ₁ φ₂)
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm q i)) =
        schr B.ψ (x₁, y₁) φ₁ (A q.1) *
          (B.ψ (-(A q.2 ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A q.2 + x₂)) := by
    rintro ⟨a, b⟩
    have h1 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inl = A a + x₁ := by
      funext i; simp [hAdef]
    have h2 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inr = A b + x₂ := by
      funext i; simp [hAdef]
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.boxFun]
    rw [h1, h2, mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr, hAdef]
    ring
  rw [← (Equiv.sumArrowEquivProdArrow κ κ F).symm.tsum_eq]
  refine (tsum_congr key).trans ?_
  refine (tsum_prod_mul (fun a => schr B.ψ (x₁, y₁) φ₁ (A a))
    (fun b => B.ψ (-(A b ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A b + x₂))).trans ?_
  congr 1
  rw [Complex.conj_tsum]
  conv_rhs => rw [← (Equiv.neg (κ → F)).tsum_eq]
  refine tsum_congr fun b => ?_
  have h3 : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.neg (κ → F)) b i)) = -A b := by
    funext i; simp [hAdef]
  simp only [GlobalTheory.WeilM.schr, h3, map_mul, Complex.conj_conj, hc,
    Prod.fst_neg, Prod.snd_neg]
  simp only [neg_dotProduct, dotProduct_neg, neg_neg, neg_add, sub_eq_add_neg, mul_neg]
end GlobalTheory.DblThetaProd
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.LagrThetaInv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.LagrThetaInv
namespace GlobalTheory.LagrThetaInv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.LagrThetaInv
open scoped Pointwise in
open GlobalTheory.LagrThetaInv in
theorem GlobalTheory.LagrThetaInv.lagrInt_rho_inv_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (κ : Type) [Fintype κ]
      (co : Darboux (symp (cA σ) ξ (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) (incM F JB)) κ),
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : κ → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (u : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)), ∀ φ ∈ schA F κ,
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * u) φ)) = GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ) := by
  intro F E _ _ _ _ _ σ B hB nS nT JT JB ξ κ _ co hco ν 𝓕 _ h𝓕 u φ hφ
  change GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
      (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)) =
    GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ)
  set g : WOF F E nS nT → ℂ := fun v => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * v) with hg
  have h1 : ∀ v : WOF F E nS nT, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (co.rho B.ψ (dC (AF F ⊗[F] E) nT * u) φ)
      (dC (AF F ⊗[F] E) nT * v) = g (v + u) := by
    intro v
    simp only [hg, GlobalTheory.WeilSchrodinger.thetaTr, Darboux.rho]
    rw [schr_dC]
  have h2 : ∀ (r : ratLF F E nS nT) (v : WOF F E nS nT), g (r +ᵥ v) = g v := by
    rintro ⟨r, γ, rfl⟩ v
    obtain ⟨y, z, hyz⟩ := hco (dC E nT * γ)
    have hr : ((incAF F E).toAddMonoidHom.mapMatrix γ : WOF F E nS nT) = γ.map (incAF F E) := rfl
    show GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ (dC (AF F ⊗[F] E) nT * (_ + v)) = _
    simp only [hg, GlobalTheory.WeilSchrodinger.thetaTr, Darboux.rho]
    rw [← schr_dC, hr, dC_mul_rat, hyz, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hB.std.2.1 y z]
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  haveI : ContinuousAdd (WOF F E nS nT) := inferInstanceAs (ContinuousAdd (Fin nT → Fin nS → AF F ⊗[F] E))
  haveI : MeasurableAdd (WOF F E nS nT) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  haveI : MeasurableConstVAdd (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun r => (continuous_const_add (r : WOF F E nS nT)).measurable⟩
  haveI : VAddInvariantMeasure (ratLF F E nS nT) (WOF F E nS nT) ν :=
    ⟨fun r s _ => measure_preimage_add ν (r : WOF F E nS nT) s⟩
  haveI : VAddCommClass (WOF F E nS nT) (ratLF F E nS nT) (WOF F E nS nT) :=
    ⟨fun a r x => add_left_comm a (r : WOF F E nS nT) x⟩
  haveI : Countable (ratLF F E nS nT) := by
    haveI : Countable E := by
      haveI : FiniteDimensional ℚ E := inferInstance
      exact ((Module.finBasis ℚ E).equivFun).injective.countable
    have : Countable (Matrix (Fin nT) (Fin nS) E) := inferInstanceAs (Countable (Fin nT → Fin nS → E))
    exact (Set.countable_range ((incAF F E).toAddMonoidHom.mapMatrix (m := Fin nT) (n := Fin nS))).to_subtype
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [h1]
  rw [← (measurePreserving_add_right ν u).setIntegral_image_emb (measurableEmbedding_addRight u) g 𝓕]
  have hF' : IsAddFundamentalDomain (ratLF F E nS nT) ((· + u) '' 𝓕) ν := by
    have hs : (· + u) '' 𝓕 = ((u : WOF F E nS nT) +ᵥ 𝓕 : Set (WOF F E nS nT)) := by
      rw [← Set.image_vadd]
      congr 1
      funext v
      exact add_comm v u
    rw [hs]
    exact h𝓕.vadd_of_comm (G' := WOF F E nS nT) (u : WOF F E nS nT)
  exact hF'.setIntegral_eq h𝓕 h2
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem heis_C_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (N : ℕ)
    (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N)
    (hCe : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u))
    (he : ∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w'))
    (Φ : (Fin N → AF F) → ℂ) (y : WOF F E nS nT) :
    heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC (AF F ⊗[F] E) nT * y) (thV B.ψ Φ ∘ e) =
      thV B.ψ (fun x => B.ψ (x ⬝ᵥ β y) * Φ x) ∘ e := by
  have hCy : e (dC (AF F ⊗[F] E) nT * y) = (0, β y) := by
    have h := hCe y 0
    rw [Matrix.mul_zero, add_zero, map_zero] at h
    exact h
  have h2 : (⅟(2 : AF F)) = algebraMap F (AF F) (1 / 2) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  funext w
  simp only [Function.comp_apply, heisOF, thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr]
  rw [map_add (f := _), hCy]
  have hph : symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w (dC (AF F ⊗[F] E) nT * y) =
      ⅟(2 : AF F) * ((e w).1 ⬝ᵥ β y) := by
    rw [symplOHF, he, hCy, h2]
    simp [symV]
  rw [hph, ← tsum_mul_left]
  refine tsum_congr fun ξ => ?_
  set x₁ := (e w).1
  set y₁ := (e w).2
  set b := β y
  set r : Fin N → AF F := fun i => algebraMap F (AF F) (ξ i)
  have hw : e w = (x₁, y₁) := rfl
  simp only [hw, Prod.mk_add_mk, add_zero]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  have h22 : (⅟(2 : AF F)) + ⅟2 = 1 := invOf_two_add_invOf_two
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (x₁ ⬝ᵥ b) * h22
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
namespace GlobalTheory.ThetaTrContF
theorem continuous_thetaTrF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, Continuous (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ _ _ κ _ co _ Φ hΦ
  haveI : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin nT → Fin nS → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
  have hc : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  exact (GlobalTheory.ThetaTrCont.schA_cont F B.ψ hψ.1.1 hψ.1.2.1 hΦ).2.comp hc
end GlobalTheory.ThetaTrContF
end
end

section



section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.HeisThetaF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
section Alg
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
end Alg
section Parts
end Parts
section Top
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
end Top
section Fin
end Fin
theorem isThetaFunOF_heisOF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
      (w₀ : WOF F E nS nT) (f : WOF F E nS nT → ℂ), IsThetaFunOF σ JS JT ξ₀ B.ψ f →
        IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT ξ₀ w₀ f hf
  have hψ : Continuous B.ψ := hB.std.1
  haveI := isTopologicalRing_AEF (F := F) (E := E)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro γ w
    simp only [heisOF]
    rw [add_assoc, hf.quasi, symplOHF_add_left, symplOHF_add_right, ← mul_assoc, ← mul_assoc,
      ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    abel
  · obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨K, hK⟩ := exists_openAddSubgroup_psi_fin B.ψ hψ
    let φ : WOF F E nS nT →+ AF F :=
      { toFun := fun u => symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u
        map_zero' := by simp only [symplOHF_zero_left, symplOHF_zero_right, sub_zero]
        map_add' := fun u v => by simp only [symplOHF_add_left, symplOHF_add_right]; abel }
    have hφ : Continuous φ := (continuous_symplOHF_left w₀).sub (continuous_symplOHF_right w₀)
    let ρ : WOF F E nS nT →+ Af F := (sndA F).toRingHom.toAddMonoidHom.comp φ
    have hρ : Continuous ρ := continuous_snd.comp hφ
    refine ⟨U ⊓ K.toAddSubgroup.comap ρ, hU.inter (K.isOpen.preimage hρ), fun u hu h0 => ?_⟩
    have h1 : pairA F 1 0 • u = 0 := smul_eq_zero_of_map_infPartF h0
    have hfst : fstA F (φ u) = 0 := by
      rw [← fstA_mul_idem]
      show fstA F (pairA F 1 0 * (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u)) = 0
      rw [mul_sub, ← symplOHF_smul_left, ← symplOHF_smul_right, h1, symplOHF_zero_left, symplOHF_zero_right,
        sub_zero, map_zero]
    have hφu : φ u = pairA F 0 (ρ u) := Prod.ext hfst rfl
    have hone : B.ψ (φ u) = 1 := by rw [hφu]; exact hK _ hu.2
    have hswap : B.ψ (symplOHF σ JS JT ξ₀ u w₀) = B.ψ (symplOHF σ JS JT ξ₀ w₀ u) := by
      have : symplOHF σ JS JT ξ₀ u w₀ = φ u + symplOHF σ JS JT ξ₀ w₀ u := by
        show _ = (symplOHF σ JS JT ξ₀ u w₀ - symplOHF σ JS JT ξ₀ w₀ u) + _
        abel
      rw [this, AddChar.map_add_eq_mul, hone, one_mul]
    funext w
    have hw := congrFun (hUf u hu.1 h0) (w + w₀)
    simp only [heisOF] at hw ⊢
    rw [← hw, add_right_comm w u w₀, symplOHF_add_left w u w₀, symplOHF_add_left w w₀ u, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul, hswap]
    ring
  · show Continuous fun w => B.ψ (symplOHF σ JS JT ξ₀ w w₀) * f (w + w₀)
    exact (hψ.comp (continuous_symplOHF_left w₀)).mul (hf.cont.comp (continuous_id.add continuous_const))
  · intro k L hL h0 w
    let φ₁ : WOF F E nS nT →+ AF F :=
      { toFun := fun u => symplOHF σ JS JT ξ₀ u w₀
        map_zero' := symplOHF_zero_left w₀
        map_add' := fun u v => symplOHF_add_left u v w₀ }
    let ev : AF F →+ ℝ :=
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).toAddMonoidHom.comp
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv.toAddMonoidHom.comp (fstA F).toRingHom.toAddMonoidHom)
    have hev : Continuous ev :=
      (LinearMap.continuous_of_finiteDimensional (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))).comp
        ((continuous_ringEquiv_mixedSpace F).comp continuous_fst)
    let g : (Fin k → ℝ) →+ ℝ := ev.comp (φ₁.comp L)
    have hg : Continuous g := hev.comp ((continuous_symplOHF_left w₀).comp hL)
    let gL := g.toRealLinearMap hg
    have hval : ∀ t, B.ψ (symplOHF σ JS JT ξ₀ (L t) w₀) =
        Complex.exp (-(2 * Real.pi * Complex.I) * ((gL t : ℝ) : ℂ)) := by
      intro t
      have hfin : sndA F (symplOHF σ JS JT ξ₀ (L t) w₀) = 0 := by
        have h1 : pairA F 0 1 • L t = 0 := smul_eq_zero_of_map_finPartF (h0 t)
        rw [← sndA_mul_idem, ← symplOHF_smul_left, h1, symplOHF_zero_left, map_zero]
      rw [hB.std.2.2 _ ?_]
      · rfl
      · intro v hv
        have hv1 : v.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hv
        refine Prod.ext ?_ ?_
        · show v.1 * (symplOHF σ JS JT ξ₀ (L t) w₀).1 = 0
          rw [hv1, zero_mul]
        · show v.2 * (symplOHF σ JS JT ξ₀ (L t) w₀).2 = 0
          rw [show (symplOHF σ JS JT ξ₀ (L t) w₀).2 = 0 from hfin, mul_zero]
    have hfun : (fun t => heisOF σ JS JT ξ₀ B.ψ w₀ f (w + L t)) = fun t =>
        B.ψ (symplOHF σ JS JT ξ₀ w w₀) * Complex.exp (-(2 * Real.pi * Complex.I) * ((gL t : ℝ) : ℂ)) *
          f (w + w₀ + L t) := by
      funext t
      simp only [heisOF]
      rw [symplOHF_add_left, AddChar.map_add_eq_mul, hval, add_right_comm]
    rw [hfun]
    refine (contDiff_const.mul ?_).mul (hf.smooth k L hL h0 (w + w₀))
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp gL.contDiff)).cexp
end GlobalTheory.HeisThetaF
end
end
end

section



section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace Tw
open _root_.GlobalTheory
theorem exists_int_add_conj_eq_one_of_base_good_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ B hB
  haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hB.unram
  exact exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hB.cm inferInstance
end Tw
end
end
