module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerEqMapNormOneTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1454
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.twistedCentralizer_eq_map_normOneTorus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (β : B.Aˣ) (ε : B.A), (ε = 1 ∨ ε = -1) → B.σ (β : B.A) = β * (ε * B.g) → ∀ (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → twCent (thL a w) δ = B.T.map (GlobalTheory.TwOrbLat.mulGL e b) := by
  first | exact @GlobalTheory.TwOrbCent.twCent_eq_map | exact GlobalTheory.TwOrbCent.twCent_eq_map | (intros; apply GlobalTheory.TwOrbCent.twCent_eq_map <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes ValuativeRel
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairCone
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.standardPair_members_mem_schwartzBruhat : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ)
    (c a a' : ℕ), GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SplitFlip.CondLE ϖ c ν →
      stdA ν ϖ c a a' ∈ SB (Matrix (Fin a) (Fin (a + a')) k) ∧ stdB ν ϖ c a a' ∈ SB (Matrix (Fin a') (Fin (a + a')) k) := by
  first | exact @GlobalTheory.StdPairSB.stdPair_mem_SB | exact GlobalTheory.StdPairSB.stdPair_mem_SB | (intros; apply GlobalTheory.StdPairSB.stdPair_mem_SB <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.commutingOperatorsPolynomialEval_pderiv : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [DecidableEq ι] (m d : ι → Module.End ℂ V)
    (hm : ∀ i j, m i * m j = m j * m i) (f₀ : V), (∀ i j, d i * m j - m j * d i = if i = j then 1 else 0) →
    (∀ i, d i f₀ = 0) → ∀ (i : ι) (p : MvPolynomial ι ℂ),
      GlobalTheory.CCRFock.polEval m hm f₀ (MvPolynomial.pderiv i p) = d i (GlobalTheory.CCRFock.polEval m hm f₀ p) := by
  first | exact @GlobalTheory.CCRFock.polEval_pderiv | exact GlobalTheory.CCRFock.polEval_pderiv | (intros; apply GlobalTheory.CCRFock.polEval_pderiv <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.tensorPolynomialsToProductVariables_injective : ∀ (W Λ : Type) [Fintype W] [DecidableEq W], Function.Injective (GlobalTheory.CCRFock.polMap W Λ) := by
  first | exact @GlobalTheory.CCRFock.polMap_injective | exact GlobalTheory.CCRFock.polMap_injective | (intros; apply GlobalTheory.CCRFock.polMap_injective <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.heisenberg_annihilation_creation_commutator_eq_delta : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    (∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) →
    ∀ j k : W × (Ix P Q × Ix R S), GlobalTheory.CCRFock.fockD H j * GlobalTheory.CCRFock.fockM H k - GlobalTheory.CCRFock.fockM H k * GlobalTheory.CCRFock.fockD H j =
      if j = k then 1 else 0 := by
  first | exact @GlobalTheory.CCRFock.CommDM.fockD_fockM_comm | exact GlobalTheory.CCRFock.CommDM.fockD_fockM_comm | (intros; apply GlobalTheory.CCRFock.CommDM.fockD_fockM_comm <;> assumption)
end

section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

theorem _root_.GlobalTheory.T.heisenberg_family_expand_creation_annihilation : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    ∀ c : W → Matrix (Ix P Q) (Ix R S) ℂ, H c = ∑ j : W × (Ix P Q × Ix R S),
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • GlobalTheory.CCRFock.fockM H j +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • GlobalTheory.CCRFock.fockD H j) := by
  first | exact @GlobalTheory.CCRFock.heis_expand | exact GlobalTheory.CCRFock.heis_expand | (intros; apply GlobalTheory.CCRFock.heis_expand <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

theorem _root_.GlobalTheory.T.scaled_coset_indicator_schwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  exact @GlobalTheory.EvAdm.indicator_coset_scaledInt_mem_SB
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

theorem _root_.GlobalTheory.T.theta_sum_indicator_nonzero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∃ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator
        (fun _ => (1 : ℂ)))) ≠ 0 := by
  first | exact @GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero | exact GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero | (intros; apply GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero <;> assumption)
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.EvAdm

theorem _root_.GlobalTheory.T.indicator_coset_scaledIntegral_eq_restrictedProduct : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    ∃ φ : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      ∀ y : κ → FiniteAdeleRing (𝓞 F) F, Set.indicator {y | y - r ∈ scaledInt F κ a} (fun _ => (1 : ℂ)) y =
        ∏ᶠ v, φ v fun i => evalV F v (y i) := by
  first | exact @GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod | exact GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod | (intros; apply GlobalTheory.EvAdm.indicator_coset_scaledInt_eq_finprod <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.FockKFin

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.EvAt0.PolD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dStep {κ : Type} [Fintype κ] (P : Submodule ℂ (SInf F κ)) : Submodule ℂ (SInf F κ) :=
  Submodule.span ℂ {h | ∃ a b : κ → mixedEmbedding.mixedSpace F, ∃ f ∈ P, h = dOp a b f}

theorem dOp_mem_dStep {κ : Type} [Fintype κ] (P : Submodule ℂ (SInf F κ)) (a b : κ → mixedEmbedding.mixedSpace F)
    {f : SInf F κ} (hf : f ∈ P) : dOp a b f ∈ dStep P :=
  Submodule.subset_span ⟨a, b, f, hf, rfl⟩

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def vacSp (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Submodule.span ℂ {g | GaussD M τ g}

def polLe (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (m : ℕ) :
    Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Nat.rec (motive := fun _ => Submodule ℂ (SInf F (Fin n × Fin d))) (vacSp M τ) (fun _ P => P ⊔ dStep P) m

theorem polLe_zero (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : polLe M τ 0 = vacSp M τ := rfl

theorem polLe_succ (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (m : ℕ) :
    polLe M τ (m + 1) = polLe M τ m ⊔ dStep (polLe M τ m) := rfl

theorem polLe_mono (M : Model σ X W) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) : Monotone (polLe M τ) :=
  monotone_nat_of_le_succ fun m => by rw [polLe_succ]; exact le_sup_left

def pureL {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) : SInf F κ →ₗ[ℂ] (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ where
  toFun f := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ
  map_add' f g := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
  map_smul' c f := by funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

end GlobalTheory.FockKFin

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
open Formalism.IndefR.Arith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GalLift.Assembly

section Abstract

variable {L : Type} [Field L] {G : Type} [Group G] [Fintype G] {C Y H : Type} [AddCommGroup Y] [Module L Y]
  [AddCommGroup H] [Module ℂ H]

theorem read_sum (σ : L →+* ℂ) (J : Y →ₛₗ[σ] H) (ι : C → Y) (act : G → C → C) (chi : G →* Lˣ) (ρ : Representation ℂ G H)
    (h : ∀ g f, J (ι (act g f)) = σ (chi g : L) • ρ g (J (ι f))) (e : G → L) {n : ℕ} (b : Fin n → L) (f : Fin n → C) :
    J (∑ g, (e g * (((chi g)⁻¹ : Lˣ) : L)) • ∑ k, b k • ι (act g (f k))) =
      ∑ g, σ (e g) • ρ g (∑ k, σ (b k) • J (ι (f k))) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_

  rw [map_smulₛₗ, map_sum, map_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ, h, map_smul, smul_smul, smul_smul, smul_smul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  have := (chi g).inv_mul
  linear_combination (e g * b k) * this

theorem shift_sum (ρ : Representation ℂ G H) (e : G → ℂ) {z₀ z : G} (h₀ : z₀ ∈ Subgroup.center G) (hz : z ∈ Subgroup.center G)
    (α β κ : ℂ) (hβ : β ≠ 0) (S T : H) (hT : κ • T = ∑ g, e g • ρ g (β • ρ z S)) :
    ∑ g, e g • ρ g (α • ρ z₀ S) = (α * β⁻¹ * κ) • ρ (z₀ * z⁻¹) T := by

  rw [mul_smul, ← map_smul (ρ (z₀ * z⁻¹)) κ, hT, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : ρ (z₀ * z⁻¹) (ρ g (ρ z S)) = ρ g (ρ z₀ S) := by
    have e1 : z₀ * z⁻¹ * (g * z) = g * z₀ := by
      rw [Subgroup.mem_center_iff.1 hz g, Subgroup.mem_center_iff.1 h₀ g]; group
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_assoc, e1, map_mul, Module.End.mul_apply]
  simp only [map_smul, h1, smul_smul]
  congr 1
  field_simp

theorem norm_of_pow {a : ℂ} {m : ℕ} (hm : 0 < m) (h : a ^ m = 1) : ‖a‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg a) hm.ne').1 (by rw [← norm_pow, h, norm_one])

theorem norm_chi (σ : L →+* ℂ) (chi : G →* Lˣ) (g : G) : ‖σ (chi g : L)‖ = 1 :=
  norm_of_pow (m := Fintype.card G) Fintype.card_pos (by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one, map_one])

variable {P : Type} [AddCommGroup P] [Module ℂ P]

theorem conj_abstract (σ : L →+* ℂ) (J : Y →ₛₗ[σ] H) (ι : C → Y) (act : G → C → C) (chi : G →* Lˣ) (ρ : Representation ℂ G H)
    (h : ∀ g f, J (ι (act g f)) = σ (chi g : L) • ρ g (J (ι f))) (e : G → L) (ev : H →ₗ[ℂ] P) (hev : Function.Injective ev)
    (W : P →ₗ[ℂ] P) (hW : ∀ y, W (ev y) = ev (∑ g, σ (e g) • ρ g y)) {z₀ z : G} (h₀ : z₀ ∈ Subgroup.center G)
    (hz : z ∈ Subgroup.center G) (ze : L) (κ : ℂ) {n : ℕ} (a : Fin n → L) (f : Fin n → C) (θ : P)
    (hθ : κ • θ = ∑ k, σ (a k) • ev (J (ι (act z (f k))))) (T : H) (hT : ev T = W θ) :
    J (∑ g, (e g * (((chi g)⁻¹ : Lˣ) : L)) • ∑ k, (ze * a k) • ι (act g (act z₀ (f k)))) =
      (σ ze * σ (chi z₀ : L) * (σ (chi z : L))⁻¹ * κ) • ρ (z₀ * z⁻¹) T := by
  have e1 : ∑ k, σ (a k) • ev (J (ι (act z (f k)))) = ev (σ (chi z : L) • ρ z (∑ k, σ (a k) • J (ι (f k)))) := by

    rw [map_sum, Finset.smul_sum, map_sum]
    exact Finset.sum_congr rfl fun k _ => by simp only [h, map_smul]; rw [smul_comm]
  have h3 : ∑ k, σ (ze * a k) • J (ι (act z₀ (f k))) = (σ ze * σ (chi z₀ : L)) • ρ z₀ (∑ k, σ (a k) • J (ι (f k))) := by

    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [h, map_smul, smul_smul, smul_smul, map_mul]
    congr 1
    ring
  rw [read_sum σ J ι act chi ρ h e (fun k => ze * a k) (fun k => act z₀ (f k)), h3]
  refine shift_sum ρ _ h₀ hz _ _ κ (norm_ne_zero_iff.1 (by rw [norm_chi]; exact one_ne_zero)) _ _ (hev ?_)
  rw [map_smul, hT, ← map_smul, hθ, e1, hW]

theorem exists_ev (ev : H →ₗ[ℂ] P) {κ : ℂ} (hκ : ‖κ‖ = 1) {n : ℕ} (a : Fin n → ℂ) (t : Fin n → H) (θ : P)
    (hθ : κ • θ = ∑ k, a k • ev (t k)) : ∃ s, ev s = θ := by
  have hκ0 : κ ≠ 0 := norm_ne_zero_iff.1 (by rw [hκ]; exact one_ne_zero)
  refine ⟨κ⁻¹ • ∑ k, a k • t k, ?_⟩

  rw [map_smul, map_sum, ← inv_smul_smul₀ hκ0 θ, hθ]
  simp only [map_smul]

def evL {I : Type} {M : I → Type} [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] (e : H →ₗ[ℂ] MultilinearMap (RingHom.id ℂ) M P)
    (v : ∀ τ, M τ) : H →ₗ[ℂ] P where
  toFun y := e y v
  map_add' x y := by rw [map_add (f := _)]; rfl
  map_smul' a x := by rw [map_smul]; rfl

end Abstract

section Main

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

def crdF (fw : FWTie T R κw v₀) (i : Fin D.R.m) (f : Cu T κw i) : Fin (R.nW i) → D.what₂.LL := (fw.e i f : (R.FW i).WK)

def ratOf (fw : FWTie T R κw v₀) (i : Fin D.R.m) (act : G → Cu T κw i → Cu T κw i) (z : G) (ze : D.what₂.LL) {n : ℕ}
    (a : Fin n → D.what₂.LL) (f : Fin n → Cu T κw i) : Fin (R.nW i) → D.what₂.LL :=
  ∑ g, ((idemOf A.X).coeff g * ((((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL)) •
    ∑ k, (ze * a k) • crdF fw i (act g (act z (f k)))

theorem sign_at_base_place_eq_embedding (R : RealDat D A T.Q.c.F) : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0

theorem exists_reps {i : Fin D.R.m} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} (hP : OMPins T R κw v₀ O i) :
    ∃ h, RepsAt (O i) (v₀ i (sg0 D A)) h := (hP.2.tuple ()).reps

end Main

section Final

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem smul_inv_of {H : Type} [AddCommGroup H] [Module ℂ H] (L : H →ₗ[ℂ] H) {κ κ' : ℂ} (h : ‖κ'‖ = 1) {a b : H}
    (e : b = κ' • a) : κ • L a = (κ * κ'⁻¹) • L b := by
  have h0 : κ' ≠ 0 := norm_ne_zero_iff.1 (by rw [h]; exact one_ne_zero)
  rw [e, map_smul, smul_smul, mul_assoc, inv_mul_cancel₀ h0, mul_one]

end Final

end GlobalTheory.GalLift.Assembly

end
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0
open GlobalTheory.ThK.EvAt0.PolD

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvAt0.PolEv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Gen

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem at_symm (M : Model σ X W) (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    At (evI F) (M.co.e.symm (fun i => liftA (a i), fun i => liftA (b i))) := by
  intro c hc
  rw [← map_smul]
  have : c • ((fun i => liftA (a i), fun i => liftA (b i)) : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) = 0 := by
    ext i <;> simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply] <;>
      exact smul_liftA hc _
  rw [this, map_zero]

theorem arc_liftA {κ : Type} (a : κ → mixedEmbedding.mixedSpace F) : arc (fun i => liftA (a i)) = a := by
  funext i; exact evI_liftA (a i)

theorem actsD_iff_dOp {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ ψ _ _ M.co hψ
  have e : D u f = dOp (arc (M.co.e u).1) (arc (M.co.e u).2) f := by
    ext x
    rw [(hD u hu f).2 x, dOp_apply]
    rfl
  have h1 : ActsD (evI F) (M.heisLine ψ u) f (D u f) :=
    (GlobalTheory.T.archActionReadings_compatible F _ f (D u f) (D u f)).1 _ (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr])
      (hD u hu f).1
  rw [← e]
  exact ⟨fun h2 => (GlobalTheory.T.archActionReadings_compatible F _ f f₁ (D u f)).2.2.1 _ h2 h1, fun h2 => h2 ▸ h1⟩

theorem isGauss_iff {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (g : SInf F (Fin n × Fin d)) : M.IsGauss ψ τ g ↔ GaussD M τ g := by
  refine exists_congr fun ε => forall₂_congr fun u u' => forall₃_congr fun hu hu' _ => ⟨fun H => ?_, fun H f f' hf hf' => ?_⟩
  · exact H _ _ ((actsD_iff_dOp hψ M u hu _ _).2 rfl) ((actsD_iff_dOp hψ M u' hu' _ _).2 rfl)
  · rw [(actsD_iff_dOp hψ M u hu _ _).1 hf, (actsD_iff_dOp hψ M u' hu' _ _).1 hf']
    exact H

theorem pol_eq {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    M.Pol ψ τ = sInf {N | (∀ f₀, GaussD M τ f₀ → f₀ ∈ N) ∧
      ∀ (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F), ∀ f ∈ N, dOp a b f ∈ N} := by
  unfold Model.Pol
  congr 1
  ext N
  simp only [Set.mem_setOf_eq]
  refine and_congr (forall_congr' fun f₀ => imp_congr_left (isGauss_iff hψ M τ f₀)) ⟨fun H a b f hf => ?_, fun H u hu f hf f₁ h1 => ?_⟩
  · have hu := at_symm M a b
    refine H _ hu f hf _ ((actsD_iff_dOp hψ M _ hu _ _).2 ?_)
    rw [LinearEquiv.apply_symm_apply, arc_liftA, arc_liftA]
  · rw [(actsD_iff_dOp hψ M u hu _ _).1 h1]
    exact H _ _ f hf

theorem dOp_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (a b : Fin n × Fin d → mixedEmbedding.mixedSpace F) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ) :
    dOp a b f ∈ M.Pol ψ τ := by
  rw [pol_eq hψ] at hf ⊢
  exact Submodule.mem_sInf.2 fun N hN => hN.2 a b f (Submodule.mem_sInf.1 hf N hN)

theorem gauss_mem {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {f : SInf F (Fin n × Fin d)} (hf : GaussD M τ f) : f ∈ M.Pol ψ τ := by
  rw [pol_eq hψ]
  exact Submodule.mem_sInf.2 fun N hN => hN.1 f hf

end Gen

end GlobalTheory.ThK.EvAt0.PolEv
end
end
