module

import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle269
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle140
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle342
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotIntFJUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle073
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle134
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle135
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle035
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle038

@[expose] public section

section

namespace GlobalTheory.IntSmulMemLatticeTwistedOperators

open NumberField

theorem exists_int_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  obtain ⟨y, hy, hint⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a))
  refine ⟨y, hy, ?_⟩
  simpa [zsmul_eq_mul] using hint

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (v : Fin n → E) : ∃ c : ℤ, c ≠ 0 ∧ c • v ∈ L := by
  apply GlobalTheory.LatticeIndicator.exists_int_smul_mem <;> assumption

theorem exists_nonzero_int_smul_mem_of_isLattice : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ (v : Fin n → E), ∃ (c : ℤ), c ≠ (0 : ℤ) ∧ c • v ∈ L :=
  fun L hL v => exists_int_smul_mem L hL v

end GlobalTheory.IntSmulMemLatticeTwistedOperators
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DarbouxSymp

variable {D : D7}

theorem cA_incA_eq (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp only [cA, sigR, incA, inclR]
  simp
  rfl

theorem gram_star_eq (V : HSp D) (i j) : star (V.gram i j) = V.gram j i :=
  V.herm.eq (V.frame i) (V.frame j)

theorem gram_det_ne_zero (V : HSp D) : V.gram.det ≠ 0 := by
  apply GlobalTheory.SplitOnto.gram_det_ne <;> assumption

theorem gram_map_mul_inv (V : HSp D) :
    HMul.hMul (V.gram.map (incA D) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) (V.gram⁻¹.map (incA D) : Matrix (Fin V.rank) (Fin V.rank) (AE D)) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne_zero V))]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem hO_rearr (S T : HSp D) (X Y : WO S T) : hO S T X Y =
    ∑ b, ∑ c, ∑ d, cA D (Y c b) * incA D (T.gram c d) * ∑ a, X d a * incA D (S.gram⁻¹ a b) := by
  unfold hO
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem hO_darboux (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank)
    (hT' : T'.gramᵀ = -(S.gram.submatrix e₁ e₁)) (hS' : S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂)) (x y : WO S' T') :
    hO S T (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      (HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
    hO S' T' x y := by
  have L1 : ∀ d b, ∑ a, (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) d a
      * incA D (S.gram⁻¹ a b) = x (e₁.symm b) (e₂.symm d) := by
    intro d b
    have h := congrFun (congrFun (show HMul.hMul (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      (S.gram.map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D))) (S.gram⁻¹.map (incA D) : Matrix (Fin S.rank) (Fin S.rank) (AE D))
      = (xᵀ.submatrix e₂.symm e₁.symm : Matrix (Fin T.rank) (Fin S.rank) (AE D)) by
        rw [Matrix.mul_assoc, gram_map_mul_inv, Matrix.mul_one]) d) b
    rw [Matrix.mul_apply] at h
    simpa using h
  have L2 : ∀ c b, cA D ((HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) c b)
      = ∑ k, cA D (y (e₁.symm k) (e₂.symm c)) * incA D (S.gram b k) := by
    intro c b

    rw [Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Matrix.map_apply, cA_incA_eq, gram_star_eq]
    rfl
  have E1 : ∀ a b, S'.gram⁻¹ a b = -T.gram (e₂ b) (e₂ a) := fun a b => by
    rw [hS']; rfl
  have E2 : ∀ c d, T'.gram c d = -S.gram (e₁ d) (e₁ c) := fun c d => by
    have := congrFun (congrFun hT' d) c
    simpa using this
  rw [hO_rearr]
  simp_rw [L1, L2]
  unfold hO
  simp_rw [E1, E2]
  have hR : ∀ F : Fin S.rank → Fin T.rank → Fin T.rank → Fin S.rank → AE D,
      (∀ a b c d, incA D (-T.gram (e₂ b) (e₂ a)) * cA D (y c b) * incA D (-S.gram (e₁ d) (e₁ c)) * x d a
        = F (e₁ d) (e₂ b) (e₂ a) (e₁ c)) →
      ∑ a, ∑ b, ∑ c, ∑ d, incA D (-T.gram (e₂ b) (e₂ a)) * cA D (y c b) * incA D (-S.gram (e₁ d) (e₁ c)) * x d a
        = ∑ d, ∑ c, ∑ k, ∑ b, F b c d k := by
    intro F hF
    refine Fintype.sum_equiv e₂ _ _ fun a => ?_
    refine Fintype.sum_equiv e₂ _ _ fun b => ?_
    refine Fintype.sum_equiv e₁ _ _ fun c => ?_
    refine Fintype.sum_equiv e₁ _ _ fun d => ?_
    exact hF a b c d
  rw [hR (fun b c d k => cA D (y (e₁.symm k) (e₂.symm c)) * incA D (S.gram b k) * incA D (T.gram c d) * x (e₁.symm b) (e₂.symm d))
    (fun a b c d => by simp only [Equiv.symm_apply_apply, map_neg]; ring)]
  simp only [Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]
  conv_lhs => enter [2, c, 2, d]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]

theorem symplO_darboux : ∀ (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank),
    T'.gramᵀ = -(S.gram.submatrix e₁ e₁) → S'.gram⁻¹ = -(T.gramᵀ.submatrix e₂ e₂) → ∀ x y : WO S' T',
      symplO S T (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
        (HMul.hMul (yᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      symplO S' T' x y := by
  intro D S T S' T' e₁ e₂ hT' hS' x y
  unfold symplO
  rw [hO_darboux S T S' T' e₁ e₂ hT' hS' x y]

end GlobalTheory.DarbouxSymp
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.BoundaryMaps

section General

variable {G H V W U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

end General

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]


end Local

section Products

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (g : ∀ a, Γ a) (c : α → ℂ) (h : ∀ a x, ρ a (g a) x = c a • x) (y : ⨂[ℂ] a, X a) :
    piTensor ρ g y = (∏ a, c a) • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, piTensor_tprod]
    simp only [h, MultilinearMap.map_smul_univ, RingHom.id_apply]
    rw [smul_comm]

theorem deltaHalf_scalar {α : Type} (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (z : kˣ) :
    deltaHalf k m (fun a => GeneralLinearGroup.scalar (m a) z) = 1 := by
  apply GlobalTheory.CompanionTheory.ZCentre.deltaHalf_scalar <;> assumption

theorem multiProd_scalar {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))
    (ω : α → kˣ →* ℂˣ) (h : ∀ a, HasCentralChar (ρ a) (ω a)) (z : kˣ) (f) :
    multiProd e ρ (GeneralLinearGroup.scalar n z) f = (∏ a, (ω a z : ℂ)) • f := by
  have h1 : leviEmb k e (fun a => GeneralLinearGroup.scalar (m a) z) = GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      simp [leviEmb, blockDiagonal'_apply_eq, GeneralLinearGroup.scalar, diagonal_apply]
    · simp [leviEmb, blockDiagonal'_apply_ne _ _ _ hab, GeneralLinearGroup.scalar,
        diagonal_apply, hab]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have hm : leviEmb k e (fun a => GeneralLinearGroup.scalar (m a) z) ∈ parab k e := by
    apply mem_parab_iff.2
    intro a b i j hab
    rw [h1]
    simp [GeneralLinearGroup.scalar, diagonal_apply, hab.ne']
  have hp : leviProj k e ⟨_, hm⟩ = (fun a => GeneralLinearGroup.scalar (m a) z) := by
    funext a
    ext i j
    simp [leviProj, diagBlock, leviEmb, GeneralLinearGroup.scalar, diagonal_apply]
  have h2 := parInd_law e _ f ⟨_, hm⟩ x
  rw [hp, deltaHalf_scalar, piTensor_scalar ρ _ _ fun a => h a z] at h2
  have h3 : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = (_ : ℂ) • f.1.1 x
  rw [h3, ← h1]
  simpa using h2

end Products

end GlobalTheory.BoundaryMaps
end
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

theorem _root_.GlobalTheory.T.eq_of_isQuotIntFJ_of_isQuotIntFJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f : GL (n ⊕ Fin c) k → ℂ) (z z' : ℂ), IsQuotIntFJ ν μX μG ρ f z → IsQuotIntFJ ν μX μG ρ f z' → z = z' := by
  first | exact @GlobalTheory.QuotIntFJ.quotIntFJ_unique | exact GlobalTheory.QuotIntFJ.quotIntFJ_unique | (intros; apply GlobalTheory.QuotIntFJ.quotIntFJ_unique <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PlaceTensor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def VacAt (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) :
    Place D → (WO S T → ℂ) → Prop
  | .inl v => fun f => IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f
  | .inr τ => fun f => IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f

def IsLocOp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f₀ : WO S T → ℂ)
    (p : Place D) (x : WO S T → ℂ) : Prop :=
  ∃ L : (WO S T → ℂ) → ℂ, (∀ (c : ℂ) (φ : WO S T → ℂ), L (fun w => c * φ w) = c * L φ) ∧
    (∀ f, IsThetaFunO ψ S T f → ∃ f', IsThetaFunO ψ S T f' ∧ ∀ g, IsThetaFunO ψ S T g →
      ipO μ 𝓕 f' g = L fun w => ipO μ 𝓕 (heisO ψ S T (wAt p w) f) g) ∧
    ∀ g, IsThetaFunO ψ S T g → ipO μ 𝓕 x g = L fun w => ipO μ 𝓕 (heisO ψ S T (wAt p w) f₀) g


open Classical in
def pull {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v))
    (Φ : Matrix (Fin m) (Fin n) (Fv D.host.F v) → ℂ) : WO S T → ℂ :=
  fun t => if IsHalf a t then Φ (κ t) else 0

def IsCoord {S T : HSp D} {v : FinPl D} {m n : ℕ} (a : AE D) (Λ : AddSubgroup (WO S T))
    (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)) : Prop :=
  (∀ x y, κ (x + y) = κ x + κ y) ∧ Set.BijOn κ {t | IsHalf a t} Set.univ ∧
    IsOpen (κ '' {t | t ∈ Λ ∧ IsHalf a t}) ∧ IsCompact (κ '' {t | t ∈ Λ ∧ IsHalf a t})

theorem wAt_eq_smul {m n : ℕ} (p : Place D) (w : Mx D m n) : wAt p w = idem D p • w := rfl

theorem onHalf_eq_pull {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) : onHalf φ S T BS BT e = pull e (mapCo φ S T BS BT) := rfl

theorem onHalfAdj_eq_pull {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (e : AE D) :
    onHalfAdj φ S T BS BT e = pull (cA D e) (adjCo φ S T BS BT) := rfl

theorem gAt_one (V : HSp D) (p : Place D) : gAt V p 1 = 1 := by
  cases p <;> simp [gAt]

theorem gAt_mul (V : HSp D) (p : Place D) (g g' : GA D V) : gAt V p (g * g') = gAt V p g * gAt V p g' := by
  cases p <;> simp [gAt]

theorem gAt_inv (V : HSp D) (p : Place D) (g : GA D V) : gAt V p g⁻¹ = (gAt V p g)⁻¹ := by
  cases p <;> simp [gAt]

theorem latO_mono {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {P Q : FinPl D → Prop} (h : ∀ v, P v → Q v) : latO S T LS LT P ≤ latO S T LS LT Q := by
  unfold latO
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun v hQ => hv v fun hP => hQ (h v hP), rest⟩

theorem isLatVac_mono {m n : ℕ} {hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)} {Λ Λ' : AddSubgroup (Mx D m n)}
    (h : Λ ≤ Λ') {f : Mx D m n → ℂ} (hf : IsLatVac hs Λ' f) : IsLatVac hs Λ f := by
  unfold IsLatVac at hf ⊢
  exact ⟨fun u hu => hf.1 u (h hu), fun e he u hu hh => hf.2 e he u (h hu) hh⟩

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f f₀ : WO S T → ℂ}

theorem vacAt_of_isLocal {p q : Place D} (h : IsLocal ψ θ S T sS sT ΛS ΛT p f) (hq : q ≠ p) :
    VacAt ψ θ S T sS sT ΛS ΛT q f := by
  rcases q with v | τ
  · exact isLatVac_mono (latO_mono fun u hu => hu ▸ hq) h.2.1
  · exact h.2.2 τ hq

theorem base_std (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsStdChar D ψ (-1) := by
  exact h.2.2.2.2.1

theorem base_inf (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsInfFam θ :=
  h.2.2.2.2.2.inf

theorem base_theta (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : IsThetaFunO ψ S T f₀ :=
  h.2.2.2.2.2.theta

theorem restrictedTensorBasePoint_norm_sq (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) : nrm2 μ 𝓕 f₀ = 1 := by
  exact h.2.2.2.2.2.norm.2 (μ, 𝓕) hμ

theorem base_ne_zero (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) : f₀ ≠ 0 := by
  rintro rfl
  obtain ⟨⟨μ, 𝓕⟩, hq⟩ := h.2.2.2.2.2.norm.1
  have h1 := restrictedTensorBasePoint_norm_sq h hq
  simp [nrm2] at h1

theorem base_isLocal (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (p : Place D) : IsLocal ψ θ S T sS sT ΛS ΛT p f₀ :=
  ⟨h.2.2.2.2.2.theta, isLatVac_mono (latO_mono fun _ _ => trivial) h.2.2.2.2.2.lat,
    fun τ _ => h.2.2.2.2.2.fock τ⟩

theorem base_vacAt (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (p : Place D) : VacAt ψ θ S T sS sT ΛS ΛT p f₀ := by
  rcases p with v | τ
  · exact isLatVac_mono (latO_mono fun _ _ => trivial) h.2.2.2.2.2.lat
  · exact h.2.2.2.2.2.fock τ

end

end GlobalTheory.PlaceTensor

end
end

section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

theorem _root_.GlobalTheory.T.tensorIdeleNormalizedAbs_eq_adelic_abs_norm : ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Algebra F E] (y : (AF F ⊗[F] E)ˣ), (∏ w, ‖(fstA F (Algebra.norm (AF F) (y : AF F ⊗[F] E))) w‖) * ∏ᶠ v, ‖evalV F v (sndA F (Algebra.norm (AF F) (y : AF F ⊗[F] E)))‖ = (GlobalTheory.Doubling.absE F E y : ℝ) := by
  first | exact @GlobalTheory.absE_eq_prod_norm_fstA_sndA | exact GlobalTheory.absE_eq_prod_norm_fstA_sndA | (intros; apply GlobalTheory.absE_eq_prod_norm_fstA_sndA <;> assumption)
end

section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

theorem _root_.GlobalTheory.T.relIndex_twoBlockParahoric_conj_torusDiagElement : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ),
    valuation k (ϖ : k) = uniformizer k →
    ∀ (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (e : D → ℤ),
    (((parahoric k A D).map (MulAut.conj (mtor (A := A) ϖ e)).toMonoidHom).relIndex (parahoric k A D) : ℝ) =
      (resCard k : ℝ) ^ ((Fintype.card A : ℤ) * sumAbs e) *
        (((KO k D).map (MulAut.conj (torusElt k D ϖ e)).toMonoidHom).relIndex (KO k D) : ℝ) := by
  first | exact @GlobalTheory.ParIdx.relIndex_parahoric_conj_mtor | exact GlobalTheory.ParIdx.relIndex_parahoric_conj_mtor | (intros; apply GlobalTheory.ParIdx.relIndex_parahoric_conj_mtor <;> assumption)
end

section

open Classical

namespace GlobalTheory.LevelVecNorm

theorem finsum_indicator_one_eq_ncard' {α : Type} (s : Set α) :
    (∑ᶠ x, s.indicator (fun _ => (1:ℝ)) x) = (s.ncard : ℝ) := by
  by_cases hs : s.Finite
  · rw [← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]
    simp
  · have hsupp : Function.support (s.indicator (fun _ => (1:ℝ))) = s := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [finsum_of_infinite_support (by rw [hsupp]; exact hs), Set.Infinite.ncard hs]
    simp

theorem suppInd_sq_sum_eq_card : ∀ {k : Type} [CommRing k] {b a : ℕ} (r t : ℕ), b = r + t → a = r → ∀ H : Subgroup (GL (Fin r) k),
    ∑ᶠ z : Matrix (Fin b) (Fin a) k, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = (Nat.card H : ℝ) := by
  intro k _ b a r t hb ha H
  subst hb; subst a
  let f : GL (Fin r) k → Matrix (Fin (r + t)) (Fin r) k := fun g i j =>
    if h : i.val < r then (g : Matrix (Fin r) (Fin r) k) ⟨i.val, h⟩ j else 0
  have htop : ∀ g, Formalism.IndefR.Datum.topL r (f g) = (g : Matrix (Fin r) (Fin r) k) := by
    intro g; ext i j
    simp [Formalism.IndefR.Datum.topL, f, i.isLt, j.isLt, show i.val < r + t by omega]
  have hlow : ∀ g, Formalism.IndefR.Datum.LowZero r (f g) := by
    intro g i j hi _
    simp [f, show ¬ i.val < r by omega]
  have hinj : Function.Injective f := by
    intro g g' h
    apply Units.ext
    rw [← htop g, ← htop g', h]
  let S : Set (Matrix (Fin (r + t)) (Fin r) k) :=
    {z | Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z}
  have hS : S = f '' (H : Set (GL (Fin r) k)) := by
    ext z
    constructor
    · rintro ⟨hz, g, hg, hgz⟩
      refine ⟨g, hg, ?_⟩
      ext i j
      by_cases hi : i.val < r
      · have := congrFun (congrFun hgz ⟨i.val, hi⟩) j
        simp only [Formalism.IndefR.Datum.topL, j.isLt, show i.val < r + t by omega] at this
        simpa [f, hi] using this
      · simp [f, hi, hz i j (by omega) j.isLt]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hlow g, g, hg, (htop g).symm⟩
  have hfun : ∀ z, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = S.indicator (fun _ => (1:ℝ)) z := by
    intro z
    unfold GlobalTheory.LevelVecNorm.suppInd
    by_cases hz : z ∈ S
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_pos hz', Set.indicator_of_mem hz]; norm_num
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_neg hz', Set.indicator_of_notMem hz]; norm_num
  simp_rw [hfun]
  rw [finsum_indicator_one_eq_ncard', hS, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
  rfl

end GlobalTheory.LevelVecNorm
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.zelevinskySegmentClass_exists_for_every_placing : GlobalTheory.Published.SegmentRepresentation → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∃ Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k), IsSegmentClass k Z := by
  first | exact @GlobalTheory.segmentClass_exists | exact GlobalTheory.segmentClass_exists | (intros; apply GlobalTheory.segmentClass_exists <;> assumption)
end
