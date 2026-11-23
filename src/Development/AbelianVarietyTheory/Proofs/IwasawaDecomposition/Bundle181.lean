module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle173
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle174
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle167
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle176
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.Columns.LevGSym
public import Formalism.LocalToGlobal.HermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle132
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.JoinForms
public import Formalism.LocalToGlobal.Columns.RecLevelSymF
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SymplecticTensorMeasures
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss.ParDer

variable {l m n : Type} [Fintype m]

theorem der_mul {M : ℝ → Matrix l m ℂ} {N : ℝ → Matrix m n ℂ} {M' : Matrix l m ℂ} {N' : Matrix m n ℂ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s) (hN : ∀ i j, HasDerivAt (fun t => N t i j) (N' i j) s)
    (i : l) (j : n) : HasDerivAt (fun t => (M t * N t) i j) ((M' * N s + M s * N') i j) s := by
  simp only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hM i k).fun_mul (hN k j)

theorem der_dot {u v : ℝ → m → ℂ} {u' v' : m → ℂ} {s : ℝ}
    (hu : ∀ i, HasDerivAt (fun t => u t i) (u' i) s) (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s) :
    HasDerivAt (fun t => u t ⬝ᵥ v t) (u' ⬝ᵥ v s + u s ⬝ᵥ v') s := by
  simp only [dotProduct, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _ => (hu k).fun_mul (hv k)

theorem der_mulVec {M : ℝ → Matrix l m ℂ} {v : ℝ → m → ℂ} {M' : Matrix l m ℂ} {v' : m → ℂ} {s : ℝ}
    (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s) (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s)
    (i : l) : HasDerivAt (fun t => (M t *ᵥ v t) i) ((M' *ᵥ v s + M s *ᵥ v') i) s :=
  der_dot (u := fun t => M t i) (u' := M' i) (hM i) hv

theorem der_vecMul {M : ℝ → Matrix m n ℂ} {v : ℝ → m → ℂ} {M' : Matrix m n ℂ} {v' : m → ℂ} {s : ℝ}
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) s) (hM : ∀ i j, HasDerivAt (fun t => M t i j) (M' i j) s)
    (j : n) : HasDerivAt (fun t => (v t ᵥ* M t) j) ((v' ᵥ* M s + v s ᵥ* M') j) s :=
  der_dot (v := fun t i => M t i j) (v' := fun i => M' i j) hv fun i => hM i j

theorem par_deriv : ∀ (P Q : ℕ) (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (Z : Mat P Q) (g g' : ℝ → Mat P Q), g 0 = 1 → g' 0 = 1 → (∀ a b, HasDerivAt (fun t => g t a b) (Z a b) 0) → (∀ a b, HasDerivAt (fun t => g' t a b) (-Z a b) 0) → (∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0) ∧ (∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0) ∧ HasDerivAt (fun t => scal (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t)) (dS Z A x) 0 := by
  intro P Q A x Z g g' h0 h0' hg hg'
  have hY : ∀ i j, HasDerivAt (fun t => (g t * baseY A) i j) ((Z * baseY A) i j) 0 := fun i j => by
    simpa using der_mul (N := fun _ => baseY A) (N' := 0) hg (fun _ _ => hasDerivAt_const _ _) i j
  have hZ : Z * baseY A = Matrix.fromRows (Z.toBlocks₁₁ * A + Z.toBlocks₁₂) (Z.toBlocks₂₁ * A + Z.toBlocks₂₂) := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks Z, baseY, Matrix.fromBlocks_mul_fromRows]
    simp
  have hY1 : ∀ i j, HasDerivAt (fun t => (g t * baseY A).toRows₁ i j) ((Z.toBlocks₁₁ * A + Z.toBlocks₁₂) i j) 0 :=
    fun i j => by have := hY (.inl i) j; rw [hZ] at this; exact this
  have hY2 : ∀ i j, HasDerivAt (fun t => (g t * baseY A).toRows₂ i j) ((Z.toBlocks₂₁ * A + Z.toBlocks₂₂) i j) 0 :=
    fun i j => by have := hY (.inr i) j; rw [hZ] at this; exact this
  have e2 : (g 0 * baseY A).toRows₂ = 1 := by rw [h0, Matrix.one_mul]; rfl
  have e1 : (g 0 * baseY A).toRows₁ = A := by rw [h0, Matrix.one_mul]; rfl
  obtain ⟨hdet, hinv⟩ := GlobalTheory.T.hasDerivAt_inv_det_and_inv_at_identity Q (fun t => (g t * baseY A).toRows₂) _ e2 hY2
  have hA : ∀ i j, HasDerivAt (fun t => matA (g t * baseY A) i j) (dA Z A i j) 0 := fun i j => by
    have := der_mul (N' := -(Z.toBlocks₂₁ * A + Z.toBlocks₂₂)) hY1 hinv i j
    rw [e1, e2, inv_one, Matrix.mul_one, Matrix.mul_neg, ← sub_eq_add_neg] at this
    exact this
  have eA : matA (g 0 * baseY A) = A := by rw [h0, Matrix.one_mul, matA_baseY]
  have hv : ∀ i, HasDerivAt (fun t => (g t *ᵥ baseV x) i) ((Z *ᵥ baseV x) i) 0 := fun i => by
    simpa using der_mulVec (v := fun _ => baseV x) (v' := 0) hg (fun _ => hasDerivAt_const _ _) i
  have hf : ∀ i, HasDerivAt (fun t => (baseF x ᵥ* g' t) i) ((baseF x ᵥ* (-Z)) i) 0 := fun i => by
    simpa using der_vecMul (v := fun _ => baseF x) (v' := 0) (M' := -Z) (fun _ => hasDerivAt_const _ _) hg' i
  have hv1 : ∀ i, HasDerivAt (fun t => ((g t *ᵥ baseV x) ∘ Sum.inl) i) ((Z.toBlocks₁₁ *ᵥ (x ∘ Sum.inl)) i) 0 :=
    fun i => (hv (.inl i)).congr_deriv (by
      simp [mulVec, dotProduct, baseV, Fintype.sum_sum_type, Matrix.toBlocks₁₁])
  have hv2 : ∀ i, HasDerivAt (fun t => ((g t *ᵥ baseV x) ∘ Sum.inr) i) ((Z.toBlocks₂₁ *ᵥ (x ∘ Sum.inl)) i) 0 :=
    fun i => (hv (.inr i)).congr_deriv (by
      simp [mulVec, dotProduct, baseV, Fintype.sum_sum_type, Matrix.toBlocks₂₁])
  have hf1 : ∀ i, HasDerivAt (fun t => ((baseF x ᵥ* g' t) ∘ Sum.inl) i) ((-((x ∘ Sum.inr) ᵥ* Z.toBlocks₂₁)) i) 0 :=
    fun i => (hf (.inl i)).congr_deriv (by
      simp [vecMul, dotProduct, baseF, Fintype.sum_sum_type, Matrix.toBlocks₂₁])
  have hf2 : ∀ i, HasDerivAt (fun t => ((baseF x ᵥ* g' t) ∘ Sum.inr) i) ((-((x ∘ Sum.inr) ᵥ* Z.toBlocks₂₂)) i) 0 :=
    fun i => (hf (.inr i)).congr_deriv (by
      simp [vecMul, dotProduct, baseF, Fintype.sum_sum_type, Matrix.toBlocks₂₂])
  have ev : (g 0 *ᵥ baseV x) ∘ Sum.inr = 0 := by rw [h0, Matrix.one_mulVec]; rfl
  have ef : (baseF x ᵥ* g' 0) ∘ Sum.inl = 0 := by rw [h0', Matrix.vecMul_one]; rfl
  have hX : ∀ l, HasDerivAt (fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) l) (dX Z A x l) 0 := by
    rintro (i | j)
    · refine ((hv1 i).fun_sub (der_mulVec hA hv2 i)).congr_deriv ?_
      rw [ev, eA]
      simp [dX, Matrix.sub_mulVec, Matrix.mulVec_mulVec]
    · refine ((der_vecMul hf1 hA j).fun_add (hf2 j)).congr_deriv ?_
      rw [ef, eA]
      simp [dX, Matrix.vecMul_add, Matrix.neg_vecMul, Matrix.vecMul_vecMul, add_comm]
  refine ⟨hA, hX, ?_⟩
  have hd := der_dot (u := fun t => linX (g t * baseY A) (g t *ᵥ baseV x) (baseF x ᵥ* g' t) ∘ Sum.inr)
    (u' := dX Z A x ∘ Sum.inr) (fun j => hX (.inr j)) hv2
  refine (hdet.fun_mul hd.fun_neg.cexp).congr_deriv ?_
  simp only [ev, e2]
  rw [h0, h0', Matrix.one_mul, Matrix.one_mulVec, Matrix.vecMul_one, linX_base]
  simp [dS, sub_eq_add_neg]

end GlobalTheory.OscGauss.ParDer
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.columnMinorProducts_fock_reproducing_identity : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (h : MvPolynomial (Fin N × Fin N) ℚ),
    h ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r => Y.rowLen r) →
    ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, Formalism.GradedWeylDivisibility.fockQ h (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J
      = Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) • h := by
  first | exact @GlobalTheory.WeylReproducing.reproducing | exact GlobalTheory.WeylReproducing.reproducing | (intros; apply GlobalTheory.WeylReproducing.reproducing <;> assumption)
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.integral_minors_iff_basis_alt : ∀ (p : ℕ) [Fact p.Prime] (Lt : Type) [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ)
    (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ) (d : ∀ s, ι s → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, b s k = ∑ J, (d s k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      (∀ J : WeylLatticeDuality.ColChoice N nu,
          ‖φ (MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1) ↔
        ∀ κ : (∀ s, ι s), ‖φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
          (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s))))‖ ≤ 1 := by
  first | exact @GlobalTheory.WeylLatDualProof.integral_minors_iff_basis | exact GlobalTheory.WeylLatDualProof.integral_minors_iff_basis | (intros; apply GlobalTheory.WeylLatDualProof.integral_minors_iff_basis <;> assumption)
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.phi_DeX_expand_alt : ∀ (p : ℕ) [Fact p.Prime] (Lt T : Type) [Fintype Lt] [DecidableEq Lt] [Fintype T] (e : Lt → T) (N : ℕ)
    (nu : Lt → YoungDiagram) (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b g : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ) (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, g s k = ∑ J, (c s J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ (φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p])) (y : T → Matrix (Fin N) (Fin N) ℂ_[p]),
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s))) =
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) := by
  first | exact @GlobalTheory.WeylLatDualProof.phi_DeX_expand | exact GlobalTheory.WeylLatDualProof.phi_DeX_expand | (intros; apply GlobalTheory.WeylLatDualProof.phi_DeX_expand <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.FrobDense GlobalTheory.CuspRep.NormTriv

namespace GlobalTheory.CuspRep.CsdFin

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation "𝐜" => AlgEquiv.toRingEquiv (IsCMField.complexConj L)

theorem loc_of_idelic (χ : HChar L)
    (h : ∀ u : (Af L)ˣ, χ.1 (finId L (Units.map (conjFin 𝐜).toMonoidHom u)⁻¹) = χ.1 (finId L u))
    {w w' : HeightOneSpectrum (𝓞 L)} (hc : GlobalTheory.Mem.Chr.ConjPl 𝐜 w w') (k : Lˣ) :
    χ.locK w' (cU 𝐜 k) = (χ.locK w k)⁻¹ := by
  have h1 := h (Units.map (Neutral.B1.finiteSingle L w) (atFin w k))
  rw [conjFin_finSingle 𝐜 hc, map_inv, finId_finSingle, finId_finSingle, map_inv] at h1
  change χ.1 (localIdele L w' (atFin w' (cU 𝐜 k))) = (χ.1 (localIdele L w (atFin w k)))⁻¹
  rw [← h1, inv_inv]

theorem idelic_of_loc (χ : HChar L)
    (h : ∀ w w', GlobalTheory.Mem.Chr.ConjPl 𝐜 w w' → ∀ k : Lˣ, χ.locK w' (cU 𝐜 k) = (χ.locK w k)⁻¹) (u : (Af L)ˣ) :
    χ.1 (finId L (Units.map (conjFin 𝐜).toMonoidHom u)⁻¹) = χ.1 (finId L u) := by
  have h1 : ∀ v x, normFin 𝐜 χ (localIdele L v x) = 1 := fun v => by
    obtain ⟨v', hv', -⟩ := GlobalTheory.Mem.Chr.existsUnique_conjPl 𝐜 v
    refine loc_eq_one_of_prod (continuous_normFin _ χ) {v} (fun k => ?_) (Finset.mem_singleton_self v)
    rw [Finset.prod_singleton, normFin_loc _ χ hv' k, h v v' hv' k, mul_inv_cancel]
  have h3 := GlobalTheory.FrobDense.eq_one_of_local _ (continuous_normFin 𝐜 χ) (finId L u) (by
    change (1 : InfiniteAdeleRing L) - 0 + 0 = 1
    simp) fun v => h1 v _
  have e : Units.map (pFin L).toMonoidHom (finId L u) = u := Units.ext (by
    change (1 : Af L) - 1 + u = u
    simp)
  change χ.1 (finId L (Units.map (pFin L).toMonoidHom (finId L u) *
    Units.map (conjFin 𝐜).toMonoidHom (Units.map (pFin L).toMonoidHom (finId L u)))) = 1 at h3
  rw [e, map_mul, map_mul] at h3
  rw [map_inv, map_inv]
  exact (eq_inv_of_mul_eq_one_left h3).symm

end GlobalTheory.CuspRep.CsdFin


open GlobalTheory.CuspRep.CsdFin in
theorem GlobalTheory.CuspRep.csdFin_iff : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), haveI := host_isCMField H;
    (∀ u : (Af H.E)ˣ, χ.1 (finId H.E (Units.map (conjFin (IsCMField.complexConj H.E).toRingEquiv).toMonoidHom u)⁻¹) =
      χ.1 (finId H.E u)) ↔
    ∀ w w', Formalism.BasicNotions.IsConjPl H w w' → ∀ k : H.Eˣ,
      χ.locK w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.locK w k)⁻¹ := by
  intro R H χ
  have := host_isCMField H
  have hk : ∀ k : H.Eˣ, Units.map (MonoidHomClass.toMonoidHom H.conj) k =
      cU (IsCMField.complexConj H.E).toRingEquiv k := fun k => Units.ext (host_complexConj H k).symm
  have hp : ∀ w w', Formalism.BasicNotions.IsConjPl H w w' ↔ GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj H.E).toRingEquiv w w' :=
    fun w w' => by
      rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
      exact ⟨fun hc x y e => hc x y (e.trans (host_complexConj H _)),
        fun hc x y e => hc x y (e.trans (host_complexConj H _).symm)⟩
  constructor
  · intro h w w' hc k
    rw [hk]
    exact loc_of_idelic χ h ((hp w w').1 hc) k
  · intro h
    exact idelic_of_loc χ fun w w' hc k => by rw [← hk]; exact h w w' ((hp w w').2 hc) k
end
end

section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

theorem _root_.GlobalTheory.T.exists_frob_of_eisenstein_root : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A v →
    ∀ ϖ : 𝓞 E, ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ∀ π : Ω, π ^ (_root_.Formalism.ConjugateSelfDual.normV v - 1) = algebraMap E Ω (ϖ : E) →
    ∃ τ : _root_.Formalism.ConjugateSelfDual.G E Ω, IsFrob (F := E) A (_root_.Formalism.ConjugateSelfDual.normV v) τ ∧ τ π = π ∧
      ∀ c : (v.adicCompletion E)ˣ, (c : v.adicCompletion E) = (-1) ^ _root_.Formalism.ConjugateSelfDual.normV v * algebraMap E (v.adicCompletion E) (ϖ : E) →
        toAb E Ω τ⁻¹ = art (localIdele E v c) := by
  exact @GlobalTheory.TameRecip.exists_frob_fix_of_eisenstein
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (cE cE_cE cA_inc cA_cA ConjIsom conj_map_mem_unitaryGroup)
open scoped TensorProduct

namespace GlobalTheory.ConjAutProps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem continuous_conjA (D : D7) : Continuous (cA D) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap
  exact this

end GlobalTheory.ConjAutProps

end
end

section

open Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamRead

theorem sum_skip {F : Type} [Field F] {n r k : ℕ} (hr : r ≤ n) (hk : k ≤ r) (N : Matrix (Fin n) (Fin n) F) (f : ℕ → ℕ → F)
    (hf : ∀ i j : Fin n, f i.1 j.1 = N i j) :
    (∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < r ∧ (y : ℕ) ≠ k then N x y else 0) =
      ∑ i ∈ Finset.range (k - 1), f i (i + 1) + ∑ i ∈ Finset.range (r - k - 1), f (k + i) (k + i + 1) := by
  rw [Formalism.L2.G.sum_sup hr k ((Finset.range r).filter (fun x => x + 1 ≠ k))
    (fun x hx => by simp only [Finset.mem_filter, Finset.mem_range]; constructor <;> intro h <;> first | exact h.2 | exact ⟨by omega, h⟩) N,
    Finset.filter_filter, Finset.sum_filter]
  have h1 : ∀ x ∈ Finset.range r, (if x + 1 ≠ k ∧ x + 1 < r then Formalism.L2.G.entN N x (x + 1) else 0) =
      if x + 1 < r ∧ x + 1 ≠ k then f x (x + 1) else 0 := fun x hx => by
    by_cases hx' : x + 1 < r ∧ x + 1 ≠ k
    · rw [if_pos hx', if_pos ⟨hx'.2, hx'.1⟩]
      have a1 : x < n := by omega
      have a2 : x + 1 < n := by omega
      unfold Formalism.L2.G.entN
      rw [dif_pos ⟨a1, a2⟩]
      exact (hf ⟨x, a1⟩ ⟨x + 1, a2⟩).symm
    · rw [if_neg hx', if_neg (fun h => hx' ⟨h.2, h.1⟩)]
  rw [Finset.sum_congr rfl h1]
  obtain ⟨d, rfl⟩ : ∃ d, r = k + d := ⟨r - k, by omega⟩
  rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
  by_cases hd : d = 0
  · subst hd
    rw [GlobalTheory.TopLawSym.sum_pred k _ _ fun p hp => by omega]
    simp
  · rw [GlobalTheory.TopLawSym.sum_pred k _ _ fun p hp => by omega,
      GlobalTheory.TopLawSym.sum_pred d (fun p => f (k + p) (k + p + 1)) (fun p => k + p + 1 < k + d ∧ k + p + 1 ≠ k) fun p hp => by omega]

theorem coarse_iff {r m t s i : ℕ} (ht : 0 < t) (hs : s < m) :
    coarse r (List.replicate m t) i = s + 1 ↔ r + s * t ≤ i ∧ i < r + s * t + t := by
  have hb := GlobalTheory.DatumLaw.blk_le (r := r) (a := r + m * t) hs le_rfl
  by_cases hir : i < r
  · rw [coarse_of_lt hir]
    omega
  · by_cases h2 : i < r + m * t
    · rw [GlobalTheory.TopLawSym.coarse_eq ht (by omega) h2, Nat.add_right_cancel_iff, Nat.div_eq_iff ht]
      omega
    · rw [coarse_of_le (by omega), blkIdx_replicate_of_le t m _ (by
        have := Nat.sub_le_sub_right (Nat.not_lt.1 h2) r
        rwa [Nat.add_sub_cancel_left] at this)]
      omega

theorem lamJsym_read (κ κ' K : Type) [CommRing κ] [Field κ'] [Field K] (e : κ →+* κ') (emb : K →+* ℂ) (ψ : AddChar κ K)
    (χ : ℕ → κˣ →* Kˣ) (ψ' : AddChar κ' ℂ) (χ' : ℕ → MulChar κ' ℂ) (n k r t m rS : ℕ) (h : r ≤ n) (hr : r = k + 2 * rS + 1)
    (ht : 0 < t) (hn : r + m * t ≤ n) (hψ : ∀ x, ψ' (e x) = emb (ψ x))
    (hχ : ∀ s, s < m → ∀ c : κˣ, χ' s (e c) = emb ((χ s c : Kˣ) : K)) (M : HJsym κ n k r t m rS h) :
    emb ((lamJsym ψ χ n k r t m rS h M : Kˣ) : K) =
      Formalism.L2.Forms.lamSym ψ' χ' k rS t m ((M.1 : Matrix (Fin n) (Fin n) κ).map e) := by
  let A : ℕ → ℕ → κ := fun i j => if h' : i < n ∧ j < n then (M.1 : Matrix (Fin n) (Fin n) κ) ⟨i, h'.1⟩ ⟨j, h'.2⟩ else 0
  have hA : ∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j := fun i j => dif_pos ⟨i.2, j.2⟩
  have h0 : ((lamJsym ψ χ n k r t m rS h M : Kˣ) : K) =
      ((chiSymF ψ r k rS (HPar0 h _ _ M) : Kˣ) : K) *
        ((detChar χ n r (List.replicate m t) ⟨M.1, HPar_le h _ _ M.2⟩ : Kˣ) : K) := rfl
  have hrS : Formalism.L2.Forms.rSym k rS = r := hr.symm
  rw [h0, GlobalTheory.TopLawSym.chiSymF_val ψ (by omega) (HPar0 h _ _ M) A fun i j => hA (Fin.castLE h i) (Fin.castLE h j), detChar_apply,
    List.length_replicate, Units.coe_prod, map_mul, map_prod, ← hψ]
  unfold Formalism.L2.Forms.lamSym Formalism.L2.Forms.lamJ
  rw [hrS]
  congr 1
  · congr 1

    rw [sum_skip h (by omega) _ (fun i j => e (A i j)) fun i j => by rw [hA]; rfl, map_add (f := _), map_sum, map_sum]
  · refine Finset.prod_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    rw [← hχ s hs, GlobalTheory.TopLaw.blkDet_eq_dB (coarse r (List.replicate m t)) (s + 1) (r + s * t) t (GlobalTheory.DatumLaw.blk_le hs hn)
      (fun i _ => coarse_iff ht hs) ⟨M.1, HPar_le h _ _ M.2⟩ A hA]
    unfold GlobalTheory.DatumLaw.dB
    rw [RingHom.map_det]
    congr 2
    ext u v
    have hb := GlobalTheory.DatumLaw.blk_le hs hn
    have a1 : r + s * t + u.1 < n := by have := u.2; omega
    have a2 : r + s * t + v.1 < n := by have := v.2; omega
    show e (A (r + s * t + u.1) (r + s * t + v.1)) = Formalism.L2.Forms.entN _ (r + s * t + u.1) (r + s * t + v.1)
    unfold Formalism.L2.Forms.entN
    rw [dif_pos ⟨a1, a2⟩]
    exact congrArg e (hA ⟨_, a1⟩ ⟨_, a2⟩)

end GlobalTheory.LamRead
end
end

section

open Formalism.L2.Col

namespace GlobalTheory

theorem mem_HJsym_iff_JSymG : ∀ (κ : Type) [Field κ] (n k r t m rS : ℕ) (h : r ≤ n), r = k + 2 * rS + 1 → 0 < t → n = r + m * t →
    ∀ M : GL (Fin n) κ, M ∈ HJsym κ n k r t m rS h ↔ M ∈ Formalism.L2.Forms.JSymG κ n k rS t false := by
  intro κ _ n k r t m rS h hr ht hn M
  subst hr
  rw [HJsym_eq_JSymG ht (by omega) h]

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Datum
open scoped Matrix

namespace GlobalTheory.TwistDatumRight

section
variable {κ : Type} [CommRing κ] {b r : ℕ}

theorem topL_mul_right (y : Matrix (Fin b) (Fin r) κ) (h : Matrix (Fin r) (Fin r) κ) :
    topL r (y * h) = topL r y * h := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, hi, Matrix.mul_apply]
  · simp [topL, hi, Matrix.mul_apply]

theorem lowZero_mul_right {y : Matrix (Fin b) (Fin r) κ} (hy : LowZero r y) (h : Matrix (Fin r) (Fin r) κ) :
    LowZero r (y * h) := by
  intro i j hi _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun k _ => by rw [hy i k hi k.2, zero_mul]

theorem lowZero_mul_right_iff (y : Matrix (Fin b) (Fin r) κ) (h : GL (Fin r) κ) :
    LowZero r (y * h.1) ↔ LowZero r y := by
  refine ⟨fun H => ?_, fun H => lowZero_mul_right H _⟩
  have := lowZero_mul_right H (h⁻¹).1
  rwa [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this

theorem det_topL_mul_right (y : Matrix (Fin b) (Fin r) κ) (h : GL (Fin r) κ) :
    (topL r (y * h.1)).det = ((Matrix.GeneralLinearGroup.det h : κˣ) : κ) * (topL r y).det := by
  rw [topL_mul_right, Matrix.det_mul, mul_comm, Matrix.GeneralLinearGroup.val_det_apply]

end

theorem omegaQ_mul_right : ∀ (D : D7) (b r : ℕ) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (h : ∀ PP : Pl D.host.E, GL (Fin r) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin r) (kP PP)), (∀ PP ∈ Q, y' PP = y PP * (h PP).1) → omegaQ Q r ξ (-1) y' = ((∏ PP ∈ Q, ξ PP (Matrix.GeneralLinearGroup.det (h PP)) : ℂˣ) : ℂ)⁻¹ * omegaQ Q r ξ (-1) y := by
  intro D b r Q ξ h y y' hy
  have hiff : (∀ PP ∈ Q, LowZero r (y' PP) ∧ IsUnit (topL r (y' PP)).det) ↔
      (∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det) := by
    refine forall₂_congr fun PP hP => ?_
    rw [hy PP hP, lowZero_mul_right_iff, det_topL_mul_right, Units.isUnit_units_mul]
  unfold omegaQ
  by_cases c : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det
  · rw [dite_eq_left c, dite_eq_left (hiff.2 c), ← Finset.prod_attach Q, Units.coe_prod, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : ((hiff.2 c) PP.1 PP.2).2.unit =
        Matrix.GeneralLinearGroup.det (h PP.1) * (c PP.1 PP.2).2.unit := by
      apply Units.ext
      rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hy PP.1 PP.2, det_topL_mul_right]
    rw [e, map_mul, Units.val_mul, zpow_neg_one, zpow_neg_one, mul_inv]
  · rw [dite_eq_right c, dite_eq_right (fun h' => c (hiff.1 h')), mul_zero]

end GlobalTheory.TwistDatumRight
end

section

open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.Member

theorem exists_isInfFam_family : ∀ D : D7, ∃ θ : InfFam D, IsInfFam θ :=
  fun D => GlobalTheory.DualPairCompare.exists_infFam D

end GlobalTheory.Member
end
