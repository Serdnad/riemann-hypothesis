module

import Formalism.LocalToGlobal.IndefiniteReal.MemSpanOfSmulMem
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrbitStepSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle049
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle003
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle034
public import Formalism.HermitianLattices.FinalMass
import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle048
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldSplitCompletelyPlaceStructure
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle095
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

section

open NumberField

namespace GlobalTheory.SpanInfDenominators

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (Λ : Submodule (𝓞 E) V) (x : V)
    (hx : x ∈ Submodule.span E (Λ : Set V)) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • x ∈ Λ := by
  apply Formalism.IndefR.LatticeTransfer.Lat.exists_smul_mem <;> assumption

theorem le_spanE_inf_toO {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsFullLattice E Λ) (U : Submodule E S.V) :
    U ≤ Formalism.MainNotions.S.Lat.spanE S (Λ ⊓ Formalism.MainNotions.S.Lat.toO S U) := by
  intro x hx
  have hxs : x ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hΛ.span_eq_top]
    trivial
  obtain ⟨c, hc, hcx⟩ := exists_smul_mem Λ x hxs
  have hcU : c • x ∈ U := by
    rw [← algebraMap_smul E c x]
    exact U.smul_mem _ hx
  have hmem : c • x ∈ Λ ⊓ Formalism.MainNotions.S.Lat.toO S U := Submodule.mem_inf.2 ⟨hcx, hcU⟩
  have hc' : algebraMap (𝓞 E) E c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
  have hx' : x = (algebraMap (𝓞 E) E c)⁻¹ • (c • x) := by
    rw [← algebraMap_smul E c x, smul_smul, inv_mul_cancel₀ hc', one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.SpanInfDenominators
end

section

open Formalism.REAL Matrix

namespace GlobalTheory.OnbSum

theorem conjTranspose_eq_of_inG {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : inG ε X) : Xᴴ = -(Jm ε * X * Jm ε) := by
  have h' : Xᴴ * Jm ε + Jm ε * X = 0 := h
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h'
  calc Xᴴ = Xᴴ * (Jm ε * Jm ε) := by rw [Jm_mul_self, Matrix.mul_one]
    _ = Xᴴ * Jm ε * Jm ε := (Matrix.mul_assoc _ _ _).symm
    _ = -(Jm ε * X * Jm ε) := by rw [h1, Matrix.neg_mul]

theorem trace_im_eq_zero {n : ℕ} {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : inG ε A) (hB : inG ε B) : (Matrix.trace (A * Bᴴ)).im = 0 := by
  have hA' := conjTranspose_eq_of_inG hA
  have hB' := conjTranspose_eq_of_inG hB
  have swap : Matrix.trace (B * Aᴴ) = Matrix.trace (A * Bᴴ) := by
    rw [hA', hB', Matrix.mul_neg, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_neg, neg_inj]
    calc Matrix.trace (B * (Jm ε * A * Jm ε)) = Matrix.trace ((B * Jm ε * A) * Jm ε) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Jm ε * (B * Jm ε * A)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace ((Jm ε * B * Jm ε) * A) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (A * (Jm ε * B * Jm ε)) := Matrix.trace_mul_comm _ _
  have hstar : (starRingEnd ℂ) (Matrix.trace (A * Bᴴ)) = Matrix.trace (A * Bᴴ) := by
    rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, swap]
  exact Complex.conj_eq_iff_im.mp hstar

theorem sum_norm_sq_of_isometry {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Matrix ι κ ℂ) (hM : Mᴴ * M = 1)
    (y : κ → V) : ∑ i, ‖∑ p, M i p • y p‖ ^ 2 = ∑ p, ‖y p‖ ^ 2 := by
  have key : ∀ p q, ∑ i, (starRingEnd ℂ) (M i p) * M i q = if p = q then (1 : ℂ) else 0 := by
    intro p q
    have h := congrFun (congrFun hM p) q
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa only [Matrix.conjTranspose_apply, Complex.star_def] using h
  have hsq : ∀ v : V, (‖v‖ : ℂ) ^ 2 = inner ℂ v v := fun v => (inner_self_eq_norm_sq_to_K v).symm
  have expand : ∀ i, inner ℂ (∑ p, M i p • y p) (∑ q, M i q • y q) =
      ∑ p, ∑ q, (starRingEnd ℂ) (M i p) * M i q * inner ℂ (y p) (y q) := by
    intro i
    rw [sum_inner]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [inner_smul_left, inner_smul_right, mul_assoc]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [hsq, expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, key]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem onb_sum : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (y : Fin n → Fin n → V), (∀ F : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsONFamily ε F → ∑ i, ‖∑ a, ∑ b, F i a b • y a b‖ ^ 2 = ∑ a, ∑ b, ‖y a b‖ ^ 2) ∧ ∀ X : Matrix (Fin n) (Fin n) ℂ, ‖∑ a, ∑ b, X a b • y a b‖ ^ 2 ≤ hs X * ∑ a, ∑ b, ‖y a b‖ ^ 2 := by
  intro n ε V _ _ y
  refine ⟨fun F hF => ?_, fun X => ?_⟩
  · let M : Matrix (Fin (n ^ 2)) (Fin n × Fin n) ℂ := fun i p => F i p.1 p.2
    have hrow : M * Mᴴ = 1 := by
      ext i j
      have hre := hF.2 i j
      have him := trace_im_eq_zero (hF.1 i) (hF.1 j)
      have htr : Matrix.trace (F i * (F j)ᴴ) = (M * Mᴴ) i j := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
        rw [Fintype.sum_prod_type]
      rw [← htr, Matrix.one_apply]
      apply Complex.ext
      · rw [hre]; split_ifs <;> simp
      · rw [him]; split_ifs <;> simp
    have e : Fin n × Fin n ≃ Fin (n ^ 2) := Fintype.equivOfCardEq (by simp [sq])
    have hcol : Mᴴ * M = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).mp hrow
    have hiso := sum_norm_sq_of_isometry M hcol (fun p => y p.1 p.2)
    simpa only [M, Fintype.sum_prod_type] using hiso
  · have h1 : ‖∑ a, ∑ b, X a b • y a b‖ ≤ ∑ a, ∑ b, ‖X a b‖ * ‖y a b‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => (norm_smul (X a b) (y a b)).le))
    have h2 : (∑ a, ∑ b, ‖X a b‖ * ‖y a b‖) ^ 2 ≤ hs X * ∑ a, ∑ b, ‖y a b‖ ^ 2 := by
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
        (fun p => ‖X p.1 p.2‖) (fun p => ‖y p.1 p.2‖)
      simpa only [hs, Fintype.sum_prod_type] using hcs
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

end GlobalTheory.OnbSum
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.StepLoc

open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem kset_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : inUJ ε g := by
  have h1 : gᴴ * g = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hg.1
    simpa [Matrix.star_eq_conjTranspose] using this
  unfold inUJ
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem inG_conj {ε : Fin n → Bool} {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (hX : inG ε X) :
    inG ε (g * X * gᴴ) := by
  have h2 : gᴴ * Jm ε = Jm ε * gᴴ := by
    have := congrArg Matrix.conjTranspose hg.2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_conjTranspose] at this
    exact this.symm
  unfold inG at *
  calc (g * X * gᴴ)ᴴ * Jm ε + Jm ε * (g * X * gᴴ)
      = g * Xᴴ * (gᴴ * Jm ε) + (Jm ε * g) * X * gᴴ := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = g * (Xᴴ * Jm ε + Jm ε * X) * gᴴ := by
        rw [h2, ← hg.2]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX]; simp

theorem exp_conj_mul {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (t : ℂ) :
    NormedSpace.exp (t • (g * X * gᴴ)) * g = g * NormedSpace.exp (t • X) := by
  have h1 : gᴴ * g = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hg
    simpa [Matrix.star_eq_conjTranspose] using this
  have hi : g⁻¹ = gᴴ := Matrix.inv_eq_left_inv h1
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_left_inverse h1)
  have : t • (g * X * gᴴ) = g * (t • X) * g⁻¹ := by
    rw [hi]; simp
  rw [this, Matrix.exp_conj _ _ hu, hi, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem orbit_conj {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsCRepOn (UJset ε) σ) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (hX : inG ε X) (w : H) :
    orbit σ (g * X * gᴴ) (σ g w) = fun t => σ g (orbit σ X w t) := by
  funext t
  have a1 := hσ.2 _ (exp_indefinite_unitary_holds n ε _ (inG_conj hg hX) t) g (kset_inUJ hg)
  have a2 := hσ.2 g (kset_inUJ hg) _ (exp_indefinite_unitary_holds n ε _ hX t)
  rw [exp_conj_mul hg.1, a2] at a1
  exact (congrArg (fun T : H →L[ℂ] H => T w) a1).symm

theorem dAct_conj {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsCRepOn (UJset ε) σ) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) (hX : inG ε X) {w : H}
    (hw : DifferentiableAt ℝ (orbit σ X w) 0) :
    dAct σ (g * X * gᴴ) (σ g w) = σ g (dAct σ X w) := by
  unfold dAct
  rw [orbit_conj hσ hg hX]
  exact (((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hw.hasDerivAt).deriv

theorem dAct_add_smul {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {X : Matrix (Fin n) (Fin n) ℂ}
    {w w' : H} (hw : DifferentiableAt ℝ (orbit σ X w) 0) (hw' : DifferentiableAt ℝ (orbit σ X w') 0)
    (c : ℂ) : dAct σ X (w + c • w') = dAct σ X w + c • dAct σ X w' := by
  have : orbit σ X (w + c • w') = fun t => orbit σ X w t + c • orbit σ X w' t := by
    funext t
    simp [orbit]
  unfold dAct
  rw [this]
  exact (hw.hasDerivAt.fun_add (hw'.hasDerivAt.fun_const_smul c)).deriv

theorem dAct_zero (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin n) (Fin n) ℂ) :
    dAct σ X 0 = 0 := by
  have : orbit σ X 0 = fun _ => 0 := by
    funext t
    simp [orbit]
  unfold dAct
  rw [this]
  simp

theorem lowKSub_stable (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (lowKSub ε lam σ) := by
  intro g hg v hv
  have : lowKSub ε lam σ ≤ (lowKSub ε lam σ).comap (σ g : H →ₗ[ℂ] H) := by
    refine sSup_le fun S hS => ?_
    intro x hx
    exact (le_sSup hS : S ≤ lowKSub ε lam σ) (hS.2.1 g hg x hx)
  exact this hv

theorem dWord_mem {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {P : ℕ} {l : List (Matrix (Fin n) (Fin n) ℂ)} {u : H} (hl : l.length ≤ P) (hX : ∀ X ∈ l, inG ε X)
    (hu : u ∈ lowKSub ε lam σ) : dWord σ l u ∈ stepSpace ε lam σ P :=
  Submodule.subset_span ⟨l, u, hl, hX, hu, rfl⟩

theorem dWord_conj {ε : Fin n → Bool} {lam : Fin n → ℝ} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsCRepOn (UJset ε) σ) (hd : ∀ P, ∀ w ∈ stepSpace ε lam σ P, IsDiffVec ε σ w)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) {u : H} (hu : u ∈ lowKSub ε lam σ)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) (hX : ∀ X ∈ l, inG ε X) :
    σ g (dWord σ l u) = dWord σ (l.map fun X => g * X * gᴴ) (σ g u) := by
  induction l with
  | nil => rfl
  | cons Y l ih =>
    have hl : ∀ X ∈ l, inG ε X := fun X h => hX X (List.mem_cons_of_mem _ h)
    have hY : inG ε Y := hX Y List.mem_cons_self
    change σ g (dAct σ Y (dWord σ l u)) =
      dAct σ (g * Y * gᴴ) (dWord σ (l.map fun X => g * X * gᴴ) (σ g u))
    rw [← ih hl, dAct_conj hσ hg hY (hd _ _ (dWord_mem le_rfl hl hu) Y hY)]

end GlobalTheory.StepLoc
end
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem invVol_pi_univ : ∀ {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (K U : ∀ i, Subgroup (G i)),
    {i | K i ≠ U i}.Finite → (∀ i, (K i).relIndex (U i) ≠ 0 ∧ (U i).relIndex (K i) ≠ 0) →
    (Subgroup.pi Set.univ K).relIndex (Subgroup.pi Set.univ U) ≠ 0 ∧
    (Subgroup.pi Set.univ U).relIndex (Subgroup.pi Set.univ K) ≠ 0 ∧
    invVol (Subgroup.pi Set.univ K) (Subgroup.pi Set.univ U) = ∏ᶠ i, invVol (K i) (U i) := by
  intro ι G _ K U hfin hne
  classical
  set S := hfin.toFinset with hSdef
  have hoff : ∀ i, i ∉ S → K i = U i := by
    intro i hi
    by_contra h
    exact hi (hfin.mem_toFinset.2 h)
  have key : ∀ A B : ∀ i, Subgroup (G i), (∀ i, i ∉ S → A i ≤ B i) →
      (Subgroup.pi Set.univ B).relIndex (Subgroup.pi Set.univ A) =
        ∏ i ∈ S, (B i).relIndex (A i) := by
    intro A B hAB
    exact GlobalTheory.relIndex_eq_prod_local (∀ i, G i) ι G (fun i => Pi.evalMonoidHom G i) ⊤
      (Subgroup.pi Set.univ A) (Subgroup.pi Set.univ B) A B S
      (fun v h _ => ⟨Pi.mulSingle v h, Subgroup.mem_top _, by simp,
        fun w hw => by simp [Pi.mulSingle_eq_of_ne hw]⟩)
      (fun g => by simp [Subgroup.mem_pi])
      (fun g => by simp [Subgroup.mem_pi])
      hAB
  have h1 := key K U (fun i hi => (hoff i hi).le)
  have h2 := key U K (fun i hi => (hoff i hi).ge)
  have hfp : ∀ f : ι → ℝ, (∀ i, i ∉ S → f i = 1) → ∏ᶠ i, f i = ∏ i ∈ S, f i := fun f hf =>
    finprod_eq_prod_of_mulSupport_subset f (fun i hi => by
      by_contra h
      exact hi (hf i h))
  refine ⟨?_, ?_, ?_⟩
  · rw [h2]; exact Finset.prod_ne_zero_iff.2 (fun i _ => (hne i).1)
  · rw [h1]; exact Finset.prod_ne_zero_iff.2 (fun i _ => (hne i).2)
  · rw [hfp _ (fun i hi => by simp [invVol, hoff i hi, Subgroup.relIndex_self])]
    simp only [invVol, h1, h2, Nat.cast_prod]
    rw [Finset.prod_div_distrib]

end GlobalTheory.HL
end

section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.GenusOrb

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]


open NumberField Matrix in
open scoped ENNReal Classical in
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] in
theorem _root_.GlobalTheory.Mass.GenusOrb.trace_pos_of_PD (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hp : _root_.GlobalTheory.Mass.PD h) (x : V) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (h x x) := by
  have hp' : ∀ (τ : K →+* ℂ) (x : V), x ≠ 0 → 0 < (τ ((h x) x)).re := hp
  have hsum := trace_eq_sum_embeddings ℂ (K := ℚ) (L := K) (x := h x x)
  have hre : (algebraMap ℚ ℂ (Algebra.trace ℚ K (h x x))).re =
      (Algebra.trace ℚ K (h x x) : ℝ) := by simp
  have hpos : (0 : ℝ) < (Algebra.trace ℚ K (h x x) : ℝ) := by
    rw [← hre, hsum, Complex.re_sum]
    obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
    haveI : Nonempty (K →ₐ[ℚ] ℂ) := ⟨φ.toRatAlgHom⟩
    exact Finset.sum_pos (fun σ _ => hp' σ.toRingHom x hx) Finset.univ_nonempty
  exact_mod_cast hpos

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def autEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) :
    Formalism.ThetaLiftIndependence.autL h M ≃ MulAction.stabilizer (isom h) M where
  toFun g := ⟨⟨g.1, g.2.1⟩, g.2.2⟩
  invFun g := ⟨g.1.1, g.1.2, g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end


open NumberField Matrix in
open scoped ENNReal Classical in
theorem _root_.GlobalTheory.Mass.GenusOrb.main : ∀ (K V : Type) [Field K] [NumberField K]
    [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm →
    _root_.GlobalTheory.Mass.PD h → ∀ L : Submodule (𝓞 K) V, Submodule.IsFullLattice K L →
    ENNReal.ofReal (_root_.Formalism.HermitianLatticesTheory.mass h L) = _root_.GlobalTheory.Mass.orbMass (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) ∧
    0 < _root_.Formalism.HermitianLatticesTheory.mass h L ∧ _root_.GlobalTheory.Mass.Stable (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) ∧
    (∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M →
      Finite (MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) M)) ∧
    ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞), _root_.Formalism.ThetaLiftIndependence.IsClassReps h L s →
      (∀ (g : _root_.Formalism.HermitianLatticesTheory.isom h) M, N (g • M) = N M) →
      ∑ M ∈ s, ENNReal.ofReal ((Nat.card (_root_.Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M =
        _root_.GlobalTheory.Mass.orbSum (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) N := by
  intro K V _ _ _ _ _ _ _ _ h _ hsymm hp L hL
  have htr : ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) :=
    _root_.GlobalTheory.Mass.GenusOrb.trace_pos_of_PD h hp
  have hmass := by
    first
    | exact _root_.Formalism.HermitianLatticesTheory.final_massBasic K V h hsymm htr L hL
    | exact _root_.Formalism.HermitianLatticesTheory.final_massBasic K V h hsymm htr L hL.toIsLattice
  obtain ⟨hmass_ex, hmass_eq, hmass_pos⟩ := hmass
  have hgen : ∀ g ∈ _root_.Formalism.HermitianLatticesTheory.isom h, ∀ M ∈ _root_.Formalism.HermitianLatticesTheory.genus h L, _root_.Formalism.HermitianLatticesTheory.gmap g M ∈ _root_.Formalism.HermitianLatticesTheory.genus h L := by
    intro g hg M hM
    obtain ⟨hML, hLM⟩ := hM
    obtain ⟨heq, hinv, -⟩ := _root_.Formalism.HermitianLatticesTheory.final_genusBasic (𝓞 K) K V h hsymm _root_.Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
    have hfull : Submodule.IsFullLattice K (_root_.Formalism.HermitianLatticesTheory.gmap g M) := by
      refine { toIsLattice := (_root_.Formalism.HermitianLatticesTheory.final_isomAct (𝓞 K) K V h g hg M).2.2.2.2.mpr hML.toIsLattice, span_eq_top := ?_ }
      have he : ((_root_.Formalism.HermitianLatticesTheory.gmap g M : Submodule (𝓞 K) V) : Set V) = g '' (M : Set V) := by
        ext x
        simp [_root_.Formalism.HermitianLatticesTheory.gmap]
      rw [he]
      change Submodule.span K ((g : V →ₗ[K] V) '' (M : Set V)) = ⊤
      rw [← Submodule.map_span, hML.span_eq_top, Submodule.map_top]
      exact LinearMap.range_eq_top.mpr g.surjective
    exact show Submodule.IsFullLattice K (_root_.Formalism.HermitianLatticesTheory.gmap g M) ∧ _root_.Formalism.HermitianLatticesTheory.SameGenus h L (_root_.Formalism.HermitianLatticesTheory.gmap g M) from
      ⟨hfull, heq.trans hLM (hinv M g hg)⟩
  have hstab : _root_.GlobalTheory.Mass.Stable (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) := fun g M hM => hgen g.1 g.2 M hM
  have hfin : ∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M →
      Finite (MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) M) := by
    intro M hM
    have hS := _root_.Formalism.HermitianLatticesTheory.final_autFinite K V h hsymm htr M hM
    haveI := hS.to_subtype
    refine Finite.of_injective (fun g : MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) M =>
      (⟨g.1.1, g.1.2, g.2⟩ : {g | g ∈ _root_.Formalism.HermitianLatticesTheory.isom h ∧ _root_.Formalism.HermitianLatticesTheory.gmap g M = M})) ?_
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have hsum : ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞),
      _root_.Formalism.ThetaLiftIndependence.IsClassReps h L s → (∀ (g : _root_.Formalism.HermitianLatticesTheory.isom h) M, N (g • M) = N M) →
      ∑ M ∈ s, ENNReal.ofReal ((Nat.card (_root_.Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M =
        _root_.GlobalTheory.Mass.orbSum (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) N := by
    intro s N hs hN
    obtain ⟨hsub, huniq⟩ := hs
    rw [_root_.GlobalTheory.Mass.orbSum_eq_sum_reps (_root_.Formalism.HermitianLatticesTheory.isom h) _ _ N hstab hN s hsub ?_]
    · refine Finset.sum_congr rfl fun M hM => ?_
      congr 1
      obtain ⟨hMlat, -⟩ := hsub M hM
      haveI := hfin M hMlat
      haveI : Finite (_root_.Formalism.ThetaLiftIndependence.autL h M) :=
        Finite.of_equiv _ (_root_.GlobalTheory.Mass.GenusOrb.autEquiv h M).symm
      haveI : Nonempty (_root_.Formalism.ThetaLiftIndependence.autL h M) := ⟨(_root_.GlobalTheory.Mass.GenusOrb.autEquiv h M).symm 1⟩
      have hpos : (0 : ℝ) < (Nat.card (_root_.Formalism.ThetaLiftIndependence.autL h M) : ℝ) := by exact_mod_cast Nat.card_pos
      rw [← ENat.card_congr (_root_.GlobalTheory.Mass.GenusOrb.autEquiv h M), ENat.card_eq_coe_natCard,
        ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_natCast]
      norm_cast
    · intro M hM
      obtain ⟨y, ⟨hy, g, hg, hgy⟩, huy⟩ := huniq M hM
      exact ⟨y, ⟨hy, ⟨g, hg⟩, hgy⟩, fun z ⟨hz, g', hg'⟩ => huy z ⟨hz, g'.1, g'.2, hg'⟩⟩
  obtain ⟨s, hs⟩ := hmass_ex
  have h1 : ENNReal.ofReal (_root_.Formalism.HermitianLatticesTheory.mass h L) = _root_.GlobalTheory.Mass.orbMass (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) := by
    rw [hmass_eq s hs, ENNReal.ofReal_sum_of_nonneg (fun M _ => by positivity)]
    have := hsum s (fun _ => 1) hs (fun _ _ => rfl)
    simp only [mul_one] at this
    rw [this]
    rfl
  exact ⟨h1, hmass_pos, hstab, hfin, hsum⟩

end GlobalTheory.Mass.GenusOrb
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem GlobalTheory.St.G.mem_hat_iff_forall_loc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ x : Fin n → E ⊗[F] Ad F, x ∈ hat F L ↔ ∀ v : HeightOneSpectrum (𝓞 F), prVec v x ∈ loc v L := by
  intro F E _ _ _ _ _ n L hL x
  haveI := hL.1
  exact GlobalTheory.LatticeStabLocal.mem_latS_adele_iff L x
end

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cmField_splitCompletely_place_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (p : ℕ), p.Prime → SplitsIn E p → ({v : HeightOneSpectrum (𝓞 F) | (p : 𝓞 F) ∈ v.asIdeal}.ncard = Module.finrank ℚ F) ∧ ∀ (v : HeightOneSpectrum (𝓞 F)), (p : 𝓞 F) ∈ v.asIdeal → Nat.card (kv F v) = p ∧ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {(p : v.adicCompletionIntegers F)} ∧ ∃ sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F, (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) ∧ ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a) := by
  first | exact @GlobalTheory.St.G.SplitPrime.split_place | exact GlobalTheory.St.G.SplitPrime.split_place | (intros; apply GlobalTheory.St.G.SplitPrime.split_place <;> assumption)
end

section

open GlobalTheory.Diag.PG

theorem _root_.GlobalTheory.T.globalRankNumberBounds_rootDiscriminant_clauses : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → C * (m * (lrd - Real.log 2)) ≤ k ∧ C * (m ^ 3 * x ^ eps * lrd) ≤ k * Real.log k ^ 2 ∧ lrd ≤ x ^ eps / C := by
  first | exact @GlobalTheory.Diag.PG.rankNums_rootDisc | exact GlobalTheory.Diag.PG.rankNums_rootDisc | (intros; apply GlobalTheory.Diag.PG.rankNums_rootDisc <;> assumption)
end
