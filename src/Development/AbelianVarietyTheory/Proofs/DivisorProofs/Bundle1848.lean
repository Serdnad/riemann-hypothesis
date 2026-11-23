module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspLatticeAnyLevel
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.LevelVectorSizeBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle059
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigenSysOfHeckeLin
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle732
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.Bundle003
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.Survey.LevelVectorSizeBounds

namespace GlobalTheory.LowForm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem op_idem {G H : Type} [Group G] [Fintype G] [AddCommGroup H] [Module ℂ H] (ρ : Representation ℂ G H) {a : G → ℂ}
    (ha : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem a) (u : H) :
    (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = (∑ g, a g • ρ g : H →ₗ[ℂ] H) u := by
  set E : H →ₗ[ℂ] H := ∑ g, a g • ρ g with hE
  have h1 : E u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
    simp only [← Finset.sum_smul, ha.2, hE, LinearMap.sum_apply, LinearMap.smul_apply]
  have h2 : E (E u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by

    simp only [hE, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
  refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

theorem adjoint_eq_self {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (E : H →ₗ[ℂ] H)
    (h1 : ∀ u, E (E u) = E u) (h2 : ∀ x, E x = x → ∀ y, ⟪x, E y⟫_ℂ = ⟪x, y⟫_ℂ) : LinearMap.adjoint E = E := by
  refine LinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  rw [LinearMap.adjoint_inner_left, ← h2 _ (h1 x) y, ← inner_conj_symm, ← h2 _ (h1 y) x, inner_conj_symm]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem eC_idem_at (hr : R.grp_record) (σ : D.what₂.LL →+* ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem (RealDat.eC (A := A) σ) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.LiftScalarCompare.eC_idem hr
  unfold RealDat.eC at h1 h2 ⊢
  refine ⟨fun g k => congrArg σ ((sg0 D A).injective (h1 g k)), fun g => ?_⟩
  have := h2 g

  simp only [← map_mul, ← map_sum] at this ⊢
  exact congrArg σ ((sg0 D A).injective this)


open Classical in
variable (R) in
def blkChar (i : Fin D.R.m) : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ :=
  fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR A.μ0 PP

def conjChar (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ :=
  fun PP => (Units.map (s : ℂ →+* ℂ).toMonoidHom).comp (m PP)

theorem twVal_zero {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    twVal χ 0 P k = ((χ.locK P k : ℂˣ) : ℂ) := by
  unfold twVal
  simp

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (r : ℕ) (hr : r ≤ n) (t s' : ℕ) (Pg Q : Finset (Pl D.host.E))
    (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x) :
    ((levFn β ⟨r, hr, t, s', Pg, Q, LevelP.triv _ _ _, fun _ => conjChar s m, conjChar s m⟩ x : ℂˣ) : ℂ) =
      s ((levFn β ⟨r, hr, t, s', Pg, Q, LevelP.triv _ _ _, fun _ => m, m⟩ x : ℂˣ) : ℂ) := by
  unfold levFn
  have e : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  simp only [e, one_mul, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  rfl

theorem chrOf_conj (i : Fin D.R.m) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : levJ R i A.μ0) :
    ((chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv (conjChar s m)) k : ℂˣ) : ℂ) =
      s ((chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) k : ℂˣ) : ℂ) :=
  levFn_conj (R.βV i) D.R.r (r_le_V i) D.R.t 1 R.Pg (R.Q A.μ0) s m (Formalism.UG.bc (Lev.swapAE D) k.1.1)

theorem hookPlus_le (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i (lab σ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i id) : hookPlus D i ≤ mainTerm D i σ := by
  have e : mainTerm D i σ = GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i (lab σ) := by
    unfold mainTerm GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum
    simp only [Nat.cast_mul]
    rfl
  rw [e, h]
  unfold hookPlus GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum
  refine Finset.sum_le_sum fun ρ _ => Real.log_le_log (Nat.cast_pos.2 (hookProd_pos _)) (Nat.cast_le.2 ?_)
  exact Nat.le_mul_of_pos_right _ (hookProd_pos _)

theorem eq_of_low_at (hW : R.models_HW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec} (hv : IsExtVec (R.MW i σ) v)
    {x y : (R.HW i σ).H}
    (h : ∀ w : ∀ ρ, lowT (R.MW i σ) ρ, (R.HW i σ).e x (fun ρ => w ρ) = (R.HW i σ).e y fun ρ => w ρ) : x = y := by
  have h0 : (R.HW i σ).e (x - y) v = 0 := by
    rw [LinearMap.map_sub]
    exact sub_eq_zero.2 (h fun ρ => ⟨v ρ, (hv ρ).2.1⟩)
  have h1 := (hW i σ).2.2 (x - y) (x - y)
  rw [ipAt, GlobalTheory.EvalAtUnitVector.ipM_self_eq_zero _ _ _ _ v (fun τ => (hv τ).1) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

theorem lower_of_parts {X Y ι : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T th : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y)
    (P : ι → Submodule ℂ Y) (S : ι → Prop) (a : ℝ) (h1 : LinearMap.adjoint e = e) (h2 : ∀ y, e (e y) = e y)
    (h3 : (⨆ (k) (_ : S k), P k) = ⊤)
    (h4 : ∀ k, P k ≠ ⊥ → ∃ l : ℝ, 0 < l ∧ (∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) ∧ a ≤ Real.log l)
    (h5 : ∀ x, th x = e (T x)) : ∀ x ∈ (LinearMap.ker th)ᗮ, Real.exp a * ‖x‖ ^ 2 ≤ ‖th x‖ ^ 2 := by
  obtain rfl : th = e ∘ₗ T := LinearMap.ext h5
  refine GlobalTheory.mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts X Y ι T e P _ (Real.exp_pos a) h1 h2 ?_ fun k => ?_
  · exact top_le_iff.1 (h3.ge.trans (iSup₂_le fun k _ => le_iSup P k))
  · by_cases hk : P k = ⊥
    · refine ⟨_, le_rfl, fun y hy => ?_⟩
      rw [hk, Submodule.mem_bot] at hy
      simp [hy]
    · obtain ⟨l, a1, a2, a3⟩ := h4 k hk
      exact ⟨l, (Real.le_log_iff_exp_le a1).1 a3, a2⟩



end GlobalTheory.LowForm

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TransferHyp

theorem stab_iff_entries {R : Type} [CommRing R] {n : ℕ} (O : Subring R) {X Y : Matrix (Fin n) (Fin n) R}
    (hXY : X * Y = 1) (hYX : Y * X = 1) :
    (∀ z : Fin n → R, (∀ i, z i ∈ O) ↔ ∀ i, X.mulVec z i ∈ O) ↔ (∀ i j, X i j ∈ O) ∧ ∀ i j, Y i j ∈ O := by
  have hs : ∀ j i : Fin n, (Pi.single j 1 : Fin n → R) i ∈ O := fun j i => by
    rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hm : ∀ {A : Matrix (Fin n) (Fin n) R}, (∀ i j, A i j ∈ O) → ∀ z : Fin n → R, (∀ i, z i ∈ O) →
      ∀ i, A.mulVec z i ∈ O := fun {A} hA z hz i => by
    change ∑ j, A i j * z j ∈ O
    exact sum_mem fun j _ => mul_mem (hA i j) (hz j)
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using (h _).1 (hs j) i
    · have := (h (Y.mulVec (Pi.single j 1))).2 (by
        rw [Matrix.mulVec_mulVec, hXY, Matrix.one_mulVec]
        exact hs j) i
      simpa using this
  · rintro ⟨h1, h2⟩ z
    refine ⟨hm h1 z, fun hz => ?_⟩
    have := hm h2 _ hz
    rwa [Matrix.mulVec_mulVec, hYX, Matrix.one_mulVec] at this

theorem stab_conj {R : Type} [CommRing R] {n : ℕ} (I Λ : (Fin n → R) → Prop) {A B H G X : Matrix (Fin n) (Fin n) R}
    (hAB : A * B = 1) (hBA : B * A = 1) (hHG : H * G = 1)
    (hΛ : ∀ y, Λ y ↔ I (B.mulVec (H.mulVec y))) :
    (∀ y, Λ y ↔ Λ ((G * (A * X * B) * H).mulVec y)) ↔ ∀ z, I z ↔ I (X.mulVec z) := by
  have key : ∀ y, B.mulVec (H.mulVec ((G * (A * X * B) * H).mulVec y)) = X.mulVec (B.mulVec (H.mulVec y)) := fun y => by
    simp only [Matrix.mulVec_mulVec]
    congr 1
    calc B * (H * (G * (A * X * B) * H)) = B * (H * G) * A * X * (B * H) := by simp only [Matrix.mul_assoc]
      _ = X * (B * H) := by rw [hHG, Matrix.mul_one, hBA, Matrix.one_mul]
  simp only [hΛ, key]
  refine ⟨fun h z => ?_, fun h y => h _⟩
  have e : B.mulVec (H.mulVec (G.mulVec (A.mulVec z))) = z := by
    rw [Matrix.mulVec_mulVec _ H, hHG, Matrix.one_mulVec, Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  have := h (G.mulVec (A.mulVec z))
  rwa [e] at this

theorem finMat_mul {D : D7} (V : HSp D) (g h : GA D V) :
    finMat D.sp.cm.sig V.gram (g * h) = finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram h :=
  congrArg Units.val (map_mul (finHom V) g h)

theorem finMat_one {D : D7} (V : HSp D) : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 :=
  congrArg Units.val (map_one (finHom V))

def finComp (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Ad E →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E :=
  (GlobalTheory.LFun.finAdEquiv F E).symm.toRingHom.comp (pFin E)

def intRing (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Subring (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) :=
  ⨅ u : HeightOneSpectrum (𝓞 E), (Ov E u).comap (GlobalTheory.LFun.compAt F u)

theorem mem_intRing {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) : z ∈ intRing F E ↔ ∀ u, GlobalTheory.LFun.compAt F u z ∈ Ov E u := by
  simp only [intRing, Subring.mem_iInf, Subring.mem_comap]

theorem stab_finComp_iff (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsCMField E] {n : ℕ} (x : UA E n) :
    (∀ z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E, (∀ i, z i ∈ intRing F E) ↔
      ∀ i, (x.1.1.map (finComp F E)).mulVec z i ∈ intRing F E) ↔
    (∀ a b u, (cLoc u x).1 a b ∈ u.adicCompletionIntegers E) ∧
      ∀ a b u, (cLoc u x⁻¹).1 a b ∈ u.adicCompletionIntegers E := by
  have hκ : ∀ (y : UA E n) a b, (y.1.1.map (finComp F E)) a b ∈ intRing F E ↔
      ∀ u, (cLoc u y).1 a b ∈ u.adicCompletionIntegers E := fun y a b => by
    refine (mem_intRing _).trans (forall_congr' fun u => ?_)
    have e : GlobalTheory.LFun.compAt F u ((y.1.1.map (finComp F E)) a b) = (cLoc u y).1 a b :=
      congrArg (fun t => pLoc E u t) ((GlobalTheory.LFun.finAdEquiv F E).apply_symm_apply (pFin E (y.1.1 a b)))
    rw [e]
    exact Iff.rfl
  have hXY : ∀ y : UA E n, y.1.1.map (finComp F E) * (y⁻¹).1.1.map (finComp F E) = 1 := fun y => by
    rw [← Matrix.map_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hYX := hXY x⁻¹
  rw [inv_inv] at hYX
  refine (stab_iff_entries _ (hXY x) hYX).trans ?_
  simp only [hκ]

theorem mem_KGL_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {x : UA E n} (hx : x ∈ locU n P) : cLoc P x ∈ GlobalTheory.LFun.KGL P (n := n) ↔
    (∀ a b u, (cLoc u x).1 a b ∈ u.adicCompletionIntegers E) ∧
      ∀ a b u, (cLoc u x⁻¹).1 a b ∈ u.adicCompletionIntegers E := by
  constructor
  · intro h2
    exact ⟨fun a b u => GlobalTheory.UnramDict.cLoc_entry_mem hx h2 u a b, fun a b u =>
      GlobalTheory.UnramDict.cLoc_entry_mem (inv_mem hx) (by rw [map_inv]; exact inv_mem h2) u a b⟩
  · rintro ⟨h4, h5⟩
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun a b => h4 a b P, fun a b => ?_⟩
    rw [← map_inv]
    exact h5 a b P

theorem map_mul_map_inv {K R : Type} [Field K] [CommRing R] {n : ℕ} (ι : K →+* R) {M N : Matrix (Fin n) (Fin n) K}
    (h : N * M = 1) : M.map ι * M⁻¹.map ι = 1 ∧ M⁻¹.map ι * M.map ι = 1 := by
  have hdet : IsUnit M.det := Matrix.isUnit_det_of_left_inverse h
  constructor
  · rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ ι.map_zero ι.map_one]
  · rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ ι.map_zero ι.map_one]

theorem cj_mem_hyp_iff : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU (E := D.host.E) (n := V.rank) ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ SuppF V f (cj j h₀ x)) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, cj j h₀ x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P := by
  intro D _ V j h₀ M hM _ _ hj hlat hloc P x
  have hO : ∀ z, z ∈ intAE D ↔ z ∈ intRing D.host.F D.host.E := fun z =>
    (GlobalTheory.LFun.mem_intAE_iff_compAt z).trans (mem_intRing z).symm
  obtain ⟨hAB, hBA⟩ := map_mul_map_inv (Algebra.TensorProduct.includeRight :
      D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E).toRingHom hM
  have hHG : finMat D.sp.cm.sig V.gram h₀ * finMat D.sp.cm.sig V.gram h₀⁻¹ = 1 := by
    rw [← finMat_mul, mul_inv_cancel, finMat_one]
  have hst : (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      (finMat D.sp.cm.sig V.gram (cj j h₀ x)).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)) ↔
      (∀ a b u, (cLoc u x).1 a b ∈ u.adicCompletionIntegers D.host.E) ∧
        ∀ a b u, (cLoc u x⁻¹).1 a b ∈ u.adicCompletionIntegers D.host.E := by
    rw [cj_apply, finMat_mul, finMat_mul, hj]
    exact (stab_conj (fun z => ∀ i, z i ∈ intRing D.host.F D.host.E)
      (fun y => y ∈ latHat D.host.F D.host.E (L0c D V)) hAB hBA hHG
      fun y => (hlat y).trans (forall_congr' fun i => hO _)).trans (stab_finComp_iff D.host.F x)
  constructor
  · rintro ⟨⟨h1, h2, -⟩, e, f, hef, h3⟩
    have hx := (hloc P e f hef x).2 ⟨h1, h3⟩
    exact ⟨hx, (mem_KGL_iff hx).2 (hst.1 h2)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨e, f, hef⟩ := GlobalTheory.IdemSupport.exists_isPrimeIdem (GlobalTheory.LFun.comp_finAdEquiv D) P
    obtain ⟨h3, h4⟩ := (hloc P e f hef x).1 h1
    exact ⟨⟨h3, hst.2 ((mem_KGL_iff h1).1 h2), fun v hv => absurd hv (Finset.notMem_empty v)⟩, e, f, hef, h4⟩

end GlobalTheory.TransferHyp

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adelicPureTensor_fixed_by_open_finiteHeisenberg : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
      ∃ M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F))) ∧
        ∀ m ∈ M, ∀ f : (κ → mixedEmbedding.mixedSpace F) → ℂ,
          GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 F m) (GlobalTheory.WeilM.pureA F f g) = GlobalTheory.WeilM.pureA F f g := by
  first | exact @GlobalTheory.WeilAdm.pureA_fixed_fin | exact GlobalTheory.WeilAdm.pureA_fixed_fin | (intros; apply GlobalTheory.WeilAdm.pureA_fixed_fin <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

theorem _root_.GlobalTheory.T.lowerUnipotent_realisedOnAdelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (C : Matrix κ κ F), Cᵀ = C → Realised ψ (Matrix.fromBlocks 1 0 (-C) 1) := by
  first | exact @GlobalTheory.AdelicSvNQuad.realised_unip | exact GlobalTheory.AdelicSvNQuad.realised_unip | (intros; apply GlobalTheory.AdelicSvNQuad.realised_unip <;> assumption)
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.automorphicForm_eq_own_realLieSmoothing : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧ smoothing ν α φ.1 = φ.1 := by
  first | exact @GlobalTheory.AutGrowth.SelfSmoothing.exists_smoothing_eq_self | exact GlobalTheory.AutGrowth.SelfSmoothing.exists_smoothing_eq_self | (intros; apply GlobalTheory.AutGrowth.SelfSmoothing.exists_smoothing_eq_self <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseDatum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def along {K X Z : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Z] [Module ℂ Z] {s s' : K →+* ℂ} (h : s = s')
    (f : X →ₛₗ[s] Z) : X →ₛₗ[s'] Z where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := by rw [← h]; exact f.map_smulₛₗ a x

theorem ext_val {G Γ W K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (hact : ∀ γ, ∃ T : M → M, ∀ v, c₀ (T v) = ρ γ (c₀ v))
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) (f : S.Cl → S.V) (h : G) : ∃ v, P.ext f h = c₀ v := by
  obtain ⟨T, hT⟩ := hact (P.decG h)
  obtain ⟨y, hy⟩ := hχ (P.decK h)
  refine ⟨y • T (e (f (P.decC h))), ?_⟩
  rw [map_smulₛₗ, hT, hy, ← he]
  rfl

theorem pair_val {G Γ W K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (pr : M → M → K) (hp : ∀ x x', pr (e x) (e x') = S.pair x x') (v w : M) :
    inner ℂ (c₀ v) (c₀ w) = σ₀ (pr v w) := by
  have h := P.coef_pair (e.symm v) (e.symm w)
  rw [he, he, ← hp] at h
  simpa only [LinearEquiv.apply_symm_apply] using h

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

include R in
theorem realisation_embedding_eq_baseEmbedding : D.what₂.embLL = sg0 D A := (sgAt_mk _ R.hv0).symm

theorem isEtaConj_base (hL : R.toLevCh.Is A.μ0) (hV : EtaVals R) : IsEtaConj (sg0 D A) R.eta R.eta :=
  ⟨hL.eta.1, GlobalTheory.EtaConjExist.unram_of_chrEq hL.eta R.C.isEta.unr, fun P e he x hx =>
    (hV P e he x hx).imp fun y hy => ⟨hy, (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) y).symm.trans hy⟩⟩


theorem places_base (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2 fun PP hPP =>
    (hL.Q_ram A.μ0 PP).2 (Or.inl hPP) (by rw [hL.xi_base]; exact fun _ _ => rfl)

theorem mu_base (hL : R.toLevCh.Is A.μ0) (j : ℕ) : R.toLevCh.mu A.μ0 j = R.mu0 j := by
  have hxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0))
  exact (congrArg (R.mu0 j * ·) hxi).trans (mul_one _)

theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dite_eq_left (by simp)]
  simp

theorem isThPVecOf_empty {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT ΛS ΛT βS βT}
    {Pg Q : Finset (Pl D.host.E)} (hQ : Q = ∅) {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {f₀ f : WO S T → ℂ} (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) :
    IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ' f₀ f := by
  subst hQ
  unfold IsThPVecOf at h ⊢
  simp only [omegaQ_empty] at h ⊢
  exact h

include R in
theorem deltaConj_base : deltaConj i (sg0 D A) = RealDat.Delta i := by
  have hl : lab (sg0 D A) = id := by
    rw [← realisation_embedding_eq_baseEmbedding R]; exact funext GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base
  unfold deltaConj
  rw [hl]
  rfl


end GlobalTheory.GalLift.BaseDatum

end
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.hermitian_lattice_local_unitary_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (n : ℕ) (Q₁ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), (B₁.P * B₂.P).Separable → B₁.P = Q₁.map e.symm.toRingHom → ∀ (γ : GLw n w) (x : (B₁.prod B₂).Aˣ) (ψ : (B₁.prod B₂).A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel (B₁.prod B₂) (γ.val.map e.symm) x ψ → kapSign n w Q₁ γ = ((K.eta (B₁.gramDet (x : (B₁.prod B₂).A).1) : ℚ) : ℂ) := by
  first | exact @GlobalTheory.InertSign.main | exact GlobalTheory.InertSign.main | (intros; apply GlobalTheory.InertSign.main <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.riemannianLieMeasure_frameBox_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∀ t : ℝ, 0 < t → riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < t} ≤ ENNReal.ofReal ((3 * t) ^ (Ψ.card * (r ^ 2 - 1))) := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.riemLie_frameBox_le | exact GlobalTheory.CovTop.VolUp.FrameBox.riemLie_frameBox_le | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.riemLie_frameBox_le <;> assumption)
end
