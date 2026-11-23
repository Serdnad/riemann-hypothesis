module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle768
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestKTypesJointShapeBlockUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle781
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle782
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle149
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle275
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle199
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle001
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions.TH Matrix
open scoped InnerProductSpace

namespace GlobalTheory.RealPartAdjointAction

variable {r s : ℕ}

theorem J_ct : (Jm r s)ᴴ = Jm r s := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem J_sq : Jm r s * Jm r s = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem J_J (X : Mat r s) : Jm r s * (Jm r s * X) = X := by
  rw [← Matrix.mul_assoc, J_sq, Matrix.one_mul]

def reP (Z : Mat r s) : Mat r s := (1 / 2 : ℂ) • (Z - adjZ Z)

def imaginary (Z : Mat r s) : Mat r s := (-Complex.I / 2 : ℂ) • (Z + adjZ Z)

theorem adj_ct_J (Z : Mat r s) : (adjZ Z)ᴴ * Jm r s = Jm r s * Z := by
  simp only [adjZ, Matrix.conjTranspose_mul, J_ct, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, J_sq,
    Matrix.mul_one]

theorem J_adj (Z : Mat r s) : Jm r s * adjZ Z = Zᴴ * Jm r s := by
  simp only [adjZ, Matrix.mul_assoc, J_J]

theorem adj_adj (Z : Mat r s) : adjZ (adjZ Z) = Z := by
  have h : adjZ (adjZ Z) = Jm r s * ((adjZ Z)ᴴ * Jm r s) := Matrix.mul_assoc _ _ _
  rw [h, adj_ct_J, J_J]

theorem realPart_mem_unitaryLieAlgebra (Z : Mat r s) : reP Z ∈ upq r s := by
  have h : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [upq, reP, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, adj_ct_J, J_adj, h]
  module

theorem imaginaryPart_mem_unitaryLieAlgebra (Z : Mat r s) : imaginary Z ∈ upq r s := by
  have h : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by simp
  simp only [upq, imaginary, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, adj_ct_J, J_adj, h]
  module

theorem re_add_im (Z : Mat r s) : reP Z + Complex.I • imaginary Z = Z := by
  have h : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I, neg_neg]
  rw [reP, imaginary, smul_smul, h]
  module

theorem realPart_adjoint (Z : Mat r s) : reP (adjZ Z) = (-1 : ℝ) • reP Z := by
  rw [reP, reP, adj_adj, neg_one_smul, ← smul_neg, neg_sub]

theorem imaginaryPart_adjoint (Z : Mat r s) : imaginary (adjZ Z) = imaginary Z := by
  rw [imaginary, imaginary, adj_adj, add_comm]

section Main

variable {W U I : Type} [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  (a : Mat r s →ₗ[ℂ] Module.End ℂ W) (b : Mat r s → Module.End ℂ U) (j : I → W →ₗ[ℂ] U)

def cx (Z : Mat r s) : Module.End ℂ U := b (reP Z) + Complex.I • b (imaginary Z)

def Sp : Submodule ℂ U := Submodule.span ℂ {y : U | ∃ (i : I) (P : W), y = j i P}

def jS (i : I) : W →ₗ[ℂ] Sp j := (j i).codRestrict (Sp j) fun P => Submodule.subset_span ⟨i, P, rfl⟩

theorem gen (K : Submodule ℂ (Sp j)) (h : ∀ i P, jS j i P ∈ K) (y : Sp j) : y ∈ K := by
  obtain ⟨y, hy⟩ := y
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, P, rfl⟩ := hx
    exact h i P
  | zero => exact K.zero_mem
  | add x y hx hy ihx ihy => exact K.add_mem ihx ihy
  | smul c x hx ih => exact K.smul_mem c ih

theorem ext_gen {N : Type} [AddCommGroup N] [Module ℂ N] (f g : Sp j →ₗ[ℂ] N)
    (h : ∀ i P, f (jS j i P) = g (jS j i P)) : f = g :=
  LinearMap.ext fun y => gen j (LinearMap.eqLocus f g) h y

def Eqv : Prop := ∀ i, ∀ Z ∈ upq r s, ∀ P, j i (a Z P) = b Z (j i P)

variable {a b j}

theorem cx_gen (h : Eqv a b j) (Z : Mat r s) (i : I) (P : W) : cx b Z (j i P) = j i (a Z P) := by
  conv_rhs => rw [← re_add_im Z]
  simp only [cx, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, h i _ (realPart_mem_unitaryLieAlgebra Z), h i _ (imaginaryPart_mem_unitaryLieAlgebra Z)]

theorem stab (f : Module.End ℂ U) (Z : Mat r s) (hf : ∀ i P, f (j i P) = j i (a Z P)) :
    ∀ y ∈ Sp j, f y ∈ Sp j := by
  have : Sp j ≤ (Sp j).comap f := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, P, rfl⟩
    show f (j i P) ∈ Sp j
    rw [hf]
    exact Submodule.subset_span ⟨i, _, rfl⟩
  exact fun y hy => this hy

def op (h : Eqv a b j) (Z : Mat r s) : Module.End ℂ (Sp j) := (cx b Z).restrict (stab _ Z (cx_gen h Z))

theorem op_gen (h : Eqv a b j) (Z : Mat r s) (i : I) (P : W) : op h Z (jS j i P) = jS j i (a Z P) :=
  Subtype.ext (cx_gen h Z i P)

def act (h : Eqv a b j) : Mat r s →ₗ[ℂ] Module.End ℂ (Sp j) where
  toFun := op h
  map_add' X Y := ext_gen j _ _ fun i P => by
    simp only [LinearMap.add_apply, op_gen, map_add (f := _)]
  map_smul' c X := ext_gen j _ _ fun i P => by
    simp only [LinearMap.smul_apply, op_gen, map_smul, RingHom.id_apply]

theorem act_gen (h : Eqv a b j) (Z : Mat r s) (i : I) (P : W) : act h Z (jS j i P) = jS j i (a Z P) :=
  op_gen h Z i P

def finPart {V : Type} [AddCommGroup V] [Module ℂ V] (c : Mat r s →ₗ[ℂ] Module.End ℂ V) : Submodule ℂ V where
  carrier := {v | ∃ F : Submodule ℂ V, FiniteDimensional ℂ F ∧ v ∈ F ∧ KStable c F}
  zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, fun X _ w hw => by
    rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _⟩
  add_mem' := by
    rintro x y ⟨F, hF, hx, kF⟩ ⟨G, hG, hy, kG⟩
    refine ⟨F ⊔ G, inferInstance, Submodule.add_mem_sup hx hy, fun X hX w hw => ?_⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (kF X hX u hu) (kG X hX v hv)
  smul_mem' := by
    rintro t x ⟨F, hF, hx, kF⟩
    exact ⟨F, hF, F.smul_mem t hx, kF⟩

def spanMod (ha : GlobalTheory.ArchRec.IsGK a) (h : Eqv a b j) : GKMod r s where
  V := Sp j
  act := act h
  lie X Y := ext_gen j _ _ fun i P => by
    simp only [act_gen, ha.1 X Y, LinearMap.sub_apply, Module.End.mul_apply, map_sub (jS j i)]
  kfin := gen j (finPart (act h)) fun i P => by
    obtain ⟨F, hF, hP, kF⟩ := ha.2.1 P
    refine ⟨F.map (jS j i), inferInstance, Submodule.mem_map_of_mem hP, ?_⟩
    rintro X hX _ ⟨w, hw, rfl⟩
    rw [act_gen]
    exact Submodule.mem_map_of_mem (kF X hX w hw)
  wts := gen j _ fun i P => by
    have hle : (⨆ μ : Ix r s → ℚ, wtSub a μ) ≤ (⨆ μ : Ix r s → ℚ, wtSub (act h) μ).comap (jS j i) := by
      refine iSup_le fun μ w hw => Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hw ⊢
      intro c
      rw [act_gen, ← map_smul, ← map_sub, hw c, map_zero]
    exact hle (ha.2.2 P)

theorem cx_adj (hb : GlobalTheory.ArchRec.IsUAct b) (Z : Mat r s) (x y : U) :
    ⟪cx b Z x, y⟫_ℂ = ⟪x, cx b (adjZ Z) y⟫_ℂ := by
  simp only [cx, realPart_adjoint, imaginaryPart_adjoint, hb.smul _ _ (realPart_mem_unitaryLieAlgebra Z), LinearMap.add_apply, LinearMap.smul_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hb.skew _ (realPart_mem_unitaryLieAlgebra Z),
    hb.skew _ (imaginaryPart_mem_unitaryLieAlgebra Z), Complex.conj_I]
  push_cast
  ring

def spanUMod (ha : GlobalTheory.ArchRec.IsGK a) (hb : GlobalTheory.ArchRec.IsUAct b) (h : Eqv a b j) : UGKMod r s where
  M := spanMod ha h
  ip := innerₛₗ ℂ (E := Sp j)
  herm x y := inner_conj_symm (𝕜 := ℂ) (E := Sp j) y x
  pos x hx := (re_inner_self_pos (𝕜 := ℂ) (E := Sp j)).2 hx
  adj Z x y := cx_adj hb Z (x : Sp j).1 (y : Sp j).1

theorem act_real (h : Eqv a b j) (Z : Mat r s) (hZ : Z ∈ upq r s) (y : Sp j) : (act h Z y : U) = b Z y := by
  have := ext_gen j ((Sp j).subtype ∘ₗ act h Z) (b Z ∘ₗ (Sp j).subtype) fun i P => by
    rw [LinearMap.comp_apply, act_gen]
    exact h i Z hZ P
  exact LinearMap.congr_fun this y

end Main

theorem main : ∀ (r s : ℕ) (W U I : Type) [inst : AddCommGroup W] [inst_1 : Module ℂ W] [inst_2 : NormedAddCommGroup U] [inst_3 : InnerProductSpace ℂ U] (a : Formalism.BasicNotions.TH.Mat r s →ₗ[ℂ] Module.End ℂ W) (b : Formalism.BasicNotions.TH.Mat r s → Module.End ℂ U) (j : I → W →ₗ[ℂ] U), GlobalTheory.ArchRec.IsGK a → GlobalTheory.ArchRec.IsUAct b → (∀ (i : I), ∀ Z ∈ Formalism.BasicNotions.TH.upq r s, ∀ (P : W), (j i : W → U) (((a : Formalism.BasicNotions.TH.Mat r s → Module.End ℂ W) Z : W → W) P) = (b Z : U → U) ((j i : W → U) P)) → ∃ (MM : Formalism.BasicNotions.TH.UGKMod r s) (inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) →ₗ[ℂ] U), Function.Injective (⇑inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → U) ∧ LinearMap.range inc = Submodule.span ℂ {y : U | ∃ (i : I) (P : W), y = (j i : W → U) P} ∧ ∀ Z ∈ Formalism.BasicNotions.TH.upq r s, ∀ (y : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM)), (inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → U) (((Formalism.BasicNotions.TH.GKMod.act (Formalism.BasicNotions.TH.UGKMod.M MM) : Formalism.BasicNotions.TH.Mat r s → Module.End ℂ (Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM))) Z : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM)) y) = (b Z : U → U) ((inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → U) y) := by
  intro r s W U I _ _ _ _ a b j ha hb h
  exact ⟨spanUMod ha hb h, (Sp j).subtype, (Sp j).injective_subtype, (Sp j).range_subtype,
    fun Z hZ y => act_real h Z hZ y⟩

end GlobalTheory.RealPartAdjointAction

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.LowerTower

open GlobalTheory.SmallerSource GlobalTheory.FockAlg

theorem lamA_mem (al be ga de : List ℚ) (a : Ix (al.length + be.length) (ga.length + de.length)) :
    lamA al be ga de a ∈ al ++ be ++ ga ++ de := by
  rw [List.append_assoc (al ++ be)]
  cases a with
  | inl i => exact List.mem_append_left _ (GlobalTheory.LowestTypes.getD_mem (List.length_append) i)
  | inr j => exact List.mem_append_right _ (GlobalTheory.LowestTypes.getD_mem (List.length_append) j)

theorem tensNo_first (X : ProvA) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hpq : 1 ≤ p + q) (lam : Ix p q → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair r s) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair r s) (blattner lam) a ≤ 0))
    (hno : ∀ μ', ¬ JointShape p q r s (blattner lam) μ') :
    TensNo (fockAct1 p q r s) (fockAct2 p q r s) (X.ds p q lam) := by
  intro MM f hf
  by_contra hne
  obtain ⟨hadm, hirr⟩ := discrete_series_gk_admissible_irreducible X h5 hpq lam
  obtain ⟨hone, -, hcone⟩ := hD p q lam hlam
  have hex : ∃ v, IsHW (X.ds p q lam).HK.act (blattner lam) v := by
    have hnb : hwSub (X.ds p q lam).HK.act (blattner lam) ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hone
      exact zero_ne_one hone
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnb
    exact ⟨v, hv0, hv⟩
  have hflow := GlobalTheory.T.degW_blattner_le_of_blattnerCone p q (X.ds p q lam).HK lam (cPair r s) θ hcone hsign
  obtain ⟨⟨μ, P, hPJ, hP1, hP2, -⟩, -⟩ :=
    GlobalTheory.T.exists_jointHarm_highestWeight_and_map_mem_genSub p q r s (X.ds p q lam).HK MM f hirr hadm hf hne (blattner lam) hex hflow
  have hbot := ((GlobalTheory.JointHarm.fock_polynomials X p q r s).2.2.2.2.1 (blattner lam) μ).2 (hno μ)
  have hmem : P ∈ hwSub (X.fock p q r s).act1 (blattner lam) ⊓ hwSub (X.fock p q r s).act2 μ ⊓
      Submodule.span ℂ (X.fock p q r s).J :=
    ⟨⟨hP1.2, hP2.2⟩, Submodule.subset_span hPJ⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hP1.1 hmem

theorem tensNo_second (X : ProvA) (hD : DiscreteSeriesBlattner X) (h5 : admQ5 X)
    {p q r s : ℕ} (hrs : 1 ≤ r + s) (lam : Ix r s → ℚ) (hlam : IsParam lam) (θ : ℚ)
    (hsign : ∀ a, (θ < lam a → 0 ≤ shiftNu (cPair p q) (blattner lam) a) ∧
      (lam a ≤ θ → shiftNu (cPair p q) (blattner lam) a ≤ 0))
    (hno : ∀ μ, ¬ JointShape p q r s μ (blattner lam)) :
    TensNo (fockAct2 p q r s) (fockAct1 p q r s) (X.ds r s lam) := by
  intro MM f hf
  set c := TensorProduct.comm ℂ (X.ds r s lam).HK.V MM.V with hc
  have hcm : ∀ (A : Module.End ℂ (X.ds r s lam).HK.V) (B : Module.End ℂ MM.V) x,
      c (TensorProduct.map A B x) = TensorProduct.map B A (c x) := by
    intro A B x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hc]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hg : IsIntw (X.fock p q r s) MM (X.ds r s lam).HK ((c : _ →ₗ[ℂ] _) ∘ₗ f) := by
    refine ⟨fun Z => LinearMap.ext fun P => ?_, fun Z => LinearMap.ext fun P => ?_⟩
    · have := LinearMap.congr_fun (hf.2 Z) P
      simp only [LinearMap.comp_apply] at this
      change c (f (fockAct1 p q r s Z P)) = TensorProduct.map _ _ (c (f P))
      rw [this, hcm]
    · have := LinearMap.congr_fun (hf.1 Z) P
      simp only [LinearMap.comp_apply] at this
      change c (f (fockAct2 p q r s Z P)) = TensorProduct.map _ _ (c (f P))
      rw [this, hcm]
  have h0 := intw_eq_zero X (GlobalTheory.JointHarm.fock_polynomials X) hD h5 hrs lam hlam θ hsign hno MM _ hg
  refine LinearMap.ext fun P => ?_
  have : c (f P) = 0 := LinearMap.congr_fun h0 P
  exact c.map_eq_zero_iff.1 this

theorem no_map_lower : ∀ (X : ProvA), DiscreteSeriesBlattner X → admQ5 X → ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → ∀ i : ℕ, 1 ≤ i → (i ≤ al.length + de.length + t → i ≤ ga.length + be.length → TensNo (fockAct1 _ _ (al.length + de.length + t - i) (ga.length + be.length - i)) (fockAct2 _ _ _ _) (X.ds _ _ (lamA al be ga de))) ∧ ((∀ x ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |x|) → i ≤ al.length + be.length → i ≤ ga.length + de.length → TensNo (fockAct2 (al.length + be.length - i) (ga.length + de.length - i) _ _) (fockAct1 _ _ _ _) (X.ds _ _ (lamA' t al be ga de))) := by
  intro X hD h5 t al be ga de hA i hi
  have ht : 1 ≤ t := hA.1
  have hn : 1 ≤ al.length + be.length + ga.length + de.length := hA.2.1
  have ht0 : (0 : ℚ) ≤ t := Nat.cast_nonneg t
  obtain ⟨-, hpar, hpar', hsign, hsign'⟩ := GlobalTheory.T.lowest_kTypes_jointShape_block_unitary t al be ga de hA
  obtain ⟨hno, -, hno'⟩ := GlobalTheory.T.lowestType_not_jointShape_smaller_pairs t al be ga de hA i hi
  refine ⟨fun hr hs => ?_, fun hbig hp hq => ?_⟩
  · refine tensNo_first X hD h5 (by omega) _ hpar 0 ?_ (hno hr hs)
    rw [cPair_sub hr hs]
    refine fun a => ⟨(hsign a).1, fun h => (hsign a).2 (lt_of_le_of_ne h fun h0 => ?_)⟩
    have := hA.2.2.2.2.2.2.2.2.2.2 _ (lamA_mem al be ga de a)
    rw [h0, abs_zero] at this
    linarith
  · refine tensNo_second X hD h5 (by omega) _ hpar' ((t : ℚ) / 2) ?_ (hno' (.inl ?_) hp hq).1
    · rw [cPair_sub hp hq]
      exact hsign'
    · rintro ⟨a, ha⟩
      have := hbig _ (lamA_mem al be ga de a)
      rw [ha, abs_of_nonneg (by positivity)] at this
      linarith

end GlobalTheory.LowerTower
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec

theorem haar_of_proper {p q n : ℕ} (T : GrpData p q) (ε : Fin n → Bool) (μ : Measure (Formalism.REAL.UJ ε))
    [μ.IsHaarMeasure] (π : T.G →* Formalism.REAL.UJ ε) (hp : IsProperMap π) (hs : Function.Surjective π) :
    ∃ c : NNReal, c ≠ 0 ∧ Topology.IsQuotientMap π ∧ Measurable π ∧ Measure.map π T.haar = c • μ := by
  have hc : Continuous π := hp.continuous
  have ht : Filter.Tendsto π (Filter.cocompact T.G) (Filter.cocompact (Formalism.REAL.UJ ε)) := by
    refine Filter.hasBasis_cocompact.tendsto_right_iff.2 fun K hK => ?_
    have hK' : IsCompact (π ⁻¹' K) := hp.isCompact_preimage hK
    exact hK'.compl_mem_cocompact
  haveI hν : (Measure.map π T.haar).IsHaarMeasure := Measure.isHaarMeasure_map T.haar π hc hs ht
  refine ⟨Measure.haarScalarFactor (Measure.map π T.haar) μ,
    (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne', hp.isClosedMap.isQuotientMap hc hs,
    hc.measurable, ?_⟩
  exact Measure.isMulLeftInvariant_eq_smul _ μ


open GlobalTheory.RealPar.SqInt (reixHom continuous_reixHom) in
noncomputable def reixUJ {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) :
    Formalism.UG.Upq p q ≃ₜ* Formalism.REAL.UJ ε where
  toFun g := ⟨Units.map (reixHom e) g.1, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat_mem h g.2⟩
  invFun g := ⟨Units.map (reixHom e.symm) g.1, by
    have hg : (umat g)ᴴ * Formalism.REAL.Jm ε * umat g = Formalism.REAL.Jm ε := g.2
    change (Matrix.reindex e.symm e.symm (umat g))ᴴ * Formalism.UG.Jpq p q * Matrix.reindex e.symm e.symm (umat g) =
      Formalism.UG.Jpq p q
    have hJ : Formalism.UG.Jpq p q = Matrix.reindex e.symm e.symm (Formalism.REAL.Jm ε) := by
      rw [← GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.reindex_form h]; simp
    rw [hJ]
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hg]⟩
  left_inv g := Subtype.ext (Units.ext (by
    change Matrix.reindex e.symm e.symm (Matrix.reindex e e _) = _
    simp))
  right_inv g := Subtype.ext (Units.ext (by
    change Matrix.reindex e e (Matrix.reindex e.symm e.symm _) = _
    simp))
  map_mul' a b := Subtype.ext (map_mul (Units.map (reixHom e)) a.1 b.1)
  continuous_toFun := Continuous.subtype_mk (((continuous_reixHom e).units_map _).comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (((continuous_reixHom e.symm).units_map _).comp continuous_subtype_val) _

theorem cover_haar_map : ∀ (p q n : ℕ) (T : GrpData p q) (ε : Fin n → Bool) (e : Ix p q ≃ Fin n) (br : Bool) (μ : Measure (Formalism.REAL.UJ ε)), SignCompat ε e → μ.IsHaarMeasure → ∃ (π : T.G →* Formalism.REAL.UJ ε) (c : NNReal), c ≠ 0 ∧ (∀ g, umat (π g) = phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) ∧ Topology.IsQuotientMap π ∧ Measurable π ∧ Measure.map π T.haar = c • μ := by
  intro p q n T ε e br μ h hμ
  obtain ⟨C, hC, -⟩ := GlobalTheory.LeviIso.exists_conj_gauge_invariant n ε
    (if br then starRingEnd ℂ else RingHom.id ℂ) (by cases br <;> simp)
  let π : T.G →* Formalism.REAL.UJ ε :=
    (C.toMonoidHom.comp (reixUJ h).toMonoidHom).comp (GlobalTheory.DetSqrtCover.covHom T)
  have hcov : IsProperMap (GlobalTheory.DetSqrtCover.covHom T) := GlobalTheory.DetSqrtCover.isProperMap_covU T
  have hp : IsProperMap π :=
    (C.toHomeomorph.isProperMap.comp (reixUJ h).toHomeomorph.isProperMap).comp hcov
  have hs : Function.Surjective π :=
    (C.surjective.comp (reixUJ h).surjective).comp (GlobalTheory.DetSqrtCover.surjective_covU T)
  obtain ⟨c, hc0, hq, hm, hmap⟩ := haar_of_proper T ε μ π hp hs
  refine ⟨π, c, hc0, fun g => ?_, hq, hm, hmap⟩
  have hre : umat (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g)) =
      Matrix.reindex e e ((T.cov g : GL (Ix p q) ℂ) : Mat p q) :=
    GlobalTheory.RealPar.SqInt.reixHom_apply e _
  have hconj := hC (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g))
  change umat (C (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g))) = _
  refine hconj.trans ?_
  change (umat (reixUJ h (GlobalTheory.DetSqrtCover.covHom T g))).map _ = _
  rw [hre]
  cases br
  · ext i j
    simp [phi, plainMat]
  · ext i j
    simp [phi, barMat]

end GlobalTheory.ArchRec
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.SumSig

section Change
variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem gram_family (S : HSpace E) {ι : Type} [Fintype ι] (v : ι → S.V) :
    (Matrix.of fun k l => S.hT (v k) (v l)) =
      (Matrix.of fun i k => S.frame.repr (v k) i)ᴴ * S.gram * Matrix.of fun i k => S.frame.repr (v k) i := by
  ext k l
  have hk := S.frame.sum_repr (v k)
  have hl := S.frame.sum_repr (v l)
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, HSpace.gram]
  conv_lhs => rw [← hk, ← hl]

  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply,
  Finset.sum_mul, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end Change

end GlobalTheory.SumSig
end
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.heckeChar_isUnitary_of_unitary_infinityType : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ), χ.HasInf φ n → χ.IsUnitary := by
  first | exact @GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf | exact GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf | (intros; apply GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf <;> assumption)
end
