module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle320
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle284
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle341
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle007
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle254
public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle323
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedBessel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SymplecticTensorMeasures
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle314
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymFrame

theorem val_mul_nsmul {Q ι : Type} [AddCommGroup Q] [Fintype ι] {g : ℕ} [NeZero g] (β : Q) (hβ : g • β = 0)
    (x y : ι → ZMod g) : (∑ i, x i * y i).val • β = ∑ i, (x i).val • (y i).val • β := by
  have h1 : (∑ i, x i * y i) = ((∑ i, (x i).val * (y i).val : ℕ) : ZMod g) := by
    push_cast
    simp
  rw [h1, ZMod.val_natCast]
  have h2 : ∀ n : ℕ, (n % g) • β = n • β := fun n => by
    conv_rhs => rw [← Nat.mod_add_div n g, add_nsmul, mul_comm, mul_nsmul', hβ, nsmul_zero, add_zero]
  rw [h2, ← Finset.sum_nsmul_assoc]
  simp [mul_smul]

theorem basisChange_quot {Q ι : Type} [AddCommGroup Q] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g] (f : Q →+ Q)
    (β υ : ι → Q) (hβ : ∀ i, g • β i = 0) (M P N : Matrix ι ι (ZMod g)) (hPN : P * N = M * P)
    (hυ : ∀ j, υ j = ∑ i, (P i j).val • β i) (hf : ∀ i, f (β i) = ∑ j, (M j i).val • β j) (j : ι) :
    f (υ j) = ∑ m, (N m j).val • υ m := by
  have e1 : f (υ j) = ∑ l, ((M * P) l j).val • β l := by

    rw [hυ, map_sum]
    simp only [map_nsmul, hf, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  rw [e1, ← hPN]
  simp only [hυ, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, val_mul_nsmul _ (hβ l)]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem basisChange_mod {V ι : Type} [AddCommGroup V] [Fintype ι] [DecidableEq ι] {g : ℕ} [NeZero g]
    (W : AddSubgroup V) (f : V →+ V) (hW : ∀ v ∈ W, f v ∈ W)
    (β υ : ι → V) (hβ : ∀ i, g • β i ∈ W) (M P N : Matrix ι ι (ZMod g)) (hPN : P * N = M * P)
    (hυ : ∀ j, υ j - ∑ i, (P i j).val • β i ∈ W) (hf : ∀ i, f (β i) - ∑ j, (M j i).val • β j ∈ W) (j : ι) :
    f (υ j) - ∑ m, (N m j).val • υ m ∈ W := by
  have key : ∀ a b : V, a - b ∈ W ↔ QuotientAddGroup.mk' W a = QuotientAddGroup.mk' W b := fun a b => by
    rw [← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  have h := basisChange_quot (QuotientAddGroup.map W W f (fun v hv => hW v hv))
    (fun i => QuotientAddGroup.mk' W (β i)) (fun i => QuotientAddGroup.mk' W (υ i))
    (fun i => by rw [← map_nsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; exact hβ i)
    M P N hPN
    (fun j => by
      have := (key _ _).1 (hυ j)

      rw [this, map_sum]; simp only [map_nsmul])
    (fun i => by
      have := (key _ _).1 (hf i)

      rw [map_sum] at this
      simp only [map_nsmul] at this
      rw [← this]; rfl) j

  rw [key, map_sum]
  simp only [map_nsmul]
  rw [← h]; rfl

variable {D : D7} (X : HidaSetting D)

theorem inclE_smul_mem_wLf (w : HeightOneSpectrum (𝓞 D.host.E)) (a : 𝓞 X.B.I.E)
    (ha : ∃ b ∈ w.asIdeal, X.ιE (a : X.B.I.E) = (b : D.host.E)) {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) :
    Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) • y ∈ wLf X w := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hz
    have hm : (a : X.B.I.E) • l ∈ wLat X w := Submodule.subset_span ⟨a, ha, l, hl, rfl⟩
    have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) •
        (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) =
        fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • l) i) := by
      funext i
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
    rw [e]
    exact Submodule.subset_span ⟨⟨_, hm⟩, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem fmat_mulVec_mem_wLf (w : HeightOneSpectrum (𝓞 D.host.E)) {k : X.B.I.Gf} (hk : k ∈ X.B.I.Kset)
    {y : VA X.B.I} (hy : y ∈ wLf X w) : X.B.I.fmat k *ᵥ y ∈ wLf X w := by
  have hz : ∀ z ∈ wLat X w, ∀ c : 𝓞 X.B.I.E, X.B.I.fmat k *ᵥ incl X.B.I (c • z) ∈ wLf X w := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, l, hl, rfl⟩ := hz
      intro c
      have e : incl X.B.I (c • (a : X.B.I.E) • l) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) • incl X.B.I (c • l) := by
        rw [smul_comm]
        funext i
        exact map_mul (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F)) (a : X.B.I.E) ((c • l) i)
      rw [e, Matrix.mulVec_smul]
      refine inclE_smul_mem_wLf X w a ha ((hk _).1 ?_)
      exact Submodule.subset_span ⟨⟨_, X.B.I.L.smul_mem c hl⟩, rfl⟩
    | zero =>
      intro c
      have e : incl X.B.I (c • (0 : Fin X.B.I.n → X.B.I.E)) = 0 := by
        rw [smul_zero]; funext i; simp [incl]
      rw [e, Matrix.mulVec_zero]; exact zero_mem _
    | add a b _ _ ha hb =>
      intro c
      have e : incl X.B.I (c • (a + b)) = incl X.B.I (c • a) + incl X.B.I (c • b) := by
        rw [smul_add]; funext i; simp only [incl, Pi.add_apply, map_add (f := _)]
      rw [e, Matrix.mulVec_add]; exact add_mem (ha c) (hb c)
    | smul d a _ ha =>
      intro c
      rw [smul_smul]; exact ha _
  induction hy using Submodule.span_induction with
  | mem z h =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := h
    have := hz l hl 1
    rw [one_smul] at this
    exact this
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha =>
    have e : X.B.I.fmat k *ᵥ (c • a) = c • (X.B.I.fmat k *ᵥ a) :=
      Matrix.mulVec_smul _ (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) a
    rw [e]; exact Submodule.smul_mem _ c ha

theorem isMatIn_basisChange : ∀ (D : D7) (X : HidaSetting D) (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), FixRed X red b → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal → ∀ (P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (u : Fin D.R.r → VA X.B.I), (∀ j, u j - ∑ i, ((((((P : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) i j).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • incl X.B.I (b kv i) ∈ wLf X (D.naut.plGw kv.1 kv.2)) → ∀ k ∈ X.B.I.Kset, GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) u k ((((P⁻¹ * red k kv * P) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
  intro D X red b hf kv hg P u hu k hk j
  haveI : NeZero (D.host.g kv.1) := ⟨(D.host.g_prime kv.1).ne_zero⟩
  have h := basisChange_mod (g := D.host.g kv.1) (wLf X (D.naut.plGw kv.1 kv.2)).toAddSubgroup
    (Matrix.mulVecLin (X.B.I.fmat k)).toAddMonoidHom
    (fun v hv => fmat_mulVec_mem_wLf X _ hk hv)
    (fun i => incl X.B.I (b kv i)) u
    (fun i => by
      have h1 := inclE_smul_mem_wLf X (D.naut.plGw kv.1 kv.2) ((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E)
        ⟨_, hg, by simp⟩ (y := incl X.B.I (b kv i)) (Submodule.subset_span ⟨⟨_, (hf kv).1.1 i⟩, rfl⟩)
      have e : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((D.host.g kv.1 : ℕ) : 𝓞 X.B.I.E) : X.B.I.E) =
          ((D.host.g kv.1 : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
        simp [map_natCast]
      rw [e, Nat.cast_smul_eq_nsmul] at h1
      exact h1)
    ((red k kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix _ _ _) (P : Matrix _ _ _)
    (((P⁻¹ * red k kv * P) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix _ _ _)
    (by rw [← Units.val_mul, ← Units.val_mul]; congr 1; group)
    (fun j => by
      have := hu j
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this)
    (fun i => by
      have := (hf kv).2 k hk i
      simp only [Nat.cast_smul_eq_nsmul] at this
      exact this) j
  simp only [Nat.cast_smul_eq_nsmul]
  exact h

end GlobalTheory.Mem.SymFrame
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

variable {D : D7}

def wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Submodule (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :=
  Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
    {c | ∃ a : 𝓞 X.B.I.E, (∃ b ∈ w.asIdeal, X.ιE (a : X.B.I.E) = (b : D.host.E)) ∧
      c = Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E)}

def ModW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ}
    (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (t : ZMod g) : Prop :=
  c - ((t.val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w

def argS (X : HidaSetting D) (x : X.B.I.Gf) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F :=
  (∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat x *ᵥ nxt X.e0 X.z0 a)) +
    ∑ i : Fin D.R.k, if h : i.1 + 1 < D.R.k then hA X.B.I (X.bwd i) (X.B.I.fmat x *ᵥ X.bw ⟨i.1 + 1, h⟩) else 0

theorem otherInstanceCharacter_eq_psi_symmetricArgument (X : HidaSetting D) (x : X.B.I.Gf) :
    X.chi2 x = X.psiEf (divN X.B.I X.B.g (argS X x)) := rfl


open Classical in
def side (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) : Bool := decide (GlobalTheory.Mem.SymFrame.EwAt X w)

def wtA (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 1 else if i.1 + 1 < ρ + k then (if s then 1 else 0) else 0

def wtB (ρ k : ℕ) (s : Bool) {r : ℕ} (i _j : Fin r) : ℤ :=
  if i.1 < ρ then 0 else if i.1 + 1 < ρ + k then (if s then 0 else -1) else if i.1 = ρ + k then 1 else -1

theorem wt_add (ρ k : ℕ) (s : Bool) {r : ℕ} (i j : Fin r) :
    wtA ρ k s i j + wtB ρ k s i j = 1 ∨ wtA ρ k s i j + wtB ρ k s i j = -1 := by
  unfold wtA wtB
  split_ifs <;> simp

theorem hA_smul_right' (X : HidaSetting D) (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) (x y : VA X.B.I) :
    hA X.B.I x (c • y) = c * hA X.B.I x y := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hA_add_right' (X : HidaSetting D) (x y z : VA X.B.I) :
    hA X.B.I x (y + z) = hA X.B.I x y + hA X.B.I x z := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_zero_right' (X : HidaSetting D) (x : VA X.B.I) : hA X.B.I x 0 = 0 := by
  simp [hA, Formalism.UG.hform]

theorem hA_mem_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {x v : VA X.B.I} (hx : x ∈ X.B.I.Lf)
    (hv : v ∈ wLf X w) : hA X.B.I x v ∈ wInt X w := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨y, hy⟩, rfl⟩ := hv
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, y', hy', rfl⟩ := hy
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • y') i)) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a : X.B.I.E) •
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (y' i)) := by
        funext i; simp [map_mul]
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (((a : X.B.I.E) • y') i)) ∈ wInt X w
      rw [e, hA_smul_right']
      have hint : hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (y' i)) ∈
          Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
        GlobalTheory.St.G.FrameClose.hA_int hx (Submodule.subset_span ⟨⟨y', hy'⟩, rfl⟩)
      rw [mul_comm]
      exact (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E)
        (Submodule.subset_span ⟨a, ha, rfl⟩)
    | zero =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((0 : Fin X.B.I.n → X.B.I.E) i)) = 0 := by
        funext i; simp
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((0 : Fin X.B.I.n → X.B.I.E) i)) ∈ wInt X w
      rw [e, hA_zero_right']; exact zero_mem _
    | add a b _ _ ha hb =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((a + b) i)) =
          (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a i)) +
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (b i)) := by
        funext i; simp
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((a + b) i)) ∈ wInt X w
      rw [e, hA_add_right']; exact add_mem ha hb
    | smul c a _ ha =>
      have e : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((c • a) i)) =
          Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (c : X.B.I.E) •
            (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (a i)) := by
        funext i; simp [Algebra.smul_def, map_mul]
      show hA X.B.I x (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) ((c • a) i)) ∈ wInt X w
      rw [e, hA_smul_right']
      have hc : Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (c : X.B.I.E) ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E :=
        Formalism.UG.P.easyc_inclE_mem _ _ _ (by first | exact ⟨c, rfl⟩ | exact c.2 | simp [Formalism.UG.intOE])
      exact (wInt X w).smul_mem (⟨_, hc⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) ha
  | zero => rw [hA_zero_right']; exact zero_mem _
  | add a b _ _ ha hb => rw [hA_add_right']; exact add_mem ha hb
  | smul c a _ ha =>
    show hA X.B.I x ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • a) ∈ wInt X w
    rw [hA_smul_right']
    exact (wInt X w).smul_mem c ha

theorem hA_sub_right' (X : HidaSetting D) (x y z : VA X.B.I) :
    hA X.B.I x (y - z) = hA X.B.I x y - hA X.B.I x z := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hA_sum_right' (X : HidaSetting D) {ι : Type} (s : Finset ι) (x : VA X.B.I) (y : ι → VA X.B.I) :
    hA X.B.I x (∑ j ∈ s, y j) = ∑ j ∈ s, hA X.B.I x (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact hA_zero_right' X x
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hA_add_right', ih]

theorem hA_isMatIn (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hN : GlobalTheory.Mem.SymFrame.IsMatIn X w u x N)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (i : Fin D.R.r) :
    hA X.B.I y (X.B.I.fmat x *ᵥ u i) -
      ∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I y (u j) ∈ wInt X w := by
  have h := hA_mem_wInt X w hy (hN i)
  rw [hA_sub_right', hA_sum_right'] at h
  simpa only [hA_smul_right'] using h

theorem wInt_of_zmod (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (hc : ZMod' X.B.I X.B.g c) : c ∈ wInt X w := by
  obtain ⟨t, ht, rfl⟩ := hc
  obtain ⟨m, hm⟩ : D.host.g k ∣ X.B.g := by
    rw [X.g_eq]; fin_cases k
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have hgen : ((D.host.g k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
    refine Submodule.subset_span ⟨(D.host.g k : 𝓞 X.B.I.E), ⟨_, hg, ?_⟩, ?_⟩
    · simp
    · simp
  have e : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t =
      ((m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t) * (D.host.g k : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    rw [hm, Nat.cast_mul]; ring
  rw [e]
  exact (wInt X w).smul_mem (⟨_, mul_mem (natCast_mem _ m) ht⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hgen

end GlobalTheory.Mem.SymChar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeConj

theorem continuous_cA (D : D7) : Continuous (cA D) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap
  exact this

end GlobalTheory.HeckeConj
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdCharLocal

theorem psiV_ne_one_of_trace {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ)
    (hinf : ∀ a : F, psiInf F ψ (algebraMap F (Ainf F) a) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F a : ℚ) : ℂ))) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  by_contra hn
  push Not at hn
  have hs := GlobalTheory.SnMass.Inhab.stdAt_of_psiInf h hinf v
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))
  have hd1 : algebraMap F (Fv F v) (d : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact_mod_cast hd0
  obtain ⟨z, hz⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp 1)
  have h1 := (hs (z * (algebraMap F (Fv F v) (d : F))⁻¹)).1 (fun y _ => hn _) d hd
  rw [inv_mul_cancel_right₀ hd1, HeightOneSpectrum.mem_adicCompletionIntegers, hz, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h1
  omega

theorem psiV_ne_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ v, ∃ y, psiV D.host.F ψ v y ≠ 1 := by
  intro D ψ hψ v
  have h := GlobalTheory.StdAdelicChar.isStdChar_inv hψ
  obtain ⟨θ, hθ⟩ := h.2.1
  obtain ⟨y, hy⟩ := psiV_ne_one_of_trace h.1 (fun a => by
    rw [h.2.2 θ hθ, GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _,
      GlobalTheory.StdRat.sum_tauE_eq_trace]
    simp) v
  refine ⟨y, fun h1 => hy ?_⟩
  rw [psiV] at h1 ⊢
  rw [AddChar.inv_apply', h1, inv_one]

end GlobalTheory.StdCharLocal
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.LocWeil
open Formalism.MainNotions.KudlaSiegelWeil (Pl FinF FinE FF Over Split LocW Restr IntV)
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (ConjIsom basConj omTens toHom)
open Formalism.IndefR.Datum (IsHalf IsLatVac)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocWeil.CompactPart

variable {D : D7}

theorem infMat_eq (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram θ g = (infHom V g).1.map θ := rfl

theorem infMat_of_fin (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {k : GA D V} (hk : k ∈ GfC V) :
    infMat D.sp.cm.sig V.gram θ k = 1 := by
  have hk' : infHom V k = 1 := hk
  rw [infMat_eq V, hk', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.LocWeil.CompactPart

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isCuspFunction_closed_under_operations : ∀ (D : D7) (V : HSp D) (φ φ' : GA D V → ℂ), IsAutFun V φ → IsAutFun V φ' → IsCuspFun V φ → IsCuspFun V φ' → IsCuspFun V (φ + φ') ∧ (∀ c : ℂ, IsCuspFun V (c • φ)) ∧ (∀ k, IsCuspFun V (rTr V k φ)) ∧ IsCuspFun V (fun g => star (φ g)) := by
  first | exact @GlobalTheory.Mem.Th.isCuspFun_closed | exact GlobalTheory.Mem.Th.isCuspFun_closed | (intros; apply GlobalTheory.Mem.Th.isCuspFun_closed <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.besselCharacter_generic_character_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), HSpace.IsIsomEmb A B ι → ∀ d : BesDat A B ι, (∀ n n' : NFlag B d.e, besChar ψ d ((n * n' : NFlag B d.e) : GA D B) = besChar ψ d (n : GA D B) * besChar ψ d (n' : GA D B)) ∧ (∀ γ ∈ NFlagQ B d.e, besChar ψ d (γ : GA D B) = 1) ∧ (Continuous fun n : NFlag B d.e => besChar ψ d (n : GA D B)) ∧ ∀ g h, EmbRel B A ι g h → ∀ n ∈ NFlag B d.e, g * n * g⁻¹ ∈ NFlag B d.e ∧ besChar ψ d (g * n * g⁻¹) = besChar ψ d n := by
  first | exact @GlobalTheory.BesselChar.besChar_laws | exact GlobalTheory.BesselChar.besChar_laws | (intros; apply GlobalTheory.BesselChar.besChar_laws <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isotropic_unipotentRadicals_rational_cocompact : ∀ (D : D7) (B : HSp D) (ρ : ℕ) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E), IsIsoSub B e → (∃ K : Set (NFlag B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NFlagQ B e, ∃ k ∈ K, n = γ * k) ∧ (∃ K : Set (NI B e), IsCompact K ∧ ∀ n, ∃ γ ∈ NIQ B e, ∃ k ∈ K, n = γ * k) := by
  first | exact @GlobalTheory.Mem.UnipCocompact.radicals_cocompact | exact GlobalTheory.Mem.UnipCocompact.radicals_cocompact | (intros; apply GlobalTheory.Mem.UnipCocompact.radicals_cocompact <;> assumption)
end
