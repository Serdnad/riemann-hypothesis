module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle317
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle330
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFrameW
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle389
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle031
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictLat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle388
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle385
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle340
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle369
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle357
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle391
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle358
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle392
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2


theorem _root_.GlobalTheory.T.exists_finite_columnConfigurations_witnesses : ∀ (P : Pre) (f : Top.Fr P) (F F₀ : IntermediateField ℚ ℂ) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)),
  ∃ (n : ℕ) (Wt : Fin n → Σ B0 : Base, Σ px0 : PreX B0.toPre, Col2.ColIn B0 px0),
    (∀ i, (Wt i).1.fields.Ok ∧ (Wt i).2.2.Ok) ∧
    ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → B.toPre = P → HEq I.C f → B.KsC = F →
      B.fixedCoefficientFieldInComplex = F₀ → HEq (Set.range I.xi) Ξ → ∃ i, GlobalTheory.Mem.HFld.SameCfg B px I (Wt i).1 (Wt i).2.1 (Wt i).2.2 := by
  first | exact @GlobalTheory.Mem.HFld.exists_finite_cfg | exact GlobalTheory.Mem.HFld.exists_finite_cfg | (intros; apply GlobalTheory.Mem.HFld.exists_finite_cfg <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GroupLoc.Coords

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA PIW.AdelClassFin

variable {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {p m : ℕ}

theorem rep_of_int (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F} (hu : ∀ j, u j ∈ I.Lf) {v : Fin I.n → I.E ⊗[I.F] Af I.F}
    {c : Fin m → ℤ} (h : v - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w) :
    RepV w p u v (fun j => (c j : ZMod p)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have h2 : ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j -
      ∑ j, ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun j _ => ?_
    rw [← sub_smul]
    refine Wq_smul ?_ (hu j)
    have hk : c j - ((((c j : ZMod p)).val : ℕ) : ℤ) = (c j / p) * p := by
      rw [ZMod.val_intCast, Int.emod_def]; ring
    have e : (c j : I.E ⊗[I.F] Af I.F) - ((((c j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) =
        ((c j / p : ℤ) : I.E ⊗[I.F] Af I.F) * (p : I.E ⊗[I.F] Af I.F) := by
      have := congrArg (Int.cast : ℤ → I.E ⊗[I.F] Af I.F) hk
      simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_mul] using this
    rw [e]
    exact Wq_mul (natCast_Wq hp hcard) (intCast_int _)
  have := add_mem h h2
  show v - _ ∈ _
  convert this using 1
  abel

theorem int_comb (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F} (hu : ∀ j, u j ∈ I.Lf) (S : Set (Fin m))
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ Submodule.span (IntAf I.F I.E) (u '' S) ⊔ Lq I w) :
    ∃ c : Fin m → ℤ, (∀ j, j ∉ S → c j = 0) ∧ y - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
  classical
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
  have key : ∃ c : Fin m → ℤ, (∀ j, j ∉ S → c j = 0) ∧
      y1 - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
    clear hy
    induction hy1 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      refine ⟨Pi.single i 1, fun j hj => Pi.single_eq_of_ne (fun e : j = i => hj (by rw [e]; exact hi)) _, ?_⟩
      rw [Fintype.sum_eq_single i (fun j hj => by simp [hj])]
      simp
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨c, hc0, hc⟩ := hx
      obtain ⟨d, hd0, hd⟩ := hz
      refine ⟨c + d, fun j hj => by simp [hc0 j hj, hd0 j hj], ?_⟩
      have := add_mem hc hd
      convert this using 1
      simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
      abel
    | smul s x _ hx =>
      obtain ⟨c, hc0, hc⟩ := hx
      obtain ⟨_, t, -, ht⟩ := congW_exists (w := w) hp hcard s.2
      refine ⟨fun j => t * c j, fun j hj => by simp [hc0 j hj], ?_⟩
      have h1 := (Lq I w).smul_mem s hc
      have h2 : ((s : I.E ⊗[I.F] Af I.F) - (t : I.E ⊗[I.F] Af I.F)) •
          ∑ j, (c j : I.E ⊗[I.F] Af I.F) • u j ∈ Lq I w := by
        refine Wq_smul ht (sum_mem fun j _ => ?_)
        rw [Int.cast_smul_eq_zsmul]
        exact zsmul_mem (hu j) _
      have := add_mem h1 h2
      convert this using 1
      show (s : I.E ⊗[I.F] Af I.F) • x - _ = (s : I.E ⊗[I.F] Af I.F) • (x - _) + _
      simp only [Int.cast_mul, mul_smul, ← Finset.smul_sum, smul_sub, sub_smul]
      abel
  obtain ⟨c, hc0, hc⟩ := key
  refine ⟨c, hc0, ?_⟩
  have := add_mem hc hy2
  convert this using 1
  abel

theorem cols_iff (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hm : m = I.n)
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) (P : GL (Fin m) (ZMod p))
    {u : Fin m → Fin I.n → I.E ⊗[I.F] Af I.F}
    (hP : ∀ j, RepV w p (fun k => iv I (b k)) (u j) (fun k => (P : Matrix (Fin m) (Fin m) (ZMod p)) k j))
    (A : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) (N : Matrix (Fin m) (Fin m) (ZMod p))
    (i : Fin m) (hN : RepV w p u (A *ᵥ u i) (fun j => N j i)) (S : Set (Fin m)) :
    (∀ j, j ∉ S → N j i = (1 : Matrix (Fin m) (Fin m) (ZMod p)) j i) ↔
      (A - 1) *ᵥ u i ∈ Submodule.span (IntAf I.F I.E) (u '' S) ⊔ Lq I w := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have hu : ∀ j, u j ∈ I.Lf := fun j => by
    have h1 : u j - _ ∈ I.Lf := lamAf_mono I (wLat0_le I w) (hP j)
    have h2 : ∑ k, ((((P : Matrix (Fin m) (Fin m) (ZMod p)) k j).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b k) ∈ I.Lf :=
      sum_mem fun k _ => by
        rw [Nat.cast_smul_eq_nsmul]
        exact nsmul_mem (DictLat.iv_mem I (hb.1 k)) _
    simpa using add_mem h1 h2
  have e1 : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j = u i := by
    rw [Fintype.sum_eq_single i (fun j hj => by simp [Matrix.one_apply_ne hj])]
    simp only [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  constructor
  · intro h
    have h1 : ∑ j, (((N j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • u j - u i ∈
        Submodule.span (IntAf I.F I.E) (u '' S) := by
      rw [← e1, ← Finset.sum_sub_distrib]
      refine sum_mem fun j _ => ?_
      by_cases hj : j ∈ S
      · rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
        have hm : u j ∈ Submodule.span (IntAf I.F I.E) (u '' S) := Submodule.subset_span ⟨j, hj, rfl⟩
        exact sub_mem (nsmul_mem hm _) (nsmul_mem hm _)
      · rw [h j hj, sub_self]; exact zero_mem _
    have := Submodule.add_mem_sup h1 hN
    convert this using 1
    abel
  · intro h j hj
    obtain ⟨c, hc0, hc⟩ := int_comb hp hcard hu S h
    have h2 : A *ᵥ u i - ∑ l, (((c + Pi.single i 1 : Fin m → ℤ) l : ℤ) : I.E ⊗[I.F] Af I.F) • u l ∈ Lq I w := by
      convert hc using 1
      simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
      rw [Fintype.sum_eq_single i (f := fun l => (((Pi.single i 1 : Fin m → ℤ) l : ℤ) : I.E ⊗[I.F] Af I.F) • u l)
        (fun l hl => by simp [hl])]
      simp only [Pi.single_eq_same, Int.cast_one, one_smul]
      abel
    have h3 := rep_unique hp hcard hm hb (rep_comp hp hcard hb.1 hN hP)
      (rep_comp hp hcard hb.1 (rep_of_int hp hcard hu h2) hP)
    have h4 := congrArg (fun v => ((P⁻¹ : GL (Fin m) (ZMod p)) : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ v) h3
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h4
    have h5 := congrFun h4 j
    simp only [Pi.add_apply, hc0 j hj, zero_add] at h5
    rw [h5]
    by_cases e : j = i
    · subst e; simp
    · simp [e]

theorem mem_unipSym_iff {κ : Type} [CommRing κ] {r ρ k : ℕ} (N : GL (Fin r) κ) :
    N ∈ unipSym κ r ρ k ↔ ∀ i j : Fin r, j ∉ {j | symAllowed ρ k i j} →
      (N : Matrix (Fin r) (Fin r) κ) j i = (1 : Matrix (Fin r) (Fin r) κ) j i := by
  constructor
  · rintro ⟨h1, h2⟩ i j hj
    rcases lt_trichotomy j i with h | h | h
    · obtain ⟨a, b, c⟩ : ρ ≤ j.1 ∧ j.1 < ρ + k ∧ i.1 = ρ + k := by
        by_contra hh
        exact hj ⟨h, hh⟩
      rw [h2 j i a b c, Matrix.one_apply_ne h.ne]
    · subst h
      rw [unip_diag h1, Matrix.one_apply_eq]
    · rw [unip_lower h1 h, Matrix.one_apply_ne h.ne']
  · intro h
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j ha hb hc => ?_⟩
    · have hij' : j.val < i.val := hij
      rw [h j i (fun hh => by have := hh.1; omega), Matrix.one_apply_ne (fun e => by rw [e] at hij'; omega)]
    · rw [h i i (fun hh => lt_irrefl _ hh.1), Matrix.one_apply_eq]
    · rw [h j i (fun hh => hh.2 ⟨ha, hb, hc⟩), Matrix.one_apply_ne (fun e => by rw [e] at hb; omega)]

end GlobalTheory.Mem.GroupLoc.Coords

namespace GlobalTheory.Mem.GroupLoc


open Formalism.L2.SG.Pf.RowDictPf in
theorem mem_unipSym_iff_colCond : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (N : GL (Fin D.R.r) (ZMod (D.host.g kv.1))), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2) (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) → (N ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k ↔ GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k) := by
  intro D X h hι hg k _ kv N hN
  choose b hb using fun kv => Formalism.L2.SG.Pf.AllRowsRhoX.exists_b X kv
  obtain ⟨P, hP⟩ := GlobalTheory.T.symmetricFrame_reduces_to_basis_mod_place D X h hι b (fun kv => by
    unfold IsRedBasis
    rw [wLat_eq X]
    exact hb kv) hg 1
  rw [Coords.mem_unipSym_iff]
  unfold ColCond ModW
  refine forall_congr' fun i => ?_
  have hP' := hP kv
  have hN' := hN i
  unfold wLf at hP' hN' ⊢
  rw [wLat_eq X] at hP' hN' ⊢
  exact Coords.cols_iff (w := wB X (D.naut.plGw kv.1 kv.2)) (D.host.g_prime kv.1)
    (by rw [card_wB, card_res_host]) X.n_eq.symm (hb kv) (P kv) hP' (X.B.I.fmat k) _ i hN' _

end GlobalTheory.Mem.GroupLoc
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.TopCh

theorem latS_mul_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {Lb L L' S : Submodule (𝓞 E) (Fin n → E)} {y y' k : GL (Fin n) (AfE F E)}
    (hyl : ∀ w : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔ (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb)
    (hL : L = L') (hy : y = y')
    (hl : ∀ w : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L' ↔ ((y' * k)⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S)
    (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S := by
  subst hL hy
  have e1 : (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ (y.1 *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have e2 : ((y * k)⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ (y.1 *ᵥ x) = (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x := by
    have e : (y * k)⁻¹ * y = k⁻¹ := by group
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, e]
  have h1 := hyl (y.1 *ᵥ x)
  have h2 := hl (y.1 *ᵥ x)
  rw [e1] at h1
  rw [e2] at h2
  exact h1.symm.trans h2



theorem kread_member : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → Pins B X → ∀ (l : I.Laws) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl) (k : Unit → GA B (B.R.N B.R.m)), I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k → let U : Subgroup (GA B (B.R.N B.R.m)) := K.lev.U; let Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E) := K.lev.Lb; let chi : U →* ℂˣ := K.lev.chi; (∀ x ∈ UAd B.sp.cm (B.R.N B.R.m), x ∈ U ↔ (k ())⁻¹ * x * k () ∈ levU B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ((I.Tp a).levG B.R.m).grp) ∧ (∀ (x : U) (z : J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)) (h : ((I.Tp a).levG B.R.m).grp), z.1 = (k ())⁻¹ * x.1 * k () → redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs z = h.1⁻¹ → chi x = Units.map (B.embLL : B.LL →* ℂ) (((I.Tp a).levG B.R.m).chr h)) ∧ ∀ x : Fin (B.R.N B.R.m) → B.host.E ⊗[B.host.F] FiniteAdeleRing (𝓞 B.host.F) B.host.F, x ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) Lb ↔ ((k ())⁻¹ : GL (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)).1 *ᵥ x ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) := by
  intro B X I hI hP l Z u a K k hR U Lb chi
  have hQ0 : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  have hG : (I.Tp a).levG B.R.m = (I.Tp I.mu0).levG B.R.m := by
    rw [TC.Tp, TC.Tp, topLev_levG_m, topLev_levG_m]
  obtain ⟨c₀⟩ := (GlobalTheory.T.lastStep_tuple_group_classes_coordinates I u I.mu0).2.2.2
  obtain ⟨e, he⟩ := (GlobalTheory.T.lastStep_tuple_group_classes_coordinates I u I.mu0).1 c₀
  have hp := (hR.pt c₀).of_extTo (I.Q_subset_SQ I.mu0) (by rw [hQ0]; exact Finset.disjoint_empty_right _)
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : GA B (B.R.N B.R.m), y₀ = (K.y c₀).1 := ⟨_, rfl⟩
  rw [← hy₀] at hp
  rw [hG]

  have hθ : ∀ θ : ((I.Tp I.mu0).levQ B.R.m).grp, θ = 1 := fun θ =>
    Subtype.ext (funext fun P => (Finset.notMem_empty P.1 (hQ0 ▸ P.2)).elim)

  have hD : ∀ q q' : DecoF B.host.E (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0), q.deco = q'.deco → q = q' :=
    fun q q' h => Subtype.ext (Prod.ext h (funext fun P => (Finset.notMem_empty P.1 (hQ0 ▸ P.2)).elim))
  have hgam : ∀ γ : UF B.host.E (B.R.N B.R.m), ufGL B.host.E (B.R.N B.R.m) γ = 1 → γ = 1 := fun γ h =>
    Subtype.ext ((toGLm B.host.E (B.R.N B.R.m)).injective (by show _ = toGLm B.host.E (B.R.N B.R.m) 1; rw [map_one]; exact h))
  have hmul : ∀ x : GA B (B.R.N B.R.m), y₀ * k () * ((k ())⁻¹ * x * k ()) = y₀ * x * k () := fun x => by group
  have hku : k () ∈ UAd B.sp.cm (B.R.N B.R.m) := by
    obtain ⟨p₀, hp₀, -⟩ := hR.k_std ()
    exact hp₀.uni
  have hyu : y₀ ∈ UAd B.sp.cm (B.R.N B.R.m) := by
    have := mul_mem hp.uni (inv_mem hku)
    rwa [mul_inv_cancel_right] at this

  have hact : ∀ h : ((I.Tp I.mu0).levG B.R.m).grp,
      (I.stp u I.mu0 B.R.m).gam c₀.1 (e.symm (1, h, 1)) = 1 ∧
      ((I.stp u I.mu0 B.R.m).act c₀.1 (e.symm (1, h, 1)) ((I.stp u I.mu0 B.R.m).rep c₀)).1.1 =
        ((1 : UF B.host.E (B.R.N B.R.m)), h.1, (1 : GLQ B.host.E (B.R.N B.R.m) (I.Q I.mu0))) • ((I.stp u I.mu0 B.R.m).rep c₀).1.1 ∧
      cosetIn ((I.stp u I.mu0 B.R.m).act c₀.1 (e.symm (1, h, 1)) ((I.stp u I.mu0 B.R.m).rep c₀)) =
        cosetIn ((I.stp u I.mu0 B.R.m).rep c₀) ∧
      (I.stp u I.mu0 B.R.m).chr c₀.1 (e.symm (1, h, 1)) = ((I.Tp I.mu0).levG B.R.m).chr h := fun h => by
    obtain ⟨-, h1, h2, h3, h4, -⟩ := he (e.symm (1, h, 1))
    rw [e.apply_symm_apply] at h1 h2 h3
    refine ⟨by rw [h1]; exact map_one _, by rw [h3]; rfl, h4, by rw [h2, map_one, mul_one]⟩
  refine ⟨fun x hxu => ?_, fun x z h hz hred => ?_, fun x => ?_⟩
  · have hgu : y₀ * x * k () ∈ UAd B.sp.cm (B.R.N B.R.m) := mul_mem (mul_mem hyu hxu) hku
    obtain ⟨q, hq⟩ := (GlobalTheory.T.isPtOf_mul_J0_decoration B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0)
      (y₀ * x * k ()) 1 ((I.stp u I.mu0 B.R.m).rep c₀).1.1 ((I.stp u I.mu0 B.R.m).rep c₀).1.1 1).2.2 hQ0 hgu
    have H2 := fun h => (GlobalTheory.T.isPtOf_mul_J0_decoration B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0)
      (y₀ * k ()) ((k ())⁻¹ * x * k ()) ((I.stp u I.mu0 B.R.m).rep c₀).1.1 q h).1 hp (by rw [hmul]; exact hq)
    have hq' := hq
    rw [hy₀] at hq'
    rw [hR.lev c₀ x q hq', levU, Subgroup.mem_map]
    constructor
    · rintro ⟨κ, hκ1, hκq, -⟩
      obtain ⟨-, hg, -, h3, -⟩ := he κ
      have e1 : (e κ).1 = 1 := hgam _ (by rw [← hg]; exact hκ1)
      have hq2 : q = ((1 : UF B.host.E (B.R.N B.R.m)), (e κ).2.1.1, (1 : GLQ B.host.E (B.R.N B.R.m) (I.Q I.mu0))) •
          ((I.stp u I.mu0 B.R.m).rep c₀).1.1 := by
        rw [← hκq, h3, e1, hθ (e κ).2.2]; rfl
      obtain ⟨hz, hred⟩ := (H2 (e κ).2.1.1).2 (by rw [hq2]; rfl)
      exact ⟨⟨_, hz⟩, by show redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hz⟩ ∈ ((I.Tp I.mu0).levG B.R.m).grp; rw [hred]; exact inv_mem (e κ).2.1.2, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      have hz : (k ())⁻¹ * x * k () ∈ J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) := hwz ▸ w.2
      have hw' : redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs w ∈ ((I.Tp I.mu0).levG B.R.m).grp := hw
      have hd := (H2 (redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs w)⁻¹).1
        ⟨hz, by rw [inv_inv]; congr 1; exact Subtype.ext hwz.symm⟩
      have hq2 : q = ((1 : UF B.host.E (B.R.N B.R.m)), (redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs w)⁻¹,
          (1 : GLQ B.host.E (B.R.N B.R.m) (I.Q I.mu0))) • ((I.stp u I.mu0 B.R.m).rep c₀).1.1 := hD _ _ hd
      obtain ⟨g1, g2, g3, -⟩ := hact ⟨_, inv_mem hw'⟩
      refine ⟨e.symm (1, ⟨_, inv_mem hw'⟩, 1), g1, ?_, g3⟩
      rw [g2, hq2]
  · have hz' : (k ())⁻¹ * x.1 * k () ∈ J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) := hz ▸ z.2
    have hred' : redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hz'⟩ = h.1⁻¹ := by
      rw [← hred]; congr 1; exact Subtype.ext hz.symm
    have hpt := (GlobalTheory.T.isPtOf_mul_J0_decoration B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0)
      (y₀ * k ()) ((k ())⁻¹ * x.1 * k ()) ((I.stp u I.mu0 B.R.m).rep c₀).1.1 ((I.stp u I.mu0 B.R.m).rep c₀).1.1 h.1).2.1 hQ0 hp hz' hred'
    rw [hmul] at hpt
    obtain ⟨g1, g2, -, g4⟩ := hact h
    have := hR.chr c₀ x (e.symm (1, h, 1)) g1 (by rw [g2, ← hy₀]; exact hpt)
    rw [g4] at this
    exact Units.ext this
  · have hS : ∀ w : Fin (B.R.N B.R.m) → B.host.E ⊗[B.host.F] FiniteAdeleRing (𝓞 B.host.F) B.host.F,
        w ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) ↔
        ((1 : GA B (B.R.N B.R.m))⁻¹ : GA B (B.R.N B.R.m)).1 *ᵥ w ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) :=
      fun w => by
        have e : ((1 : GA B (B.R.N B.R.m))⁻¹ : GA B (B.R.N B.R.m)).1 *ᵥ w = w := by rw [inv_one, Units.val_one, Matrix.one_mulVec]
        rw [e]
    have hp1 : IsPtOf B.sp.cm (y₀ * k () * (1 * 1)) ((I.stp u I.mu0 B.R.m).rep c₀).1.1 := by rw [mul_one, mul_one]; exact hp
    have hl := GlobalTheory.T.pointLattice_iff_baseLattice_decorated B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0)
      (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) 1 1 (y₀ * k ()) ((I.stp u I.mu0 B.R.m).rep c₀).1.1 (one_mem _) hS hp1
    have hc := (((spaces_in_coordinates I hI hP l Z).2.2.2 B.R.m le_rfl).2.2 u I.mu0).1 c₀
    exact latS_mul_iff (K.y_lat c₀) hc hy₀.symm hl x

end GlobalTheory.Mem.Col2.TopCh
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaKernelLift_converges_continuous_growth_deriv : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∀ f h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ) ∧ (∀ f, Continuous fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∧ (∃ N : ℕ, ∀ f, ∃ C : ℝ, ∀ h, ‖∫ g in 𝓕, κ f g h * F g ∂μ‖ ≤ C * (height θ W h : ℝ) ^ N) ∧ ∀ τ, ∀ X ∈ lieAt W τ, ∀ f f', (∀ g h, HasDerivAt (fun t : ℝ => κ f g (h * oneP θ W τ X t)) (κ f' g h) 0) → ∀ h, HasDerivAt (fun t : ℝ => ∫ g in 𝓕, κ f g (h * oneP θ W τ X t) * F g ∂μ) (∫ g in 𝓕, κ f' g h * F g ∂μ) 0 := by
  first | exact @GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv | exact GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv | (intros; apply GlobalTheory.Mem.Lift.lift_conv_cont_growth_deriv <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

theorem carries_mul_self {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {g h : GL (Fin N) (TensorProduct F E (Formalism.L2.Herm.Af F))} {L : Submodule (𝓞 E) (Fin N → E)}
    (hg : Formalism.L2.Herm.Carries g L L) (hh : Formalism.L2.Herm.Carries h L L) : Formalism.L2.Herm.Carries (g * h) L L := by
  intro x
  rw [hg x, hh, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]



theorem admissibleBasePoint_chart_mul_twist : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∀ (g : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → Ch0) (t : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), (∀ β, ∃ p : DecoF B.fields.E (B.R.N i) ∅ ∅ ∅, PtOf (t β) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N i)) → (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), ((B.T u : 𝓞 B.host.F) ∈ v.asIdeal ∨ ∀ j, (B.host.g j : 𝓞 B.host.F) ∉ v.asIdeal) → bc (prV (E := B.host.E) v) (t β) = 1) → (a = I.mu0 → ∀ β, t β = 1) → GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i (fun β => k0 (g β) * t β) := by
  intro B X I hI u a i Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 hR g t hstd hoff h0
  refine ⟨fun β => ?_, fun β v hT hQ hd => ?_, fun β P r j hr => ?_⟩
  · obtain ⟨p, hp, hN⟩ := hR.k_std (g β)
    obtain ⟨q, hq, hN'⟩ := hstd β
    have h1 := hp.lat
    have h2 := hq.lat
    rw [hN] at h1
    rw [hN'] at h2
    refine ⟨p, ⟨mul_mem hp.uni hq.uni, ?_, fun P => ?_, fun w => ?_, fun P => ?_⟩, hN⟩
    · rw [hN]
      exact carries_mul_self h1 h2
    · exact absurd P.2 (Finset.notMem_empty _)
    · exact absurd w.2 (Finset.notMem_empty _)
    · exact absurd P.2 (Finset.notMem_empty _)
  · have hq0 : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty _
    have hk : bc (prV (E := B.host.E) v) (k0 (g β)) = 1 :=
      hR.k_off (g β) v hT (by rintro ⟨P, hP, -⟩; rw [hq0] at hP; simp at hP) (Or.inl rfl)
    have ht : bc (prV (E := B.host.E) v) (t β) = 1 := by
      rcases hd with rfl | hd
      · rw [h0 rfl β, map_one]
      · exact hoff β v (Or.inr hd)
    have hm := map_mul (bc (prV (E := B.host.E) v)) (k0 (g β)) (t β)
    rw [hk, ht, one_mul] at hm
    exact hm
  · have hv : (B.T u : 𝓞 B.host.F) ∈ (P.1.under (𝓞 B.host.F)).asIdeal := by
      have := T_mem_vT (GlobalTheory.BasePrimes.primes_ok B X).1 u P
      rw [HeightOneSpectrum.under, Ideal.mem_comap, map_natCast]
      exact this
    have ht := hoff β _ (Or.inl hv)
    have ht' := (map_inv (bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F)))) (t β)).trans (by rw [ht, inv_one])
    have hent : ∀ r l, adAt B.host.F P.1 (((t β)⁻¹ : GA B (B.R.N i)).1 r l) = if r = l then 1 else 0 := by
      intro r l
      have e := congrArg (fun g => g.1 r l) ht'
      simp only [bc, Units.coe_map, Units.val_one, MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at e
      change prV (E := B.host.E) (P.1.under (𝓞 B.host.F)) (((t β)⁻¹ : GA B (B.R.N i)).1 r l) = _ at e
      split_ifs with h
      · subst h
        exact FullDt.adAt_eq_one_of_prV P.1 (by simpa only [Matrix.one_apply_eq] using e)
      · exact TilX.adAt_eq_zero_of_prV P.1 _ (by simpa only [Matrix.one_apply_ne h] using e)
    have key : adAt B.host.F P.1 (((k0 (g β) * t β)⁻¹ : GA B (B.R.N i)).1 r j) =
        adAt B.host.F P.1 (((k0 (g β))⁻¹ : GA B (B.R.N i)).1 r j) := by

      rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply, map_sum]
      simp only [map_mul, hent, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [key]
    exact hR.k_T (g β) P r j hr

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelChoices_standard_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKerTie l Z t → ex.errX.piT = X.piT → t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  first | exact @GlobalTheory.Mem.Col2.TC.k_pins_tie | exact GlobalTheory.Mem.Col2.TC.k_pins_tie | (intros; apply GlobalTheory.Mem.Col2.TC.k_pins_tie <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem _root_.GlobalTheory.T.normAt_sq_integralForm_eq_classSumMetric : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x : (MtHL I hX a).V), ((Formalism.HermitianLatticesTheory.normAt (MtHL I hX a).b (MtHL I hX a).X (InfinitePlace.mk B.embLL) x ^ 2 : ℝ) : ℂ) = cSum I hX a (toCx I hX a x) (toCx I hX a x) := by
  first | exact @GlobalTheory.Mem.Df.normAt_sq_eq_cSum | exact GlobalTheory.Mem.Df.normAt_sq_eq_cSum | (intros; apply GlobalTheory.Mem.Df.normAt_sq_eq_cSum <;> assumption)
end
