module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle403
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle272
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle163
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle148
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle400
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle127
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle002
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
import Formalism.LocalToGlobal.IndefiniteReal.Bundle017
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FixLev
variable {D : D7}

theorem continuous_mt (V : HSp D) : Continuous (mt V) :=
  Units.continuous_val.comp continuous_subtype_val

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y : Type} [Fintype Y] [DecidableEq Y]

theorem map_mt_mul (q : SplitPt D k) (V : HSp D) (g h : GA D V) :
    (mt V (g * h)).map q.pr = (mt V g).map q.pr * (mt V h).map q.pr := by
  rw [GlobalTheory.SplitCut.mt_mul, Matrix.map_mul]

theorem frame_mul {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (A B : Matrix (Fin N) (Fin N) k) :
    F.γ * A * F.β * (F.γ * B * F.β) = F.γ * (A * B) * F.β := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.β F.γ, F.βγ, Matrix.one_mul]

theorem frame_cancel {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) {A B : Matrix Y Y k}
    (h : F.β * A * F.γ = F.β * B * F.γ) : A = B := by
  have := congrArg (fun M => F.γ * M * F.β) h
  simp only [Matrix.mul_assoc] at this
  simpa [← Matrix.mul_assoc, F.γβ] using this

theorem frame_conj {N : ℕ} (F : GlobalTheory.LocMod.Frame k N Y) (A : Matrix (Fin N) (Fin N) k) :
    F.β * (F.γ * A * F.β) * F.γ = A := by
  simp only [← Matrix.mul_assoc, F.βγ, Matrix.one_mul]
  rw [Matrix.mul_assoc, F.βγ, Matrix.mul_one]

def locHom (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) : GA D V →* GL Y k where
  toFun g := ⟨F.γ * (mt V g).map q.pr * F.β, F.γ * (mt V g⁻¹).map q.pr * F.β,
    by rw [frame_mul, ← map_mt_mul, mul_inv_cancel, GlobalTheory.SplitCut.mt_one,
      Matrix.map_one _ (map_zero q.pr) (map_one q.pr), Matrix.mul_one, F.γβ],
    by rw [frame_mul, ← map_mt_mul, inv_mul_cancel, GlobalTheory.SplitCut.mt_one,
      Matrix.map_one _ (map_zero q.pr) (map_one q.pr), Matrix.mul_one, F.γβ]⟩
  map_one' := Units.ext (by
    change F.γ * (mt V 1).map q.pr * F.β = 1
    rw [GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (map_zero q.pr) (map_one q.pr), Matrix.mul_one, F.γβ])
  map_mul' g h := Units.ext (by
    change F.γ * (mt V (g * h)).map q.pr * F.β = F.γ * (mt V g).map q.pr * F.β * (F.γ * (mt V h).map q.pr * F.β)
    rw [frame_mul, map_mt_mul])

theorem locHom_val (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) (g : GA D V) :
    (locHom q V F g).val = F.γ * (mt V g).map q.pr * F.β := rfl

theorem locHom_spec (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) (g : GA D V) :
    (mt V g).map q.pr = F.β * (locHom q V F g).val * F.γ := by
  rw [locHom_val, frame_conj]

theorem continuous_locHom (q : SplitPt D k) (V : HSp D) (F : GlobalTheory.LocMod.Frame k V.rank Y) :
    Continuous (locHom q V F) := by
  have h1 : Continuous fun g : GA D V => F.γ * (mt V g).map q.pr * F.β :=
    (continuous_const.matrix_mul ((continuous_mt V).matrix_map q.cont_pr)).matrix_mul continuous_const
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  refine (h1.comp continuous_inv).congr fun g => ?_
  change F.γ * (mt V g⁻¹).map q.pr * F.β = ((locHom q V F g)⁻¹ : GL Y k).val
  rw [← map_inv, locHom_val]

end Local

theorem list_prod_single {M : Type} [Monoid M] {ι : Type} [DecidableEq ι] (f : ι → M) (i : ι)
    (hf : ∀ i', i' ≠ i → f i' = 1) : ∀ l : List ι, l.Nodup → i ∈ l → (l.map f).prod = f i := by
  intro l hl hi
  rw [List.prod_map_eq_pow_single i f (fun i' hne _ => hf i' hne),
    List.count_eq_one_of_mem hl hi, pow_one]

theorem map_mt_list_prod {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) (V : HSp D) (l : List (GA D V)) : (mt V l.prod).map q.pr = (l.map fun g => (mt V g).map q.pr).prod := by
  induction l with
  | nil => simp [GlobalTheory.SplitCut.mt_one]
  | cons a l ih => rw [List.prod_cons, map_mt_mul, ih, List.map_cons, List.prod_cons]

theorem exists_section (V : HSp D) {n : ℕ} (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)]
    [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, SplitPt D (k i))
    (hq : Function.Injective fun i => (q i).v) (Y : Fin n → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : ∀ i, GlobalTheory.LocMod.Frame (k i) V.rank (Y i)) :
    ∃ Ψ : (∀ i, GL (Y i) (k i)) → GA D V, Continuous Ψ ∧ (∀ x, Ψ x ∈ grpAt V (fun p => ∃ i, p = (q i).v)) ∧
      (∀ x i, (mt V (Ψ x)).map (q i).pr = (F i).β * (x i).val * (F i).γ) ∧
      ∀ g ∈ grpAt V (fun p => ∃ i, p = (q i).v), ∀ x,
        (∀ i, (mt V g).map (q i).pr = (F i).β * (x i).val * (F i).γ) → Ψ x = g := by
  choose gl hgc hgl hgu using fun i => GlobalTheory.T.exists_continuous_local_GL_embedding_splitPlace D (k i) (q i) V (Y i) (F i)
  have hmat : ∀ (h : Fin n → GA D V), (∀ i, SuppAt (q i).e V (h i)) → ∀ i,
      (mt V ((List.finRange n).map h).prod).map (q i).pr = (mt V (h i)).map (q i).pr := fun h hh i => by
    rw [map_mt_list_prod, List.map_map]
    exact list_prod_single (fun i' => (mt V (h i')).map (q i).pr) i
      (fun i' hi' => GlobalTheory.T.matrix_proj_eq_one_of_suppAt_distinct_finitePlace D (k i) (k i') (q i) (q i') V (h i') (fun e => hi' (hq e).symm) (hh i'))
      _ (List.nodup_finRange n) (List.mem_finRange i)
  refine ⟨fun x => ((List.finRange n).map fun i => gl i (x i)).prod, ?_, fun x => ?_, fun x i => ?_, fun g hg x hx => ?_⟩
  · exact continuous_list_prod _ fun i _ => (hgc i).comp (continuous_apply i)
  · refine Subgroup.list_prod_mem (K := grpAt V (fun p => ∃ i, p = (q i).v)) fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact GlobalTheory.T.mem_supportedSubgroup_of_suppAt_splitPlace_mem D (k i) (q i) V _ (hgl i (x i)).1 _ ⟨i, rfl⟩
  · rw [hmat (fun i => gl i (x i)) (fun i => (hgl i (x i)).1) i]
    exact (hgl i (x i)).2
  · obtain ⟨h, hh, rfl⟩ := GlobalTheory.T.unitarySupported_splitPlaces_eq_prod_local_parts D V n k q hq g hg
    show ((List.finRange n).map fun i => gl i (x i)).prod = _
    congr 1
    refine List.map_congr_left fun i _ => (hgu i (h i) (x i) (hh i) ((hmat h hh i).symm.trans (hx i))).symm


open GlobalTheory.SeeSaw GlobalTheory.StepData in
theorem fixLev_compact_open : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), GPin G → ∀ j, j < D.R.m →
    v.JG j ≤ grpAt (c.V j) (· ∈ v.gP) ∧ IsCompact (v.JG j : Set (GA D (c.V j))) ∧
    IsOpen (((v.JG j).subgroupOf (grpAt (c.V j) (· ∈ v.gP)) : Subgroup _) : Set (grpAt (c.V j) (· ∈ v.gP))) := by
  intro D c v n G hG j hj
  have ha : ∀ i, j + ((G i).s + 1 - j) = (G i).s + 1 := fun i => by have := (G i).hs; omega
  set V := c.V j
  have hP : (· ∈ v.gP) = fun p => ∃ i, p = (G i).q.v := funext fun p => propext (hG.places p)
  have hMat : ∀ i a ha g x, (G i).Mat j a ha g x ↔ x = locHom (G i).q V ((G i).FY j a ha) g := fun i a ha g x => by
    constructor
    · intro h
      exact Units.ext (frame_cancel ((G i).FY j a ha) (h.symm.trans (locHom_spec _ _ _ g)))
    · rintro rfl
      exact locHom_spec _ _ _ g
  let Js : ∀ i, Subgroup (GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((G i).s + 1 - j)) (G i).k) := fun i =>
    (((G i).S.T (Fin D.R.t)).lev j _ (ha i)).J
  have hJ : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO (Js i) := fun i =>
    GlobalTheory.UnfoldedEntries.isCO_lev (T := (G i).S.T (Fin D.R.t)) (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _) j _ (ha i)
  have hmem : ∀ g, g ∈ v.JG j ↔ g ∈ grpAt V (· ∈ v.gP) ∧ ∀ i, locHom (G i).q V ((G i).FY j _ (ha i)) g ∈ Js i := by
    intro g
    rw [hG.lev j hj g]
    refine and_congr_right fun _ => ⟨fun H i => H i _ (ha i) _ ((hMat _ _ _ _ _).2 rfl), fun H i a ha' x hx => ?_⟩
    have e : a = (G i).s + 1 - j := by omega
    subst e
    rw [(hMat _ _ _ _ _).1 hx]
    exact H i
  refine ⟨fun g hg => ((hmem g).1 hg).1, ?_, ?_⟩
  · obtain ⟨Ψ, hc, hin, hloc, huniq⟩ := exists_section V (fun i => (G i).k) (fun i => (G i).q) hG.inj
      (fun i => XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin ((G i).s + 1 - j)) (fun i => (G i).FY j _ (ha i))
    have himg : (v.JG j : Set (GA D V)) = Ψ '' Set.pi Set.univ fun i => (Js i : Set _) := by
      ext g
      constructor
      · intro hg
        obtain ⟨h1, h2⟩ := (hmem g).1 hg
        refine ⟨fun i => locHom (G i).q V ((G i).FY j _ (ha i)) g, fun i _ => h2 i, huniq g (hP ▸ h1) _ fun i => ?_⟩
        exact locHom_spec _ _ _ g
      · rintro ⟨x, hx, rfl⟩
        refine (hmem _).2 ⟨hP ▸ hin x, fun i => ?_⟩
        have e : locHom (G i).q V ((G i).FY j _ (ha i)) (Ψ x) = x i :=
          Units.ext (frame_cancel ((G i).FY j _ (ha i)) ((locHom_spec _ _ _ _).symm.trans (hloc x i)))
        rw [e]
        exact hx i (Set.mem_univ _)
    rw [himg]
    exact (isCompact_univ_pi fun i => (hJ i).2).image hc
  · have hset : (((v.JG j).subgroupOf (grpAt V (· ∈ v.gP)) : Subgroup _) : Set (grpAt V (· ∈ v.gP))) =
        ⋂ i, (fun g : grpAt V (· ∈ v.gP) => locHom (G i).q V ((G i).FY j _ (ha i)) g.1) ⁻¹' (Js i : Set _) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_iInter, Set.mem_preimage]
      exact ((hmem g.1).trans (and_iff_right g.2))
    rw [hset]
    exact isOpen_iInter_of_finite fun i =>
      (hJ i).1.preimage ((continuous_locHom _ _ _).comp continuous_subtype_val)

end GlobalTheory.FixLev
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LatAt

variable {D : D7}

theorem pairA_mul (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := by
  refine Prod.ext ?_ ?_
  · show (0 : Ainf D.host.F) * 0 = 0
    rw [zero_mul]
  · rfl

theorem pair_tmul_mul (α β : Af D.host.F) (a b : D.host.E) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] a : AE D) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] b) =
      pairA D.host.F 0 (α * β) ⊗ₜ[D.host.F] (a * b) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul]

def Good (v : Pl D) (α : Af D.host.F) : Prop :=
  α ∈ intAf D.host.F ∧ ∀ w, w ≠ v → evalV D.host.F w α = 0

theorem Good.mul {v : Pl D} {α β : Af D.host.F} (hα : Good v α) (hβ : Good v β) : Good v (α * β) :=
  ⟨fun w => by rw [map_mul]; exact mul_mem (hα.1 w) (hβ.1 w), fun w hw => by rw [map_mul, hα.2 w hw, zero_mul]⟩

theorem good_indP (v : Pl D) : Good v (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := by
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [GlobalTheory.SelfDualAt.evalV_indP, if_neg hw]

theorem indicatorAdele_mul_self (v : Pl D) :
    GlobalTheory.SelfDualAt.indP (D := D) (· = v) * GlobalTheory.SelfDualAt.indP (D := D) (· = v) = GlobalTheory.SelfDualAt.indP (D := D) (· = v) := by
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  have h1 : evalV D.host.F w (GlobalTheory.SelfDualAt.indP (D := D) (· = v) * GlobalTheory.SelfDualAt.indP (D := D) (· = v)) =
      evalV D.host.F w (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := by
    rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs <;> simp
  exact h1

theorem gen_mem_idAt (v : Pl D) (α : Af D.host.F) (hα : ∀ w, w ≠ v → evalV D.host.F w α = 0) (x : D.host.E) :
    (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x ∈ idAt D (· = v) := by
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [hα _ w.2, TensorProduct.zero_tmul]

theorem AA_ne_zero : D.host.AA ≠ 0 :=
  (GlobalTheory.SeeSaw.LiftModel.AA_ne (D := D) Formalism.IndefR.Fin.factPrincipalDatum).1

theorem int_of_mem {c d : D.host.E} (hc : c ∈ D.host.AA) (hd : d ∈ D.host.AA⁻¹) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = d * c := by
  have h : d * c ∈ D.host.AA⁻¹ * D.host.AA := FractionalIdeal.mul_mem_mul hd hc
  rw [inv_mul_cancel₀ AA_ne_zero] at h
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact ⟨o, ho⟩

theorem smul_latV_mem_latA (S : HSp D) (L : Lat S) (v : Pl D) {ε : Af D.host.F} (hε : Good v ε) {c : D.host.E}
    (hc : c ∈ D.host.AA) {z : Fin S.rank → AE D} (hz : z ∈ latV S L (· = v)) :
    ((pairA D.host.F 0 ε) ⊗ₜ[D.host.F] c : AE D) • z ∈ latA S L (· = v) := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hz
  unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβ1, hβ2, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    apply AddSubgroup.subset_closure
    have g := hε.mul ⟨hβ1, hβ2⟩
    refine ⟨ε * β, g.1, g.2, c, hc, x, hx, ?_⟩
    funext i
    rw [Pi.smul_apply, smul_eq_mul, pair_tmul_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

end GlobalTheory.SeeSaw.LatAt

namespace GlobalTheory.SeeSaw.LatAt

variable {D : D7}

theorem mem_latA_fwd (S : HSp D) (L : Lat S) (v : Pl D) (y : Fin S.rank → AE D) (hy : y ∈ latA S L (· = v)) :
    (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) := by
  unfold GlobalTheory.FinPl.latA GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα1, hα2, c, hc, x, hx, rfl⟩ := hy
    refine ⟨fun i => gen_mem_idAt v α hα2 _, fun s hs => ?_⟩
    unfold idV at hs
    induction hs using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨β, hβ1, hβ2, d, hd, rfl⟩ := hs
      obtain ⟨o, ho⟩ := int_of_mem hc hd
      unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
      apply AddSubgroup.subset_closure
      have g := Good.mul (v := v) ⟨hβ1, hβ2⟩ ⟨hα1, hα2⟩
      refine ⟨β * α, g.1, g.2, 1, rfl, o • x, L.smul_mem o hx, ?_⟩
      funext i
      rw [Pi.smul_apply, smul_eq_mul, pair_tmul_mul, one_mul, Pi.smul_apply, Algebra.smul_def, ← mul_assoc]
      congr 2
      exact ho.symm
    | zero => rw [zero_smul]; exact zero_mem _
    | add s t _ _ h1 h2 => rw [add_smul]; exact add_mem h1 h2
    | neg s _ h => rw [neg_smul]; exact neg_mem h
  | zero => exact ⟨fun i => zero_mem _, fun s _ => by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ h1 h2 =>
    exact ⟨fun i => add_mem (h1.1 i) (h2.1 i), fun s hs => by rw [smul_add]; exact add_mem (h1.2 s hs) (h2.2 s hs)⟩
  | neg y _ h => exact ⟨fun i => neg_mem (h.1 i), fun s hs => by rw [smul_neg]; exact neg_mem (h.2 s hs)⟩

theorem mem_latA_bwd (S : HSp D) (L : Lat S) (v : Pl D) (y : Fin S.rank → AE D) (hsupp : ∀ i, y i ∈ idAt D (· = v))
    (h : ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v)) : y ∈ latA S L (· = v) := by
  have hε : Good v (GlobalTheory.SelfDualAt.indP (D := D) (· = v)) := good_indP v
  have key : ∀ t ∈ D.host.AA * D.host.AA⁻¹,
      ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] t : AE D) • y ∈ latA S L (· = v) := by
    intro t ht
    refine FractionalIdeal.mul_induction_on ht ?_ ?_
    · intro c hc d hd
      have e : ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] (c * d) : AE D) =
          ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] c) *
            ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] d) := by
        rw [pair_tmul_mul, indicatorAdele_mul_self]
      rw [e, mul_smul]
      refine smul_latV_mem_latA S L v hε hc (h _ ?_)
      unfold idV
      exact AddSubgroup.subset_closure ⟨_, hε.1, hε.2, d, hd, rfl⟩
    · intro a b ha hb
      rw [TensorProduct.tmul_add, add_smul]
      exact add_mem ha hb
  have h1 := key 1 (by rw [mul_inv_cancel₀ AA_ne_zero]; exact FractionalIdeal.one_mem_one _)
  have e1 : ((pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP (D := D) (· = v))) ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) • y = y := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    exact GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) (y i) (hsupp i)
  rwa [e1] at h1

end GlobalTheory.SeeSaw.LatAt

theorem GlobalTheory.SeeSaw.mem_latA_iff_mul_inv : ∀ (D : D7) (v : Pl D) (S : HSp D) (L : Lat S) (y : Fin S.rank → AE D), y ∈ latA S L (· = v) ↔ (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ idV D.host.AA⁻¹ v, s • y ∈ latV S L (· = v) :=
  fun _ v S L y => ⟨GlobalTheory.SeeSaw.LatAt.mem_latA_fwd S L v y, fun h => GlobalTheory.SeeSaw.LatAt.mem_latA_bwd S L v y h.1 h.2⟩

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.periodIdealZpow_completion_adeleConj_iff : ∀ (D : D7) (v : Pl D) (n : ℤ) (s : AE D), s ∈ idV (D.host.AA ^ n) v ↔ cA D s ∈ idV (D.host.AAbar ^ n) v := by
  first | exact @GlobalTheory.SeeSaw.idV_AA_zpow_conj | exact GlobalTheory.SeeSaw.idV_AA_zpow_conj | (intros; apply GlobalTheory.SeeSaw.idV_AA_zpow_conj <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistPlace_last_two_level_indices_ne_zero : ∀ (D : D7) (c : Comm D) (v : VCom c) (χ : ℕ → (AE D)ˣ →* Circle) (Q : QAt v χ), Q.idx (Q.s + 1) ≠ 0 ∧ Q.idx (Q.s + 1 + 1) ≠ 0 := by
  first | exact @GlobalTheory.QPl.QAt.idx_last_ne_zero | exact GlobalTheory.QPl.QAt.idx_last_ne_zero | (intros; apply GlobalTheory.QPl.QAt.idx_last_ne_zero <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_spanSingleton_mul_idealCompletion_iff : ∀ (D : D7) (v : Pl D) (𝔞 : FI D) (x : D.host.E), x ≠ 0 → ∀ s, s ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔞) v ↔ incA D x⁻¹ * s ∈ idV 𝔞 v ∧ s ∈ idAt D (· = v) := by
  first | exact @GlobalTheory.SeeSaw.idV_spanSingleton_mul_iff | exact GlobalTheory.SeeSaw.idV_spanSingleton_mul_iff | (intros; apply GlobalTheory.SeeSaw.idV_spanSingleton_mul_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistPlace_couplingIndex_finite_level_stable : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), (Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)).Finite ∧ (∀ yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb) ∧ (∀ yb yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb) ∧ (∀ yb yb' yb'', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb'' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb'') ∧ ∀ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂), ∀ yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → yb' ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := by
  first | exact @GlobalTheory.QPl.CoupStab.coupIdx_stab | exact GlobalTheory.QPl.CoupStab.coupIdx_stab | (intros; apply GlobalTheory.QPl.CoupStab.coupIdx_stab <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitIdealCompletionAtPlace_eq_integralAdelesAtPlace : ∀ (D : D7) (v : Pl D) (a : AE D), a ∈ idV (1 : FI D) v ↔ a ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.SeeSaw.idV_one_eq_intAt | exact GlobalTheory.SeeSaw.idV_one_eq_intAt | (intros; apply GlobalTheory.SeeSaw.idV_one_eq_intAt <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.twistPlace_normalisedCombinations_preserve_thetaFunctions : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → F.Pins w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQ j) Ψ₁) ∧ IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQT j h) Ψ₂) := by
  first | exact @GlobalTheory.QPl.pins_keep_theta | exact GlobalTheory.QPl.pins_keep_theta | (intros; apply GlobalTheory.QPl.pins_keep_theta <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inverseDifferentCompletion_iff_characterDual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (v : Pl D), ∀ s ∈ idAt D (· = v), s ∈ idV (dI D) v ↔ ∀ o ∈ intAt D (· = v), psiE ψ (s * o) = 1 := by
  first | exact @GlobalTheory.SeeSaw.DiffDual.idV_dI_iff | exact GlobalTheory.SeeSaw.DiffDual.idV_dI_iff | (intros; apply GlobalTheory.SeeSaw.DiffDual.idV_dI_iff <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch.DiffInv

theorem aaD_eq_dI_pow : ∀ (D : D7) (i : Fin D.R.rS), aaD D i = dI D ^ (D.R.rS - i.1) := by
  intro D i
  have hP := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  have hinv : dI D = (ddS D)⁻¹ := by
    rw [GlobalTheory.IntTerm.Conv.ddS_eq]
    exact eq_inv_of_mul_eq_one_left hP
  rw [hinv, inv_pow, aaD, ← Nat.cast_sub i.2.le, _root_.zpow_neg, _root_.zpow_natCast]

end GlobalTheory.Core.Mi.LatMatch.DiffInv
end

section

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

theorem _root_.GlobalTheory.T.twistPrime_rational_coset_sameOrbit_iff_level : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k), AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → ∀ (b : L.β (s + 1)) (hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (e : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e → ∀ z z' : Sp X.E (R.N (s + 1)), (GlobalTheory.QPl.SameOrb ((W.T s R).lev (s + 1) 0 rfl).J (box _ (W.ϖ ^ cst.M)) (Submodule.Quotient.mk fun r => ι (z (e r))) (Submodule.Quotient.mk fun r => ι (z' (e r))) ↔ ∃ κ ∈ (L.levQ (s + 1) b ⟨P.1, hQ⟩).H, ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 z - z') ∈ stdAt X.E (R.N (s + 1)) P.1) := by
  first | exact @GlobalTheory.TwBridge.LevOrb.sameOrb_iff_level | exact GlobalTheory.TwBridge.LevOrb.sameOrb_iff_level | (intros; apply GlobalTheory.TwBridge.LevOrb.sameOrb_iff_level <;> assumption)
end
