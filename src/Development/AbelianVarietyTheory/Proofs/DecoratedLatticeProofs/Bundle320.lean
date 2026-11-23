module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle231
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle312
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle287
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftsAllChartsEqClassSum
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.TwistIndex

open Classical

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (g : GL (Fin n) κ) : Formalism.L2.DIV.upperLeftBlock (le_refl n) g = g := by
  have hg : g ∈ (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 n) : Subgroup (GL (Fin n) κ)) := by
    show (g : Matrix (Fin n) (Fin n) κ).BlockTriangular _
    intro i j hij
    simp [Formalism.L2.DIV.blk2] at hij
  apply Units.ext
  rw [Formalism.L2.DIV.upper_block_val_submatrix _ hg]
  ext i j
  simp [Fin.castLE]

variable {D : D7}

theorem mem_datY_iff (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {r t j : ℕ} (hr hr' : r ≤ V.rank) (Pg Q : Finset (Pl D.host.E))
    (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x : GL (Fin V.rank) (Lev.EAf D)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ↔
      x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr' Pg ∅ (LevelP.triv _ _ _) χ' ξ' Lev.Frm.B) ∧
        ∀ PP ∈ Q, Formalism.L2.DIV.redFn β PP x ∈ (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) : Subgroup (GL (Fin V.rank) (kP PP))) := by
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, h5⟩, fun PP hP => ?_⟩
    · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)
    · exact (Formalism.L2.DIV.mem_parah.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 PP) hP)).2
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h5⟩, h6⟩
    refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, h5⟩
    exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Formalism.L2.DIV.mem_parah.2 ⟨h2, h6 PP hP⟩

theorem relIndex_twist : ∀ (D : D7) (c : Com D) (w : Twist D) (j : ℕ) (s : PiLocalization₂ D), w.Is c → j ≤ D.R.m → IsStage c w j s → ∀ hr χ ξ, Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L ≤ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ∧ (((Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L).relIndex (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B)) : ℕ) : ℝ) = ∏ PP ∈ w.Q, idxQ PP j := by
  intro D c w j s hw _ hs hr' χ ξ
  obtain ⟨hr, hL, hflat⟩ := hs
  rw [hL]
  have hmem := fun x => mem_datY_iff s.V s.β hr hr' w.Pg w.Q w.chi χ w.ξ ξ (r := D.R.r) (t := D.R.t) (j := j) x
  refine ⟨fun x hx => ((hmem x).1 hx).1, ?_⟩
  have hSt : Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ≤
      Formalism.L2.DIV.St s.β := fun x hx => Formalism.L2.DIV.parLev_St hx.1
  let φ : Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) →*
      (∀ PP : w.Q, GL (Fin s.V.rank) (kP PP.1)) :=
    MonoidHom.pi fun PP => (Formalism.L2.DIV.redAt s.β PP.1).comp (Subgroup.inclusion hSt)
  have hφ : ∀ x PP, φ x PP = Formalism.L2.DIV.redFn s.β PP.1 x.1 := by
    intro x PP
    unfold Formalism.L2.DIV.redFn
    rw [Formalism.L2.DIV.extendOne_of_mem _ (hSt x.2)]
    rfl
  have hcomap : (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B)).subgroupOf
      (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B)) =
      (Subgroup.pi Set.univ fun PP : w.Q =>
        (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r) : Subgroup (GL (Fin s.V.rank) (kP PP.1)))).comap φ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hmem]
    simp only [hφ]
    constructor
    · rintro ⟨-, h⟩ PP -
      exact h PP.1 PP.2
    · intro h
      exact ⟨x.2, fun PP hP => h ⟨PP, hP⟩ (Set.mem_univ _)⟩
  have hsurj : Function.Surjective φ := by
    intro g
    obtain ⟨N, hN, -⟩ := hflat.base
    obtain ⟨e, he⟩ := hw.com.split
    have hnc := GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he
    let L' : LevDat D.host.E ℂ s.V.rank := Lev.datW s.V.rank c.Pg (LevelP.triv c.Pg s.V.rank ℂ) Lev.Frm.B
    have hlift : Lev.LiftsExist s.V s.β L' :=
      GlobalTheory.ParahoricLift.liftsExist s.V s.β L' s.Λ N hN (fun PP hP PP' hP' => by
        rcases hP' with h | h
        · exact hnc PP hP PP' h
        · exact absurd h (Finset.notMem_empty _)) (Finset.disjoint_empty_right _)
    let g0 : Formalism.L2.DIV.G0 L'.Pg L'.r := fun PP => if h : PP.1 ∈ w.Q then g ⟨PP.1, h⟩ else 1
    have h0 := hlift g0
    have hκ := h0.choose_spec
    have hκ1 : Lev.finE s.V h0.choose ∈ Formalism.L2.DIV.parLev D.sp.cm s.V.gram s.β L' := hκ.2.1
    have hκ2 : Formalism.L2.DIV.rTup s.β L' (Lev.finE s.V h0.choose) = g0 := hκ.2.2
    have hred : ∀ PP (h : PP ∈ c.Pg), Formalism.L2.DIV.redFn s.β PP (Lev.finE s.V h0.choose) = g0 ⟨PP, h⟩ := by
      intro PP h
      exact (restrictedBlock_self_apply _).symm.trans (congrFun hκ2 ⟨PP, h⟩)
    have hPg : ∀ PP ∈ w.Pg, Formalism.L2.DIV.redFn s.β PP (Lev.finE s.V h0.choose) = 1 := by
      intro PP hP
      have hc : PP ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_left _ hP
      rw [hred PP hc]
      have hq : PP ∉ w.Q := Finset.disjoint_left.1 hw.disj hP
      show (if h : PP ∈ w.Q then g ⟨PP, h⟩ else (1 : GL (Fin s.V.rank) (kP PP))) = 1
      exact dif_neg hq
    have hSt' := Formalism.L2.DIV.parLev_St hκ1
    have hxbig : Lev.finE s.V h0.choose ∈
        Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) := by
      refine ⟨⟨⟨⟨Formalism.L2.DIV.parLev_UA hκ1, hSt'⟩, ?_⟩, ?_⟩, ?_⟩
      · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP =>
          Formalism.L2.DIV.mem_parah.2 ⟨hSt', by rw [hPg PP hP]; exact Subgroup.one_mem _⟩
      · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)
      · show Formalism.L2.DIV.rTup s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) (Lev.finE s.V h0.choose) ∈
          (⊥ : Subgroup (Formalism.L2.DIV.G0 w.Pg D.R.r))
        refine Subgroup.mem_bot.2 (funext fun PP => ?_)
        show Formalism.L2.DIV.upperLeftBlock hr' (Formalism.L2.DIV.redFn s.β PP.1 (Lev.finE s.V h0.choose)) = 1
        rw [hPg PP.1 PP.2]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    refine ⟨⟨_, hxbig⟩, funext fun PP => ?_⟩
    rw [hφ]
    have hc : PP.1 ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_right _ PP.2
    rw [hred PP.1 hc]
    show (if h : PP.1 ∈ w.Q then g ⟨PP.1, h⟩ else 1) = g PP
    rw [dite_eq_left PP.2]
  have hn : s.V.rank = D.R.r + j * D.R.t := hflat.rank
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, index_pi_univ, Nat.cast_prod]
  refine Eq.trans ?_ (Finset.prod_coe_sort w.Q (fun PP => idxQ PP j))
  refine Finset.prod_congr rfl fun PP _ => ?_
  refine (GlobalTheory.ParabIndex.index_maxParabolic_GL_finiteField (kP PP.1) s.V.rank D.R.r (j * D.R.t) hn).trans ?_
  have hq : Nat.card (kP PP.1) = Ideal.absNorm PP.1.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hq, hn]
  rfl

end GlobalTheory.TwistIndex

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LatIndHalf

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_one (p : SplitPt D k) : p.sec 1 = p.e := by
  rw [← map_one p.pr, p.sec_pr, mul_one]

theorem e_mul_sec (p : SplitPt D k) (a : k) : p.e * p.sec a = p.sec a := by
  rw [← p.sec_pr, p.pr_sec]

theorem sec_mul (p : SplitPt D k) (a b : k) : p.sec (a * b) = p.sec a * p.sec b :=
  calc p.sec (a * b) = p.sec (p.pr (p.sec a * p.sec b)) := by rw [map_mul p.pr, p.pr_sec, p.pr_sec]
    _ = p.e * (p.sec a * p.sec b) := p.sec_pr _
    _ = p.sec a * p.sec b := by rw [← mul_assoc, e_mul_sec]

theorem e_mem_idAt (p : SplitPt D k) : p.e ∈ idAt D (· = p.v) := by
  obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem p
  obtain ⟨α, rfl, -, h0⟩ := hε
  have hmem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ idAt D (· = p.v) := by
    rw [show algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) from rfl]
    unfold idAt
    rw [Submodule.mem_inf, RingHom.mem_ker, Submodule.mem_iInf]
    refine ⟨?_, fun w => RingHom.mem_ker.2 ?_⟩
    · change fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · change evalV D.host.F w.1 α ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  rw [← heε]
  exact Ideal.mul_mem_right _ _ hmem

theorem mul_mem_latV {S : HSp D} {L : Lat S} {P : Pl D → Prop} {w : AE D} (hw : finPart D w ∈ intAE D)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : (fun i => w * y i) ∈ latV S L P := by
  let Ψ : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) :=
    AddMonoidHom.mk' (fun y i => w * y i) fun a b => funext fun i => mul_add w (a i) (b i)
  have main : latV S L P ≤ (latV S L P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) :=
      AddMonoidHom.mk' (fun c i => GlobalTheory.LatticeStable.liftFin D (c * (β ⊗ₜ[D.host.F] (1 * x i))))
        fun c c' => funext fun i => by rw [add_mul, LinearMap.map_add (f := _)]; rfl
    have hle : intAE D ≤ (latV S L P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨γ, hγ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨γ * β, fun v => by rw [map_mul]; exact mul_mem (hγ v) (hβi v),
        fun v hv => by rw [map_mul, hβ v hv, mul_zero], 1, rfl, o • x, L.smul_mem o hx, ?_⟩
      funext i
      change GlobalTheory.LatticeStable.liftFin D ((γ ⊗ₜ[D.host.F] (o : D.host.E)) * (β ⊗ₜ[D.host.F] (1 * x i))) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
        show algebraMap (𝓞 D.host.E) D.host.E o = (o : D.host.E) from rfl]
      congr 1
      ring
    have e : Ψ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) = Φ (finPart D w) :=
      funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D w β _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact main hy

variable {p : SplitPt D k} {S T : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem mulVec_sec (α : Frame p S n') (β : Frame p T n) {t : WO S T} (ht : IsHalf p.e t) (x : n' → k) :
    t *ᵥ (fun j => p.sec ((α.b *ᵥ x) j)) = fun i => p.sec ((β.b *ᵥ (rd α β t *ᵥ x)) i) := by
  have hM : (β.b * rd α β t * α.b') *ᵥ (α.b *ᵥ x) = β.b *ᵥ (rd α β t *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc (β.b * rd α β t), α.b'b, Matrix.mul_one, Matrix.mulVec_mulVec]
  rw [← hM]
  funext i
  conv_lhs => rw [← GlobalTheory.FinPl.HalfInd.wr_rd α β ht]
  simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.HalfInd.wr_apply]

  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => (sec_mul p _ _).symm

theorem mem_latO_iff_rd (α : Frame p S n') (β : Frame p T n) {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS)
    (hT : IsSelfDualC T LT) (hU : p.UnitAA) {ΛS : Submodule 𝒪[k] (n' → k)} {ΛT : Submodule 𝒪[k] (n → k)}
    (hα : α.IsLat LS ΛS) (hβ : β.IsLat LT ΛT) {t : WO S T} (ht : IsHalf p.e t) :
    t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ↔ ∀ x ∈ ΛS, rd α β t *ᵥ x ∈ ΛT := by
  have hmem := GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = p.v) t
  rw [hU.2 T LT] at hmem
  constructor
  · intro h x hx
    have h1 : t *ᵥ (fun j => p.sec ((α.b *ᵥ x) j)) ∈ latV T LT (· = p.v) := (hmem.1 h).2 _ ((hα x).1 hx)
    rw [mulVec_sec α β ht] at h1
    exact (hβ _).2 h1
  · intro h
    refine hmem.2 ⟨fun i j => ?_, fun y hy => ?_⟩
    · rw [← ht i j]
      exact Ideal.mul_mem_right _ _ (e_mem_idAt p)
    · have hy' : t *ᵥ y = t *ᵥ (fun j => p.e * y j) := by
        funext i
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_assoc, mul_comm (t i j) p.e, ht i j]
      have hey : (fun j => p.e * y j) = fun j => p.sec ((α.b *ᵥ (α.b' *ᵥ fun j => p.pr (y j))) j) := by
        funext j
        rw [Matrix.mulVec_mulVec, α.bb', Matrix.one_mulVec, p.sec_pr]
      have hint : finPart D p.e ∈ intAE D := by
        rw [← sec_one p]
        exact (p.int_iff 1).1 (one_mem _)
      have hx : α.b' *ᵥ (fun j => p.pr (y j)) ∈ ΛS := (hα _).2 (hey ▸ mul_mem_latV hint hy)
      show t *ᵥ y ∈ latV T LT (· = p.v)
      rw [hy', hey, mulVec_sec α β ht]
      exact (hβ _).1 (h _ hx)

end GlobalTheory.FinPl.LatIndHalf

theorem GlobalTheory.FinPl.LatIndHalf.extFun_latInd_eq_halfInd : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → p.UnitAA → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → extFun α β (latInd ΛS ΛT) = halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT hU ΛS ΛT hα hβ
  funext t
  unfold extFun halfInd
  by_cases ht : IsHalf p.e t
  · rw [if_pos ht]
    unfold latInd
    have key := GlobalTheory.FinPl.LatIndHalf.mem_latO_iff_rd α β hS hT hU hα hβ ht
    by_cases h : t ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v)
    · rw [if_pos (key.1 h), if_pos ⟨h, ht⟩]
    · rw [if_neg fun h' => h (key.2 h'), if_neg fun h' => h h'.1]
  · rw [if_neg ht, if_neg fun h => ht h.2]

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LocProd

variable {D : D7}

theorem mem_congGrp_entries (V : HSp D) (I : Ideal (AE D)) (g : GA D V) :
    g ∈ congGrp V I ↔ ∀ i j, (Formalism.L2.Theta.mt V g - 1) i j ∈ I := by
  rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff]
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map, Units.val_one]
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
  change ((matHom V g).1.map (Ideal.Quotient.mk I)) i j = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D ⧸ I)) i j ↔ _
  rw [Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, map_one]
    rfl
  · simp only [Matrix.one_apply_ne hij, map_zero]
    rfl

theorem congGrp_mono (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J := fun g hg =>
  (mem_congGrp_entries V J g).2 fun i j => h ((mem_congGrp_entries V I g).1 hg i j)

theorem idAt_le_idOff (P P' : Pl D → Prop) (h : ∀ w, P w → ¬ P' w) : idAt D P ≤ idOff D P' := by
  intro a ha
  have h2 := (Submodule.mem_inf.1 ha).2
  rw [Submodule.mem_iInf] at h2
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]
  intro w hw
  exact h2 ⟨w, fun h' => h w h' hw⟩

theorem grpAt_le_grpOff' (V : HSp D) (P P' : Pl D → Prop) (h : ∀ w, P w → ¬ P' w) : grpAt V P ≤ grpOff V P' :=
  congGrp_mono V (idAt_le_idOff P P' h)

theorem mem_idOff_of_forall (P : Pl D → Prop) (a : AE D) (h : ∀ w, P w → a ∈ idOff D (· = w)) : a ∈ idOff D P := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at h ⊢
  intro w hw
  exact h w hw w rfl

theorem mem_grpOff_of_forall (V : HSp D) (P : Pl D → Prop) (g : GA D V) (h : ∀ w, P w → g ∈ grpOff V (· = w)) :
    g ∈ grpOff V P := by
  unfold grpOff
  rw [mem_congGrp_entries]
  intro i j
  exact mem_idOff_of_forall P _ fun w hw => (mem_congGrp_entries V _ g).1 (h w hw) i j

theorem map_list_prod_eq_one {ι G H : Type*} [Monoid G] [Monoid H] (φ : G →* H) (f : ι → G) :
    ∀ J : List ι, (∀ i ∈ J, φ (f i) = 1) → φ (J.map f).prod = 1
  | [], _ => by simp
  | a :: J, h => by
    rw [List.map_cons, List.prod_cons, map_mul, h a List.mem_cons_self,
      map_list_prod_eq_one φ f J fun i hi => h i (List.mem_cons_of_mem a hi), one_mul]

theorem map_list_prod_single {ι G H : Type*} [Monoid G] [Monoid H] (φ : G →* H) (f : ι → G) (j : ι)
    (h1 : ∀ i, i ≠ j → φ (f i) = 1) : ∀ J : List ι, J.Nodup → j ∈ J → φ (J.map f).prod = φ (f j)
  | [], _, hj => absurd hj List.not_mem_nil
  | a :: J, hn, hj => by
    have ha : a ∉ J := List.Nodup.notMem hn
    have hn' : J.Nodup := List.Nodup.of_cons hn
    rw [List.map_cons, List.prod_cons, map_mul]
    by_cases haj : a = j
    · subst haj
      rw [map_list_prod_eq_one φ f J fun i hi => h1 i fun e => ha (e ▸ hi), mul_one]
    · have hjJ : j ∈ J := by
        rcases List.mem_cons.1 hj with e | e
        · exact absurd e.symm haj
        · exact e
      rw [h1 a haj, one_mul, map_list_prod_single φ f j h1 J hn' hjJ]

theorem eq_prod_gl_mul_off : ∀ (D : D7) (S : HSp D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n), Function.Injective (fun i => (p i).v) → ∀ J : List ι, J.Nodup → (∀ i, i ∈ J) → ∀ κ : GA D S, ∃ g : ι → GL n k, (∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v)) ∧ ∃ κ' ∈ grpOff S (fun x => ∃ i, x = (p i).v), κ = (J.map fun i => (β i).gl (g i)).prod * κ' := by
  intro D S k _ _ _ _ ι p n _ _ β hinj J hJ hall κ
  have hloc := fun i => ((GlobalTheory.FinPl.localComponents D (· = (p i).v)).2 S).1 κ
  have hcomm := fun i => ((GlobalTheory.FinPl.localComponents D (· = (p i).v)).2 S).2.1
  choose x hx y hy hxy using hloc
  have hfr := fun i => ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n (β i)).1 (x i)).1 (hx i)
  choose g hg using hfr
  have hglAt : ∀ i, (β i).gl (g i) ∈ grpAt S (· = (p i).v) := fun i =>
    ((GlobalTheory.T.splitPlaceHermitianFrame_properties D k (p i) S n (β i)).1 _).2 ⟨g i, rfl⟩
  have key : ∀ i, κ * ((β i).gl (g i))⁻¹ ∈ grpOff S (· = (p i).v) := by
    intro i
    rw [← hg i, hxy i, hcomm i (x i) (hx i) (y i) (hy i), mul_assoc, mul_inv_cancel, mul_one]
    exact hy i
  refine ⟨g, key, (J.map fun i => (β i).gl (g i)).prod⁻¹ * κ, ?_, (mul_inv_cancel_left _ _).symm⟩
  apply mem_grpOff_of_forall
  rintro w ⟨j, rfl⟩
  let φ := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (idOff D (· = (p j).v)))).comp (matHom S)
  have hker : ∀ h, h ∈ grpOff S (· = (p j).v) ↔ φ h = 1 := fun h => MonoidHom.mem_ker
  have hκ : φ κ = φ ((β j).gl (g j)) := by
    have := (hker _).1 (key j)
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    exact this
  have h1 : ∀ i, i ≠ j → φ ((β i).gl (g i)) = 1 := fun i hij =>
    (hker _).1 (grpAt_le_grpOff' S _ _ (fun w hw hw' => hij (hinj (hw.symm.trans hw'))) (hglAt i))
  rw [hker, map_mul, map_inv, map_list_prod_single φ (fun i => (β i).gl (g i)) j h1 J hJ (hall j), hκ, inv_mul_cancel]

end GlobalTheory.FinPl.LocProd

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

namespace GlobalTheory.IwaPlace

variable {D : D7}

theorem flag_times_stab : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → IsSelfDualC S₀ L₀ → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ p ∈ grpAt S (· = v), (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S p ⬝ d.jX = d.jX ⬝ a) ∧ Moves S (p⁻¹ * h) L L (· = v) := by
  intro D S S₀ ρ d L L₀ v hT hL hL₀ hM h hh
  obtain ⟨q, hq, ⟨a, ha, hqa⟩, Λ₀, hΛ, hz⟩ := GlobalTheory.T.exists_flag_stabiliser_move_lattice_split_witt D S S₀ ρ d L L₀ v hT (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D S L v hL) hM h hh
  obtain ⟨γ, hγ, hγL⟩ := GlobalTheory.T.selfDualLattices_single_orbit_tamePlace D S₀ v _ Λ₀ hT (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D S₀ L₀ v hL₀) hΛ
  refine ⟨q * d.emb0 γ, mul_mem hq (wittCoreEmbedding_preserves_supportedUnitarySubgroup d hγ), ⟨a, ha, ?_⟩, ?_⟩
  · rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, hqa]
  · intro y hy
    obtain ⟨z, hzdef⟩ : ∃ z, z = mt S ((q * d.emb0 γ)⁻¹ * h) *ᵥ y := ⟨_, rfl⟩
    rw [← hzdef]
    have hzI : ∀ i, z i ∈ idAt D (· = v) := by rw [hzdef]; exact mulVec_mem_idAt _ hy
    have hw : y = mt S (h⁻¹ * q) *ᵥ (mt S (d.emb0 γ) *ᵥ z) := by
      rw [hzdef, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mt_mul, ← mt_mul]
      have : h⁻¹ * q * d.emb0 γ * ((q * d.emb0 γ)⁻¹ * h) = 1 := by group
      rw [this, mt_one, Matrix.one_mulVec]
    have key := hz (mt S (d.emb0 γ) *ᵥ z) (mulVec_mem_idAt _ hzI)
    rw [← hw] at key
    rw [key, hM z, Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding, Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding, Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding,
      ← Matrix.mulVec_mulVec, ← hγL _ (mulVec_mem_idAt _ hzI)]

theorem iwasawa_at_place : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → IsSelfDualC S₀ L₀ → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ n ∈ flagN d, n ∈ grpAt S (· = v) ∧ ∃ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) ∧ d.levi t ∈ grpAt S (· = v) ∧ ∃ γ ∈ grpAt S₀ (· = v), ∃ κ, InK S L (· = v) κ ∧ h = n * d.levi t * d.emb0 γ * κ := by
  intro D S S₀ ρ d L L₀ v hT hL hL₀ hM h hh
  obtain ⟨p, hp, hflag, hmv⟩ := flag_times_stab D S S₀ ρ d L L₀ v hT hL hL₀ hM h hh
  obtain ⟨n, hn, hnv, t, ht, htv, γ, hγ, hpe⟩ := GlobalTheory.T.flagStabilizer_eq_unipotent_torus_levi_atPlace D S S₀ ρ d v p hp hflag
  refine ⟨n, hn, hnv, t, ht, htv, γ, hγ, p⁻¹ * h, ⟨mul_mem (inv_mem hp) hh, hmv⟩, ?_⟩
  rw [← hpe]; group

end GlobalTheory.IwaPlace

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.thetaLifts_all_charts_eq_classSum : ∀ (D : D7) (c : Comm D) (ρ : RealD c), c.Is → ρ.Is → ∀ j (hj : j + 1 ≤ D.R.m) (hab : ρ.N j ≤ ρ.N (j + 1)), BorelSpace (GinfC (c.X j)) ∧ ∃ ν : Measure (GinfC (c.X j)), IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant ∧ ∀ (m : ℕ) (y : Fin m → c.Fr j) (P : Fin m → PolF D (c.X (j + 1)).rank (c.X j).rank) (m' : ℕ) (y' : Fin m' → D.what₂.Tau → Matrix (Fin (ρ.N (j + 1))) (Fin (ρ.N (j + 1))) ℂ) (y'' : Fin m' → c.Fr (j + 1)) (s : Fin m' → ℂ), (∀ i τ, (ρ.fr (j + 1) (y'' i)).1 τ = ρ.sc j τ • y' i τ) → (∀ F ∈ Vn (ρ.lam j) (ρ.n j), ∀ Λ : FP D.what₂.Tau (ρ.N j) (ρ.N (j + 1)) →ₗ[ℂ] ℂ, ∑ i, (∏ τ, ((ρ.fr j (y i)).1 τ).det ^ (-ρ.sS j τ)) * ∫ k, Λ (mvZ (fun τ => (ρ.r j (Nat.le_of_succ_le hj) k.1 τ)⁻¹) (fun _ => 1) (castP (ρ.hN j (Nat.le_of_succ_le hj)) (ρ.hN (j + 1) hj) (P i))) * evalAt (fun τ => ρ.r j (Nat.le_of_succ_le hj) k.1 τ * (ρ.fr j (y i)).1 τ) F ∂ν = ∑ i, s i * Λ (subY hab (y' i) F)) → ∀ (t : Tup c) (A : ClsK ρ t), t.Is → A.Is → ∀ ψ ∈ t.Ram j, ∀ γ, ∑ i, ∑ α, (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) (t.rd j α ψ (y i)) = t.cK j • ∑ i, (s i * ∏ τ, ((ρ.fr (j + 1) (y'' i)).1 τ).det ^ ρ.sD j τ) • t.rd (j + 1) γ (t.K j ψ) (y'' i) := by
  first | exact @GlobalTheory.SeeSaw.lift_eq_classSum | exact GlobalTheory.SeeSaw.lift_eq_classSum | (intros; apply GlobalTheory.SeeSaw.lift_eq_classSum <;> assumption)
end
