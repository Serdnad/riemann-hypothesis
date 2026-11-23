module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle008
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftMatrixComputesLiftRational
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1472
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanGoodEqMj
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle007
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

noncomputable section

open _root_.Formalism.L2.Col

@[reducible] def Base.fields (B : Base) : Fields where
  F := B.host.F
  E := B.host.E
  K := B.LL
  starE := B.host.cmStar
  Tau := Tau B.R
  deTau := Classical.decEq _
  emb := B.tauLL

@[reducible] def Base.primes (B : Base) (X : PreX B.toPre) : Primes B.fields where
  cond := B.host.QS * B.host.q * B.host.d
  g := B.host.g
  piG := X.piG
  Word := B.Word
  deWord := Classical.decEq _
  T := B.T
  piT := X.piT


open Classical in
@[reducible] def Base.wts (B : Base) : Wts B.fields B.Word B.R where
  row := fun τ => RowPar.of (B.hc τ)
  hc := B.hcW
  tops := Finset.univ.filter fun τ : Tau B.R => (τ : B.R.GG) ∈ B.host.topPlaces

@[reducible] def Base.dat (B : Base) (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m) : Dat where
  R := B.R
  X := B.fields
  sig0 := B.embLL
  Pr := B.primes X
  Ch := Ch
  W := B.wts
  a := X.a

namespace Base

variable (B : Base)

theorem fields_star (x : B.host.E) : letI := B.fields.starE; star x = B.host.conj x := bridge_star_holds B.R B.host x

theorem fields_sig (x : B.host.E) : B.fields.sig x = B.host.conj x := bridge_star_holds B.R B.host x

theorem fields_emb_apply (τ : Tau B.R) (x : B.host.E) :
    B.fields.emb τ x = B.embE (B.host.sigmaOf (τ : B.R.GG) x) := rfl

theorem fields_f : B.fields.f = B.R.f := card_Tau B.host

theorem fields_embC (τ : Tau B.R) : B.fields.embC B.embLL τ = B.host.emb (τ : B.R.GG) := by
  unfold Fields.embC Host.emb
  rw [← B.embE_φ₀]
  rfl

theorem fields_conjO_coe (x : 𝓞 B.host.E) :
    ((B.fields.conjO x : 𝓞 B.host.E) : B.host.E) = B.host.conj (x : B.host.E) :=
  B.fields_star (x : B.host.E)

theorem primes_piGCong (X : PreX B.toPre) : (B.primes X).PiGCong := X.piG_cong

theorem primes_piG_norm (X : PreX B.toPre) (i : Fin 2) :
    (B.primes X).piG i * B.fields.conjO ((B.primes X).piG i) = ((B.primes X).g i : 𝓞 B.fields.E) := by
  apply RingOfIntegers.coe_injective
  have h := X.piG_norm i
  rw [← B.fields_conjO_coe] at h
  simpa using h

theorem primes_piT_norm (X : PreX B.toPre) (u : B.Word) :
    (B.primes X).piT u * B.fields.conjO ((B.primes X).piT u) = ((B.primes X).T u : 𝓞 B.fields.E) := by
  apply RingOfIntegers.coe_injective
  have h := X.piT_norm u
  rw [← B.fields_conjO_coe] at h
  simpa using h

theorem mem_wts_tops (τ : Tau B.R) : τ ∈ B.wts.tops ↔ (τ : B.R.GG) ∈ B.host.topPlaces := by
  classical
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem wts_isOk : B.wts.Ok := by
  exact
    { row_ok τ := ⟨B.hc τ, rfl⟩
      hc_row u τ := by
        show RowPar.of (B.hcW u τ) = RowPar.of (B.hc τ)
        unfold RowPar.of
        rw [B.hcW_v, B.hcW_b, B.hcW_e]
      u_first u u' τ h := (B.hcW_first u τ h).trans (B.hcW_first u' τ h).symm
      u_last u u' τ h := (B.hcW_last u τ (by omega)).trans (B.hcW_last u' τ (by omega)).symm }

theorem primes_sizes (X : PreX B.toPre) : Sizes (B.primes X) B.wts X.a := by
  exact
    { g_big i := by rw [B.fields_f]; exact X.g_big i
      T_gt := X.T_gt
      a_gt := by rw [B.fields_f]; exact X.a_gt
      spread_le u j hj τ := by
        unfold Wts.lamTrue
        rw [spread_shiftW]
        exact X.spread_le u j hj τ }

theorem baseData_embedding_conj (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m) (x : (B.dat X Ch).X.K) :
    (B.dat X Ch).sig0 (star x) = starRingEnd ℂ ((B.dat X Ch).sig0 x) := B.starLL_cx x

theorem dat_e_even (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m) (j : Fin (B.dat X Ch).R.m) :
    ∃ z : ℤ, ∑ τ, ((B.dat X Ch).W.row τ).e j = 2 * (z : ℚ) := (X.e_even j).even

end Base

end

end GlobalTheory.Mem
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.MjCoord

theorem closure_image_span {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {V H : Type} [AddCommGroup V]
    [Module (𝓞 K) V] [AddCommGroup H] [Module ℂ H] (f : V →+ H) (hfs : ∀ (b : 𝓞 K) (x : V), f (b • x) = σ (b : K) • f x)
    (X : Set V) :
    AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' X, y = σ (a : K) • x} =
      AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' (Submodule.span (𝓞 K) X : Set V), y = σ (a : K) • x} := by
  set C := AddSubgroup.closure {y | ∃ a : 𝓞 K, ∃ x ∈ f '' X, y = σ (a : K) • x}
  have stab : ∀ (b : 𝓞 K), ∀ z ∈ C, σ (b : K) • z ∈ C := by
    intro b z hz
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨b * a, x, hx, by rw [smul_smul, ← map_mul]; norm_cast⟩
    | zero => rw [smul_zero]; exact C.zero_mem
    | add _ _ _ _ h1 h2 => rw [smul_add]; exact C.add_mem h1 h2
    | neg _ _ h1 => rw [smul_neg]; exact C.neg_mem h1
  have key : ∀ x ∈ Submodule.span (𝓞 K) X, f x ∈ C := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure ⟨1, f x, ⟨x, hx, rfl⟩, by simp⟩
    | zero => rw [map_zero]; exact C.zero_mem
    | add _ _ _ _ h1 h2 => rw [map_add (f := _)]; exact C.add_mem h1 h2
    | smul b x _ h => rw [hfs]; exact stab b _ h
  apply le_antisymm
  · refine AddSubgroup.closure_mono ?_
    rintro _ ⟨a, _, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a, _, ⟨x, Submodule.subset_span hx, rfl⟩, rfl⟩
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨a, _, ⟨x, hx, rfl⟩, rfl⟩
    rw [← hfs]
    exact key _ (Submodule.smul_mem _ a hx)

theorem majAt_self {K : Type} [Field K] [NumberField K] {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x x =
      ((Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v x) ^ 2 : ℝ) : ℂ) := by
  rw [Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Formalism.HermitianLatticesTheory.majAt]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

theorem norm_w0C_sq {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) (b : Bool)
    (hk : X.KForm b) (he : X.EWnorm b) (j : Bs.J) (x : Fin (X.dW b j) → K) :
    ‖X.w0C b j (cpt Bs.v0.embedding x)‖ ^ 2 =
      X.nP b * Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) (X.XW b j) Bs.v0 x) ^ 2 := by
  have h1 := majAt_gram (X.XW b j) Bs.v0 (X.bW b j Bs.v0) (hk j Bs.v0).1 rfl x x
  have h2 := he j (lin (X.bW b j Bs.v0) (cpt Bs.v0.embedding x)) (lin (X.bW b j Bs.v0) (cpt Bs.v0.embedding x))
  rw [← h1, majAt_self, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ((‖X.w0C b j (cpt Bs.v0.embedding x)‖ ^ 2 : ℝ) : ℂ) =
      ((X.nP b * Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K _) (X.XW b j) Bs.v0 x) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, ← h2, Complex.ofReal_pow]
    rfl
  exact Complex.ofReal_injective h3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}



theorem eW_jW_eq (Z : ReadL R F X0 Y) (i : Fin D.R.m) (y) :
    Y.mj.eW i (Z.jW i y) = GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i y :=
  (Z.jW_read i y).trans (congrArg ((R.FW i).j (sg0 D A3.A)) (Fintype.linearCombination_apply _ _ _))

theorem eW_inj (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (i : Fin D.R.m) : Function.Injective (Y.mj.eW i) :=
  GlobalTheory.Mem.LiftForms.inj_of_norm_sq _ (RealDat.nP_pos (F := F.lv2) false) (Y.mj.eW_norm i)

theorem jW_basis (Z : ReadL R F X0 Y) (hH : Holds R F) (i : Fin D.R.m) :
    LinearIndependent ℂ (fun k => Z.jW i (Pi.single k 1)) ∧
      Submodule.span ℂ (Set.range fun k => Z.jW i (Pi.single k 1)) = ⊤ := by
  have he := eW_inj Y i
  have hc : (Y.mj.eW i ∘ fun k => Z.jW i (Pi.single k 1)) = fun k =>
      GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i (Pi.single k 1) :=
    funext fun k => eW_jW_eq Z i _
  refine ⟨LinearIndependent.of_comp (Y.mj.eW i) ?_, ?_⟩
  · rw [hc]; exact GlobalTheory.Mem.LiftTheta.goodForm_li R.toRealDat F.lv2 hH.prim.unif false i
  · apply Submodule.map_injective_of_injective he
    rw [Submodule.map_top, Submodule.map_span, ← Set.range_comp, hc]
    exact (GlobalTheory.Mem.LiftTheta.goodForm_span R.toRealDat F.lv2 false i).trans
      ((hH.aux.levelW false i _).trans (Y.mj.eW_range i).symm)

theorem chiKs (hP : Pins R F cG) (i : Fin D.R.m) : (R.FW i).ChiKs := by
  intro g
  have hL := hP.char.base.lev
  have h : ((Formalism.IndefR.FWT.chiC R.toRealDat i g : ℂˣ) : ℂ) ∈ (D.what₂.embLL.comp (algebraMap Ks D.what₂.LL)).fieldRange := by
    unfold Formalism.IndefR.FWT.chiC
    rw [Units.coe_prod]
    refine prod_mem fun PP _ => ?_
    refine GlobalTheory.ChiDetValues.res_mem _ _ _ (hL.mu0 i) (fun x hx => ?_) _ _ (hL.chi i _ PP.2) _
    obtain ⟨y, hy⟩ := hP.keep.valKs i x hx
    exact ⟨y, hy.symm⟩
  obtain ⟨y, hy⟩ := h
  exact ⟨y, D.what₂.embLL.injective (hy.trans ((Units.coe_prod _ _).trans (hP.char.base.grp.chiW i g).symm))⟩



theorem jW_lat (Z : ReadL R F X0 Y) (hP : Pins R F cG) (hH : Holds R F) (i : Fin D.R.m) :
    OLatTie D.what₂.embLL (D.what₂.MjLat ((i : ℕ) + 1)) (Z.jW i) ((s0Of R F).M i) := by
  have he := eW_inj Y i
  have hli := (jW_basis Z hH i).1
  have hej := eW_jW_eq Z i
  have hI := hH.aux.integral i
  have hspan := GlobalTheory.GoodLatDescent.span_MK_good (R.FW i) hI.1 (fun g f => (hI.2.2 g f).1)
    (chiKs hP i) F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)
    (fun p => ?_) hP.keep.levKs.2
  swap
  · obtain ⟨y, hy⟩ := hP.keep.levKs.1 p
    exact ⟨y⁻¹, by rw [map_inv₀, hy, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]; rfl⟩
  have hsg : sg0 D A3.A = D.what₂.embLL := RingHom.ext fun a => by rw [sg0, sgAt_mk _ R.hv0]
  have himg : Y.mj.eW i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier =
      (R.FW i).j (sg0 D A3.A) '' {y | y ∈ (R.FW i).MK ∧ y ∈ (R.FW i).Wgood F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g)} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy1, hy2, e⟩ := (Y.mj.eW_lat i x).1 hx
      exact ⟨y, ⟨hy1, hy2⟩, e.symm⟩
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hyM : y ∈ (R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) := by
        rw [← hspan]; exact Submodule.subset_span ⟨hy1, hy2⟩
      obtain ⟨c, -, hcy⟩ := (GlobalTheory.Mem.LiftTheta.mem_image_iff R.toRealDat F.lv2 false i _).1 ⟨y, hyM, rfl⟩
      exact ⟨Z.jW i c, (Y.mj.eW_lat i _).2 ⟨y, hy1, hy2, (hej c).trans hcy⟩, (hej c).trans hcy⟩
  refine GlobalTheory.Mem.LiftTheta.oLatTie_of_closure (fun a => ⟨⟨D.what₂.OtoLL a, D.O_int a⟩, rfl⟩) _ (Y.mj.eW i) he (Z.jW i)
    (GlobalTheory.Mem.LiftTheta.semi_injective _ hli) _
    ((R.FW i).j (sg0 D A3.A) '' ((R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A3.A.X).coeff g) : Set _)) (fun y => ?_) ?_
  · refine (GlobalTheory.Mem.LiftTheta.mem_image_iff R.toRealDat F.lv2 false i y).trans ?_
    exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, (hej x).trans h⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, (hej x).symm.trans h⟩⟩
  · rw [himg, ← hspan]
    exact closure_image_span (σ := D.what₂.embLL) ((R.FW i).j (sg0 D A3.A)).toAddMonoidHom
      (fun b x => by
        rw [← hsg]
        show (R.FW i).j _ (b • x) = _
        rw [← algebraMap_smul D.what₂.LL b x, map_smulₛₗ]
        rfl) _



theorem jW_norm (Z : ReadL R F X0 Y) (hH : Holds R F) (i : Fin D.R.m) (x : Fin ((s0Of R F).dW i) → D.what₂.LL) :
    Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun D.what₂.LL _) ((s0Of R F).XW i) (InfinitePlace.mk D.what₂.embLL) x) =
      ‖Z.jW i x‖ := by
  have h1 := norm_w0C_sq (R.toCx3 F) false (RealDat3.kForm_of hH.prim.unif false) (RealDat3.ewNorm false) i x
  have h2 : (R.toCx3 F).w0C false i (cpt A3.A.v0.embedding x) =
      Tw.mk (twAt D.what₂.embLL A3.A.v0) (GlobalTheory.Mem.LiftTheta.goodForm R.toRealDat F.lv2 false i x) :=
    GlobalTheory.Mem.LiftTheta.liftWeight_complexPoint_eq_twist R.toRealDat F.lv2 false i x
  have h3 : ‖(R.toCx3 F).w0C false i (cpt A3.A.v0.embedding x)‖ = ‖Y.mj.eW i (Z.jW i x)‖ :=
    (congrArg norm h2).trans (congrArg norm (eW_jW_eq Z i x)).symm
  have h4 := Y.mj.eW_norm i (Z.jW i x)
  have h5 : RealDat.nP F.lv2 false *
      Formalism.HermitianLatticesTheory.cnorm (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun D.what₂.LL _) ((s0Of R F).XW i) A3.A.v0 x) ^ 2 =
        RealDat.nP F.lv2 false * ‖Z.jW i x‖ ^ 2 := by
    rw [← h4, ← h3]
    exact h1.symm
  rw [← R.hv0]
  exact (sq_eq_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).1
    (mul_left_cancel₀ (RealDat.nP_pos (F := F.lv2) false).ne' h5)

end GlobalTheory.Mem.R3.MjCoord

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

def GeoExV (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (C : Formalism.L2.Pj.CoreJ D) [Algebra C.Q.c.F D.what₂.LL]
    (F : Face D A3.A) : Prop :=
  ∀ (R : RealDat D A3.A C.Q.c.F) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Formalism.L2.Host.ValLL D R.C → GlobalTheory.RealGeo.PreChar R → R.grp_levels F → C.pb = R.C.P.pb →
    Keep (A3 := A3) R F cG → ∃ dict mu chiW x₀ cE nW FW,
      (R.upd5 nW FW R.mu R.twPl R.err0).grp_chiW ∧
      Nonempty (@GlobalTheory.RealGeo.GeoHalf D G _ _ Pl0 T A3.A (GlobalTheory.RealGeo.reCore C dict mu chiW x₀ cE)
        (inferInstanceAs (Algebra C.Q.c.F D.what₂.LL)) (R.upd5 nW FW R.mu R.twPl R.err0) fun _ => 1) ∧
      ∀ i x, ∃ y, (FW i).j (sg0 D A3.A) y = R.thG i A3.A.μ0 (R.jV i A3.A.μ0 x)

end GlobalTheory.Mem.R3
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

namespace GlobalTheory.AtMember

variable {D : D7}

structure CorePin (J : Core D) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop where
  laws : LawsCore J
  canon : J.Q.Canon
  rank : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q
  pb : J.pb = pb

theorem CorePin.reCore {J : CoreJ D} {pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)} (h : CorePin J.toCore pb) {dict mu chiW x₀ cE}
    (hM : LawsM (GlobalTheory.RealGeo.reCore J dict mu chiW x₀ cE).toCore) : CorePin (GlobalTheory.RealGeo.reCore J dict mu chiW x₀ cE).toCore pb :=
  ⟨⟨hM, h.laws.cuspMul, h.laws.latZ, h.laws.cuNe, h.laws.expo⟩, h.canon, h.rank, h.pb⟩

structure FieldTies (D : D7) (C : Formalism.L2.Host.CharFrame D) : Prop where
  one : FieldOK0 D D.host.pde
  two : FieldOK0 D D.host.pde'
  del : ∀ x, ((C.del.1 x : ℂˣ) : ℂ) ∈ FO D
  del' : ∀ x, ((C.del'.1 x : ℂˣ) : ℂ) ∈ FO D
  small : ∀ L : ℝ, HostSz D.host L → Sz (FO D) (poR D.R L) (poR D.R L)

def HalfAt (EX : ErrX D) (C : Formalism.L2.Host.CharFrame D) : Prop :=
  ∀ k, barE D (EX.piG k) ∈ (C.P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def NumAtL (L : SizeData₂ D) (x : ℝ) : Prop :=
  DV.KapDef D ∧ (∃ (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm), GlobalTheory.BigOn.PageNum Tp x) ∧ FieldSmall D L

end GlobalTheory.AtMember
end
end
