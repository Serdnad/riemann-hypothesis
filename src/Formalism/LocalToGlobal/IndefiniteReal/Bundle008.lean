module

public import Formalism.LocalToGlobal.Divisibility.Bundle002
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle001
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.CxCutPO
public import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransfer
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Formalism.LocalToGlobal.IndefiniteReal.MemSpanOfSmulMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.IndefiniteReal.CxCutEP

@[expose] public section

section

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.DIV.CyclotomicLifting Formalism.IndefR.Cx.EigenprojectionMatrices Formalism.IndefR.Cx.OrthogonalPartDecomposition

namespace GroupActionMatrices

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ} {Z : Submodule K B.S.Forms} {I : Type}

def oM (B : BlockDat K G Pl0) (op : I → Module.End K B.S.Forms) (i : I) : Matrix (Fin B.S.dim) (Fin B.S.dim) K :=
  LinearMap.toMatrix B.S.basis B.S.basis (op i)

structure OkOp (B : BlockDat K G Pl0) (op : I → Module.End K B.S.Forms) : Prop where

  rat : ∀ i a b, oM B op i a b ∈ cmMax K

  adj : ∀ i, ∃ i', ∀ f g : B.S.Forms,
    B.S.csum (op i f : B.S.Cl → B.S.V) (g : B.S.Cl → B.S.V) = B.S.csum (f : B.S.Cl → B.S.V) (op i' g : B.S.Cl → B.S.V)

  comm : Col.PairComm op

  split : Col.SplitOver op

  opG : ∀ i g, Commute (op i) (B.r g)

variable {op : I → Module.End K B.S.Forms}

theorem equivFun_oM (i : I) (f : B.S.Forms) :
    B.S.basis.equivFun (op i f) = (oM B op i).mulVec (B.S.basis.equivFun f) := by
  exact equivFun_end (op i) f

theorem oM_comm (hc : Col.PairComm op) (i j : I) : oM B op i * oM B op j = oM B op j * oM B op i := by
  simp only [oM]
  rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, (hc i j).eq]

private theorem okH_of_okOp (hO : OkOp B op) : BlockDat.OkH ({ S := B.S, r := B.r, Pl := I, pl := id, q := fun _ => 1, n := B.n, t := 1, op := fun p => op p.1, bl := [fun _ => 1] } : BlockDat K G I) :=
  { rat := fun p a b => hO.rat p.1 a b
    adj := fun p => by
      obtain ⟨i', hi'⟩ := hO.adj p.1
      exact ⟨(i', 0), hi'⟩ }

theorem oM_adj (hO : OkOp B op) (i : I) : ∃ i', (oM B op i)ᴴ * B.S.H = B.S.H * oM B op i' := by
  obtain ⟨i', hi'⟩ := opMat_adj (okH_of_okOp hO) (i, 0)
  exact ⟨i'.1, hi'⟩

private theorem blockHyp_of_okOp (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) : BlockHyp ({ S := B.S, r := B.r, Pl := I, pl := id, q := fun _ => 1, n := B.n, t := 1, op := fun p => op p.1, bl := [fun _ => 1] } : BlockDat K G I) ℓ v0 s :=
  { conj := h.conj
    irr := h.irr
    ok :=
    { good := h.ok.good
      hrat := h.ok.hrat
      hpos := h.ok.hpos
      act := h.ok.act
      actRat := h.ok.actRat
      comm := fun p q => hO.comm p.1 q.1
      split := fun p => hO.split p.1
      opG := fun p g => hO.opG p.1 g
      blocks := ⟨le_rfl, List.cons_ne_nil _ _, by simp⟩
      q_pos := fun _ => Nat.one_pos
      pl_inj := Function.injective_id } }

private theorem eigSum_prod_nat_eq_eigSum (C : (I → K) → Prop) :
    Col.eigSum (fun p : I × ℕ => op p.1) (fun y => C (fun i => y (i, 0))) = Col.eigSum op C := by
  apply le_antisymm
  · refine iSup₂_le fun y hy => le_trans ?_ (le_iSup₂ (f := fun x (_ : C x) => Col.eigAt op x) _ hy)
    exact le_iInf fun i => iInf_le (fun p : I × ℕ => (op p.1).maxGenEigenspace (y p)) (i, 0)
  · refine iSup₂_le fun x hx => ?_
    have h2 : Col.eigAt op x ≤ Col.eigAt (fun p : I × ℕ => op p.1) (fun p => x p.1) :=
      le_iInf fun p => iInf_le (fun i => (op i).maxGenEigenspace (x i)) p.1
    refine h2.trans ?_
    unfold Col.eigSum
    refine le_trans ?_ (le_iSup _ (fun p : I × ℕ => x p.1))
    exact le_iSup_of_le (show C (fun i => x i) from hx) le_rfl

theorem eig_ratG (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (C : (I → K) → Prop) :
    SubHasRatBasis (B.inV0 ℓ (Col.eigSum op C)) := by
  have h1 := eig_rat (blockHyp_of_okOp h hO) (okH_of_okOp hO) (fun y => C (fun i => y (i, 0)))
  rw [eigSum_prod_nat_eq_eigSum] at h1
  exact h1

def tVg (B : BlockDat K G Pl0) (ℓ : Lvl K G) (op : I → Module.End K B.S.Forms) (i : I) : Matrix (Fin (B.nV ℓ)) (Fin (B.nV ℓ)) K :=
  B.vPr ℓ * oM B op i * B.vE ℓ

theorem vE_tVg (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (i : I) : B.vE ℓ * tVg B ℓ op i = oM B op i * B.vE ℓ := by
  exact vE_tV (blockHyp_of_okOp h hO) (i, 0)

theorem tVg_comm (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (i j : I) : tVg B ℓ op i * tVg B ℓ op j = tVg B ℓ op j * tVg B ℓ op i := by
  exact tV_comm (blockHyp_of_okOp h hO) (i, 0) (j, 0)

theorem Pq_tVg (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (hZ : ∀ i, Z ≤ Z.comap (op i)) (i : I) :
    B.Pq ℓ Z * tVg B ℓ op i = (B.Pq ℓ Z * tVg B ℓ op i * B.zE ℓ Z) * B.Pq ℓ Z := by
  exact Pq_tV (blockHyp_of_okOp h hO) (okH_of_okOp hO) (fun p => hZ p.1) (i, 0)

theorem adjCg (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (σ : K →+* ℂ) (i : I) :
    ∃ i', (B.HV ℓ).map σ * (tVg B ℓ op i).map σ = ((tVg B ℓ op i').map σ)ᴴ * (B.HV ℓ).map σ := by
  obtain ⟨i', hi'⟩ := adjC (blockHyp_of_okOp h hO) (okH_of_okOp hO) σ (i, 0)
  exact ⟨i'.1, hi'⟩

theorem part_orthg (h : BlockHyp B ℓ v0 s) (hO : OkOp B op) (hZ : ∀ i, Z ≤ Z.comap (op i)) (v : InfinitePlace K)
    {C C' : (I → K) → Prop} (hSS : ∀ x, C' x → ¬ C x)
    {x y : Fin (B.dZ ℓ Z) → K} (hx : x ∈ (B.inV0 ℓ (Col.eigSum op C)).comap (B.zE ℓ Z).mulVecLin)
    (hy : y ∈ (B.inV0 ℓ (Col.eigSum op C')).comap (B.zE ℓ Z).mulVecLin) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K _) (B.XQ ℓ Z) v x y = 0 := by
  have hA : ((B.HV ℓ).map v.embedding).PosDef := BlockDat.lf_HV_pos h v
  have hc : Col.PairComm (linF fun i => (tVg B ℓ op i).map v.embedding) := fun i j => by
    refine linF_commute ?_
    have e := congrArg (fun M => M.map v.embedding) (tVg_comm h hO i j)
    simpa only [Matrix.map_mul] using e
  have hs : Col.SplitOver (linF fun i => (tVg B ℓ op i).map v.embedding) := fun i =>
    Module.End.iSup_maxGenEigenspace_eq_top _
  have hcf : Col.PairComm (linF fun i => (oM B op i).map v.embedding) := fun i j => by
    refine linF_commute ?_
    have e := congrArg (fun M => M.map v.embedding) (oM_comm hO.comm i j)
    simpa only [Matrix.map_mul] using e
  have hvv : B.vPr ℓ * B.vE ℓ = 1 := (BlockDat.lf_v_proj h).1.1

  have key : ∀ {D : (I → K) → Prop} {w : Fin (B.dZ ℓ Z) → K},
      w ∈ (B.inV0 ℓ (Col.eigSum op D)).comap (B.zE ℓ Z).mulVecLin →
      (fun a => v.embedding ((B.zE ℓ Z *ᵥ w) a)) ∈ Col.eigSum (linF fun i => (tVg B ℓ op i).map v.embedding)
        (fun y => ∃ x, D x ∧ y = fun i => v.embedding (x i)) := by
    intro D w hw
    have h1 : B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ w) ∈ Col.eigSum (fun i => Matrix.toLin' (oM B op i)) D := by
      have hw' : (B.vE ℓ).mulVecLin ((B.zE ℓ Z).mulVecLin w) ∈ B.coord (Col.eigSum op D) := hw
      obtain ⟨F, hF, hFe⟩ := Submodule.mem_map.1 hw'
      have h3 := eigSum_le_comap_of (B.S.basis.equivFun : B.S.Forms →ₗ[K] (Fin B.S.dim → K)) op
        (fun i => Matrix.toLin' (oM B op i))
        (fun i f => by simp only [LinearEquiv.coe_coe, equivFun_oM, Matrix.toLin'_apply]) D hF
      rw [Submodule.mem_comap, hFe] at h3
      simpa only [Matrix.mulVecLin_apply] using h3
    have h2 := emb_mem_eigSum v.embedding (oM B op) D h1
    refine mem_eigSum_of_emb _ _ ((B.vE ℓ).map v.embedding) ((B.vPr ℓ).map v.embedding)
      (by rw [← Matrix.map_mul, hvv, Matrix.map_one _ (map_zero _) (map_one _)])
      (fun i => by
        have e := congrArg (fun M => M.map v.embedding) (vE_tVg h hO i)
        simpa only [Matrix.map_mul] using e) hc hs hcf _ ?_
    have e : (B.vE ℓ).map v.embedding *ᵥ (fun a => v.embedding ((B.zE ℓ Z *ᵥ w) a)) =
        fun a => v.embedding ((B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ w)) a) := by
      ext a
      exact (RingHom.map_mulVec _ _ _ _).symm
    rw [e]
    exact h2
  have hx' := key hx
  have hy' := key hy
  have hCC : ∀ y, (fun y => ∃ x, C' x ∧ y = fun i => v.embedding (x i)) y →
      ¬ (fun y => ∃ x, C x ∧ y = fun i => v.embedding (x i)) y := by
    rintro y ⟨x', hx1, rfl⟩ ⟨x, hx2, hxx⟩
    have hxe : x = x' := funext fun i => v.embedding.injective (congrFun hxx i).symm
    exact hSS x' hx1 (hxe ▸ hx2)
  have hPN : ∀ i, (B.Pq ℓ Z).map v.embedding * (tVg B ℓ op i).map v.embedding =
      (B.Pq ℓ Z * tVg B ℓ op i * B.zE ℓ Z).map v.embedding * (B.Pq ℓ Z).map v.embedding := fun i => by
    have e := congrArg (fun M => M.map v.embedding) (Pq_tVg h hO hZ i)
    simpa only [Matrix.map_mul] using e
  have hPz : B.Pq ℓ Z * B.zE ℓ Z = 1 := (pq_orth (Z := Z) h).1
  have hPu : ∀ w : Fin (B.dZ ℓ Z) → K,
      (B.Pq ℓ Z).map v.embedding *ᵥ (fun a => v.embedding ((B.zE ℓ Z *ᵥ w) a)) = fun a => v.embedding (w a) := by
    intro w
    ext a
    have e := (RingHom.map_mulVec v.embedding (B.Pq ℓ Z) (B.zE ℓ Z *ᵥ w) a).symm
    rw [Matrix.mulVec_mulVec, hPz, Matrix.one_mulVec] at e
    exact e
  have hq : IsQuotMetric (B.Pq ℓ Z) (B.HV ℓ) (B.XQ ℓ Z) := BlockDat.XQ_quot h.conj h.ok h.irr
  have hvx : ∀ w : Fin (B.dZ ℓ Z) → K,
      Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin (B.dZ ℓ Z))) v w = fun a => v.embedding (w a) := fun w => by
    ext a
    simp [Formalism.HermitianLatticesTheory.vecAt]
  rw [Formalism.HermitianLatticesTheory.majBasic_majAt, (hq v).2, hvx, hvx]
  by_cases hR : IsUnit ((B.Pq ℓ Z).map v.embedding * ((B.HV ℓ).map v.embedding)⁻¹ *
      ((B.Pq ℓ Z).map v.embedding)ᴴ).det
  · have e := cx_quot_orth (hA := hA) (adj := adjCg h hO v.embedding) (hPN := hPN) (hR := hR) (hc := hc)
      (hs := hs) (hCC := hCC) (hu := hx') (hu' := hy')
    rw [hPu, hPu] at e
    exact e
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hR]
    simp

end GroupActionMatrices

end Formalism.IndefR.Cx
end
end

section

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement Formalism.HN _root_.Formalism.IndefR.LatticeTransfer.Lat

theorem Lat.log_le_half {n N : ℕ} (h : n ^ 2 ≤ N) :
    Real.log n ≤ Real.log N / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := Real.log_natCast_nonneg N
    simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · have h1 : Real.log ((n : ℝ) ^ 2) ≤ Real.log N :=
      Real.log_le_log (by positivity) (by exact_mod_cast h)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith

theorem Lat.cube_mem {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    {B : Submodule (𝓞 K) V} {N : 𝓞 K} {z : V} (h : N • z ∈ B) : N ^ 3 • z ∈ B := by
  have : N ^ 3 • z = N ^ 2 • N • z := by rw [smul_smul]; ring_nf
  rw [this]
  exact B.smul_mem _ h


theorem all_parts_transfer_of_facts (hE : IdemE) (hP : IdemP) (hC : Core) (hD : DimSq) (hM : Metric) :
    AllPartsTransfer := by
  intro K _ _ _ _ G _ _ S _ T _ _ _ τ H₀ χ₀ H χ hτ hM1 V _ _ _ _ ι _ _ b X ρ hX hU A hA
  obtain ⟨hfg, hspan, hst⟩ := hA
  have : FiniteDimensional K V := Module.Finite.of_basis b
  choose γ δ c Γ hcore using hC K G S T τ H₀ χ₀ H χ hτ hM1
  obtain ⟨he, ho⟩ := hE K G S T τ hτ V ρ
  have tr := fun s => tr_of_core hP (hcore s) ρ (he s)
  obtain ⟨hsa, hnorm⟩ := hM K G V ι b X ρ hX hU
  have hN : 0 < Fintype.card G := Fintype.card_pos
  have hla : 0 ≤ Real.log (Fintype.card G : ℝ) := Real.log_natCast_nonneg _
  have horth : ∀ (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) s t, s ≠ t →
      Formalism.BranchingDeterminantCap.OrthAt b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) (cut A (epP H χ ρ ∘ₗ eS (τ t) ρ)) := by
    intro H χ s t hst' v x hx y hy
    have sw := (sandwich hE hP hτ ρ hst H χ).2.2
    rw [← sw s x hx, hsa, ← sw t y hy]
    have : eS (τ s) ρ (eS (τ t) ρ y) = 0 := LinearMap.congr_fun (ho s t hst') y
    rw [this]
    exact Formalism.BranchingDeterminantCap.OrthogonalSumAlt.majAt_zero_right b X v x
  have sw1 := sandwich hE hP hτ ρ hst H χ
  have sw0 := sandwich hE hP hτ ρ hst H₀ χ₀
  have os1 := Formalism.BranchingDeterminantCap.orthSandwich K V ι b X hX S (fun s => cut A (epP H χ ρ ∘ₗ eS (τ s) ρ))
    (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) (Fintype.card G) (fg_cut hfg _) hN (horth H χ) sw1.1 sw1.2.1
  have os0 := Formalism.BranchingDeterminantCap.orthSandwich K V ι b X hX S (fun s => cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))
    (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) (Fintype.card G) (fg_cut hfg _) hN (horth H₀ χ₀) sw0.1
    sw0.2.1
  have hrk : ∀ s, rkK (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) =
      nS (τ s) H χ * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) := fun s => by
    rw [rkK_cut hspan, rkK_cut hspan]; exact (tr s).rank
  have hxm : ∀ s j, ∀ a ∈ cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ),
      ((Fintype.card G : 𝓞 K) ^ 3) • (epP H χ ρ ∘ₗ ρ (γ s j)) a ∈
        cut A (epP H χ ρ ∘ₗ eS (τ s) ρ) := fun s j a ha =>
    cube_mem (smul_mem_cut hP ρ hst H χ _ (tr s).2.1 ha.1
      ((tr s).2.2.1 j a ((mem_cut (tr s).1).1 ha).2))
  have hym : ∀ s i, ∀ a ∈ cut A (epP H χ ρ ∘ₗ eS (τ s) ρ),
      ((Fintype.card G : 𝓞 K) ^ 3) • (epP H₀ χ₀ ρ ∘ₗ ρ (δ s i)) a ∈
        cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ) := fun s i a ha =>
    cube_mem (smul_mem_cut hP ρ hst H₀ χ₀ _ (tr s).1 ha.1
      ((tr s).2.2.2.1 i a ((mem_cut (tr s).2.1).1 ha).2))
  have hyi : ∀ s, ∀ a ∈ cut A (epP H χ ρ ∘ₗ eS (τ s) ρ),
      (∀ i, (epP H₀ χ₀ ρ ∘ₗ ρ (δ s i)) a = 0) → a = 0 := fun s a ha h0 =>
    (tr s).inj_y a ((mem_cut (tr s).2.1).1 ha).2 h0
  have hrk0 : rkK (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) =
      ∑ s, nS (τ s) H χ * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) := by
    rw [os1.1]; exact Finset.sum_congr rfl fun s _ => hrk s
  have h3a : ∀ s, |degT b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) -
      (nS (τ s) H χ : ℝ) * degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))| ≤
      (6 * Real.log (Fintype.card G) + Real.log (nS (τ s) H χ)) *
        ((nS (τ s) H χ : ℝ) * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))) := by
    intro s
    by_cases hn : nS (τ s) H χ = 0
    · simp [degT, hrk s, hn]
    by_cases hr : cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ) = ⊥
    · have h0 : rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) = 0 := by
        rw [hr]; simp [rkK]
      simp [degT, hrk s, h0]
    exact Formalism.BranchingDeterminantCap.transferPart K V ι b X hX _ _ _ (Fintype.card G)
      (fun j => epP H χ ρ ∘ₗ ρ (γ s j)) (fun i => epP H₀ χ₀ ρ ∘ₗ ρ (δ s i)) (fg_cut hfg _)
      (fg_cut hfg _) hr (Nat.pos_of_ne_zero hn) hN (hxm s) (hym s) (fun i v => hnorm H χ _ v)
      (fun i v => hnorm H₀ χ₀ _ v)
      (fun a ha h0 => (tr s).first_axis_injective a (fun j => ((mem_cut (tr s).1).1 (ha j)).2) h0) (hyi s) (hrk s)
  have h3b : ∀ s, (6 * Real.log (Fintype.card G) + Real.log (nS (τ s) H χ)) *
        ((nS (τ s) H χ : ℝ) * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))) ≤
      6.5 * Real.log (Fintype.card G) *
        ((nS (τ s) H χ : ℝ) * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))) := by
    intro s
    have := log_le_half ((hD K G S T τ hτ s).2 H χ)
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hcast : ((∑ s, nS (τ s) H χ * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) : ℕ) : ℝ) =
      ∑ s, (nS (τ s) H χ : ℝ) * rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) := by push_cast; rfl
  have o12 : ∑ s, degT b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) ≤
      degT b X (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) := os1.2.1
  have o13 : degT b X (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) ≤
      ∑ s, degT b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) + 2 * Real.log (Fintype.card G) *
        (rkK (cut A (epP H χ ρ ∘ₗ eGood τ ρ)) : ℝ) := os1.2.2
  have o02 : ∑ s, degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) ≤
      degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) := os0.2.1
  have o03 : degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) ≤
      ∑ s, degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) + 2 * Real.log (Fintype.card G) *
        (rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) : ℝ) := os0.2.2
  rw [hrk0] at o13
  rw [os0.1, Nat.cast_sum] at o03
  have h4 := Formalism.BranchingDeterminantCap.transferDeg S (fun s => (rkK (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)) : ℝ))
    (fun s => (nS (τ s) H χ : ℝ)) (fun s => degT b X (cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ)))
    (fun s => degT b X (cut A (epP H χ ρ ∘ₗ eS (τ s) ρ))) (Real.log (Fintype.card G))
    (degT b X (cut A (epP H χ ρ ∘ₗ eGood τ ρ)))
    (fun s => ((h3a s).trans (h3b s)).trans (le_of_eq (by norm_num))) o12 (by rw [← hcast]; exact o13)
    hla (fun s => by positivity)
  have h810 : 8.5 * Real.log (Fintype.card G : ℝ) ≤ 10 * Real.log (Fintype.card G : ℝ) := by
    linarith only [hla]
  have h85 : (17 / 2 : ℝ) = 8.5 := by norm_num
  rw [h85, ← hcast] at h4
  refine ⟨⟨hrk, hrk0⟩, ⟨iSup_le sw1.1, sw1.2.1, fun s t hst' x hx y hy v => horth H χ s t hst' v x hx y hy,
    sub_nonneg.2 o12, sub_le_iff_le_add'.2 o13, sub_nonneg.2 o02, sub_le_iff_le_add'.2 o03⟩,
    fun s => ⟨h3a s, h3b s⟩, ⟨?_, ?_⟩, fun h0 => ⟨?_, add_le_add_right h810 _⟩⟩
  · exact h4
  · exact mul_le_mul_of_nonneg_right h810 (Nat.cast_nonneg _)
  · have := Formalism.BranchingDeterminantCap.transferMuMax K V ι b X hX S (fun s => cut A (epP H₀ χ₀ ρ ∘ₗ eS (τ s) ρ))
      (fun s => cut A (epP H χ ρ ∘ₗ eS (τ s) ρ)) (cut A (epP H χ ρ ∘ₗ eGood τ ρ))
      (cut A (epP H₀ χ₀ ρ ∘ₗ eGood τ ρ)) (Fintype.card G) (fun s => nS (τ s) H χ)
      (fun s i => epP H₀ χ₀ ρ ∘ₗ ρ (δ s i)) (fg_cut hfg _) (fg_cut hfg _) h0 hN
      (fun s => (hD K G S T τ hτ s).2 H χ) (horth H χ) sw1.1 sw1.2.1 sw0.1 hym
      (fun s i v => hnorm H₀ χ₀ _ v) hyi
    rw [h85] at this
    exact this

end Formalism.IndefR.LatticeTransfer
end
end
