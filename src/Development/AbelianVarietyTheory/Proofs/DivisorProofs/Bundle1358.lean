module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import GroundTheory.AutomorphicForms.RealGroupsHaar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SiegelTransposeInverse

open GlobalTheory.Doubling

theorem conj_mulVec_diag {A n ι : Type} [CommRing A] [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
    (e : n ⊕ n ≃ ι) (c : A →+* A) {G t : Matrix n n A} (hG : IsUnit G.det) {p : Matrix (n ⊕ n) (n ⊕ n) A}
    (hp : p * Matrix.fromRows (1 : Matrix n n A) 1 = Matrix.fromRows (1 : Matrix n n A) 1 * t)
    {X Q : Matrix ι ι A} (hQ : p.submatrix e.symm e.symm * Q = 1) (hXQ : X = Qᵀ)
    (hX : Formalism.UG.cT c X * blkMat e G (-G) * X = blkMat e G (-G)) (u : n → A) :
    (blkMat e (1 : Matrix n n A) (-1) * X * blkMat e (1 : Matrix n n A) (-1)) *ᵥ pairVec e u u =
      pairVec e ((G⁻¹ * t.map c * G) *ᵥ u) ((G⁻¹ * t.map c * G) *ᵥ u) := by
  have h1 : blkMat e G (-G) * X = (p.submatrix e.symm e.symm).map c * blkMat e G (-G) := by
    have h0 : Formalism.UG.cT c X = Q.map c := by rw [hXQ]; rfl
    have h2 : (p.submatrix e.symm e.symm).map c * Q.map c = 1 := by
      rw [← Matrix.map_mul, hQ, Matrix.map_one _ (map_zero c) (map_one c)]
    conv_rhs => rw [← hX, h0, Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have h3 : ∀ y : n → A, (p.submatrix e.symm e.symm).map c *ᵥ pairVec e y y =
      pairVec e (t.map c *ᵥ y) (t.map c *ᵥ y) := by
    intro y
    have h4 := congrArg (fun M : Matrix (n ⊕ n) n A => M *ᵥ y)
      ((Matrix.map_mul (f := c) (L := p) (M := Matrix.fromRows (1 : Matrix n n A) 1)).symm.trans
        ((congrArg (fun M : Matrix (n ⊕ n) n A => M.map c) hp).trans Matrix.map_mul))
    simp only [Matrix.fromRows_map, Matrix.map_one _ (map_zero c) (map_one c), ← Matrix.mulVec_mulVec,
      Matrix.fromRows_mulVec, Matrix.one_mulVec] at h4
    rw [← Matrix.submatrix_map, Matrix.submatrix_mulVec_equiv, pairVec, pairVec, ← h4]
    have h7 : (Sum.elim y y ∘ ⇑e.symm) ∘ ⇑e.symm.symm = Sum.elim y y := by
      funext j; simp
    rw [h7]
  have h5 : blkMat e G⁻¹ (-G⁻¹) * blkMat e G (-G) = 1 := by
    rw [blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ hG, blkMat_one]
  have h6 : X = blkMat e G⁻¹ (-G⁻¹) * ((p.submatrix e.symm e.symm).map c * blkMat e G (-G)) := by
    rw [← h1, ← Matrix.mul_assoc, h5, Matrix.one_mul]
  rw [h6]
  simp only [← Matrix.mulVec_mulVec, blkMat_mulVec, Matrix.neg_mulVec, Matrix.mulVec_neg, Matrix.one_mulVec, neg_neg, h3]

theorem keepsDiag_and_det {A n ι : Type} [CommRing A] [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
    (e : n ⊕ n ≃ ι) (c : A →+* A) {G t : Matrix n n A} (hG : IsUnit G.det) {Y : Matrix ι ι A}
    (hY : ∀ u, Y *ᵥ pairVec e u u = pairVec e ((G⁻¹ * t.map c * G) *ᵥ u) ((G⁻¹ * t.map c * G) *ᵥ u)) :
    KeepsDiag e Y ∧ (leviMat e Y).det = c t.det := by
  have hK : KeepsDiag e Y := keepsDiag_of_mulVec fun w hw => by
    obtain ⟨x, rfl⟩ := (mem_diagSub e).1 hw
    rw [hY]
    exact (pairVec_mem_diagSub e).2 rfl
  refine ⟨hK, ?_⟩
  have hL : leviMat e Y = G⁻¹ * t.map c * G := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have h := (hK.mulVec_diag (Pi.single j 1)).symm.trans (hY _)
    funext i
    simpa only [pairVec_inl] using congrFun h (e (.inl i))
  rw [hL, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, Matrix.nonsing_inv_mul _ hG,
    Matrix.det_one, one_mul, RingHom.map_det, RingHom.mapMatrix_apply]

open GlobalTheory.DiagThetaRule in
theorem epsD_mul_self {D : D7} (S : HSp D) : epsD S * epsD S = 1 := by
  apply Subtype.ext
  apply Units.ext
  show Formalism.L2.Theta.mt (dblSp S) (epsD S) * Formalism.L2.Theta.mt (dblSp S) (epsD S) = 1
  rw [mt_epsD, blkMat_mul, neg_mul_neg, Matrix.one_mul, blkMat_one]


open GlobalTheory.DiagThetaRule in
theorem exists_siegel_conj (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
    (hp : p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1)
    (g : GA D (GlobalTheory.Doubling.dblSp S)) (hg : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp S) g =
      ((GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)⁻¹).1.1ᵀ) :
    ∃ h : GlobalTheory.Doubling.siegel S, GlobalTheory.DiagThetaRule.epsD S * g = (h : GA D (GlobalTheory.Doubling.dblSp S)) * GlobalTheory.DiagThetaRule.epsD S ∧
      GlobalTheory.Doubling.aP S h = GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t) := by
  have hG : IsUnit (JR (F := D.host.F) (AF D.host.F) S.gram).det := by
    have h := ((isHermND_gram S).2.isUnit).map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))
    rw [RingHom.map_det, RingHom.mapMatrix_apply] at h
    exact h
  have hX : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (Formalism.L2.Theta.mt (dblSp S) g) *
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) S.gram) (-(JR (F := D.host.F) (AF D.host.F) S.gram)) *
      Formalism.L2.Theta.mt (dblSp S) g =
      blkMat finSumFinEquiv (JR (F := D.host.F) (AF D.host.F) S.gram) (-(JR (F := D.host.F) (AF D.host.F) S.gram)) := by
    rw [← JR_dblSp_gram]
    exact g.2
  have hQ : p.1.1.submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      ((GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)⁻¹).1.1 = 1 := by
    rw [← GlobalTheory.DblSchr.reG_val (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p]
    exact Units.mul_inv _
  have hY := keepsDiag_and_det finSumFinEquiv (sigR (AF D.host.F) D.sp.cm.sig) hG
    (conj_mulVec_diag finSumFinEquiv (sigR (AF D.host.F) D.sp.cm.sig) hG hp hQ hg hX)
  refine ⟨⟨epsD S * g * epsD S, mem_siegelOf.2 hY.1⟩, ?_, Units.ext hY.2⟩
  show epsD S * g = epsD S * g * epsD S * epsD S
  rw [mul_assoc, epsD_mul_self, mul_one]

end GlobalTheory.SiegelTransposeInverse
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DblSchr

open Matrix GlobalTheory.Doubling

theorem dblGram_xi : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ξ • incM D.host.F (GlobalTheory.DblSchr.JBd S JB) = incM D.host.F (D.host.xi0 • (GlobalTheory.Doubling.dblSp S).gram⁻¹) := by
  intro D S JB ξ h
  have hinv : (dblSp S).gram⁻¹ = blkMat finSumFinEquiv S.gram⁻¹ (-S.gram⁻¹) :=
    Matrix.inv_eq_left_inv (by
      rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (isHermND_gram S).2.isUnit, blkMat_one])
  rw [hinv, incM_JBd]
  ext i j
  have hij : ∀ a b, ξ * incM D.host.F JB a b = incM D.host.F (D.host.xi0 • S.gram⁻¹) a b := fun a b => by
    rw [← h]; rfl
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp only [blkMat, GlobalTheory.WeilM.dbl, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, Matrix.smul_apply, Matrix.submatrix_apply, h1, h2,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply, smul_zero, map_zero, smul_neg, map_neg, smul_eq_mul, mul_zero, mul_neg] at hij ⊢
  · exact hij i' j'
  · exact congrArg Neg.neg (hij i' j')

end GlobalTheory.DblSchr
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.DblSchr.ddr_rat : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ x : Matrix (Fin T.rank) (Fin (GlobalTheory.Doubling.dblSp S).rank) D.host.E, ∃ y z : κ ⊕ κ → D.host.F,
      (GlobalTheory.DblSchr.ddr co).e (incM D.host.F x) =
        (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  intro D S T JA JB ξ κ _ co h x
  obtain ⟨y₁, z₁, h₁⟩ := h (x.submatrix id finSumFinEquiv).toCols₁
  obtain ⟨y₂, z₂, h₂⟩ := h (x.submatrix id finSumFinEquiv).toCols₂
  refine ⟨Sum.elim y₁ y₂, Sum.elim z₁ (-z₂), ?_⟩
  rw [GlobalTheory.DblSchr.ddr, GlobalTheory.DblSchr.reD_e, Equiv.symm_symm]
  have e1 : ((incM D.host.F x).submatrix id finSumFinEquiv).toCols₁ = incM D.host.F (x.submatrix id finSumFinEquiv).toCols₁ := rfl
  have e2 : ((incM D.host.F x).submatrix id finSumFinEquiv).toCols₂ = incM D.host.F (x.submatrix id finSumFinEquiv).toCols₂ := rfl
  simp only [GlobalTheory.DblSchr.dblD, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, e1, e2, h₁, h₂]
  refine Prod.ext ?_ ?_
  · funext i; rcases i with i | i <;> rfl
  · funext i; rcases i with i | i <;> simp
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitLat

theorem mulVec_int_iff {K : UQ} {n : ℕ} (P : Matrix (Fin n) (Fin n) K.E) :
    (∀ u : Fin n → K.E, (∀ i, u i ∈ (algebraMap K.O K.E).range) →
      ∀ i, (P *ᵥ u) i ∈ (algebraMap K.O K.E).range) ↔
    ∀ i j, P i j ∈ (algebraMap K.O K.E).range := by
  constructor
  · intro h i j
    have := h (Pi.single j 1) (fun k => by
      by_cases hk : k = j
      · subst hk; simpa using Subring.one_mem _
      · simpa [hk] using Subring.zero_mem _) i
    simpa [Matrix.mulVec_single] using this
  · intro h u hu i
    simp only [Matrix.mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (h i j) (hu j)

theorem unitLat_eq_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ q q' : UL n w, unitLat e B ψ q = unitLat e B ψ q' ↔ q⁻¹ * q' ∈ KL n w := by
  intro E _ _ _ _ w _ K e _ hint n B ψ q q'
  let R := (algebraMap K.O K.E).range
  let M : GLw n w → Matrix (Fin n) (Fin n) K.E := fun g => (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).map e.symm
  have hMmul : ∀ g h : GLw n w, M (g * h) = M g * M h := fun g h => by
    simp only [M, Units.val_mul]
    exact Matrix.map_mul (f := (e.symm : w.adicCompletion E →+* K.E))
  have hM1 : M 1 = 1 := by
    simp only [M, Units.val_one]
    exact Matrix.map_one (f := e.symm) (map_zero _) (map_one _)
  have hent : ∀ g : GLw n w, (∀ i j, M g i j ∈ R) ↔ ∀ i j, (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j ∈ Ov E w := by
    intro g
    refine forall_congr' fun i => forall_congr' fun j => ?_
    show e.symm _ ∈ R ↔ _
    rw [hint, RingEquiv.apply_symm_apply]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hmem : ∀ g : UL n w, ∀ y, y ∈ unitLat e B ψ g ↔ ∀ i, (M ((g : GLw n w)⁻¹) *ᵥ ψ y) i ∈ R :=
    fun g y => Iff.rfl

  have hlat : unitLat e B ψ q = unitLat e B ψ q' ↔
      ∀ v : Fin n → K.E, ((∀ i, (M ((q : GLw n w)⁻¹) *ᵥ v) i ∈ R) ↔ ∀ i, (M ((q' : GLw n w)⁻¹) *ᵥ v) i ∈ R) := by
    rw [SetLike.ext_iff]
    constructor
    · intro h v
      have := h (ψ.symm v)
      rwa [hmem, hmem, LinearEquiv.apply_symm_apply] at this
    · intro h y
      rw [hmem, hmem]
      exact h (ψ y)

  have half : ∀ a b : GLw n w,
      (∀ v : Fin n → K.E, (∀ i, (M b⁻¹ *ᵥ v) i ∈ R) → ∀ i, (M a⁻¹ *ᵥ v) i ∈ R) ↔
      ∀ i j, M (a⁻¹ * b) i j ∈ R := by
    intro a b
    rw [← mulVec_int_iff]
    constructor
    · intro h u hu
      have h1 := h (M b *ᵥ u) (by
        rw [Matrix.mulVec_mulVec, ← hMmul, inv_mul_cancel, hM1, Matrix.one_mulVec]; exact hu)
      rwa [Matrix.mulVec_mulVec, ← hMmul] at h1
    · intro h v hv
      have h1 := h _ hv
      rwa [Matrix.mulVec_mulVec, ← hMmul, mul_assoc, mul_inv_cancel, mul_one] at h1
  have hKL : q⁻¹ * q' ∈ KL n w ↔
      ((q : GLw n w)⁻¹ * q') ∈ Formalism.UG.GLint (Fin n) (Ov E w) := by
    rw [KL, Subgroup.mem_subgroupOf]
    rfl
  rw [hKL, Formalism.UG.P.tjcosets_mem_K_iff, ← hent, ← hent, hlat]
  have hinv : ((q : GLw n w)⁻¹ * q')⁻¹ = (q' : GLw n w)⁻¹ * q := by group
  rw [hinv, ← half, ← half]
  constructor
  · intro h
    exact ⟨fun v hv => (h v).2 hv, fun v hv => (h v).1 hv⟩
  · intro h v
    exact ⟨h.2 v, h.1 v⟩

end GlobalTheory.InertUnitLat
end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem integral_eq_integral_mulLeft_matrixInf (E : Type) [Field E] [NumberField E] (n : ℕ)
    (A : GL (Fin n) (Cinf E)) (F : (Fin n → Fin n → Cinf E) → ℂ) :
    ∫ a, F a = ∫ h : (Fin n → Fin n → Cinf E), ((jacInf (A : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) *
      F (fun i j => ((A : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) := by
  set W := InfinitePlace E
  set M : Matrix (Fin n) (Fin n) (Cinf E) := (A : Matrix (Fin n) (Fin n) (Cinf E)) with hM
  set L : (Fin n → Fin n → Cinf E) →ₗ[ℝ] (Fin n → Fin n → Cinf E) :=
    { toFun := fun x i j => (M * Matrix.of x) i j
      map_add' := fun x y => by
        funext i j
        change (M * (Matrix.of x + Matrix.of y)) i j = (M * Matrix.of x) i j + (M * Matrix.of y) i j
        rw [mul_add, Matrix.add_apply]
      map_smul' := fun c x => by
        funext i j
        change (M * (c • Matrix.of x)) i j = c • (M * Matrix.of x) i j
        rw [Matrix.mul_smul, Matrix.smul_apply] } with hLdef
  have hL : ∀ h, L h = fun i j => (M * Matrix.of h) i j := fun h => rfl

  let e : (Fin n → Fin n → Cinf E) ≃ₗ[ℝ] (W → Fin n → Fin n → ℂ) :=
    { toFun := fun h w i j => h i j w
      invFun := fun g i j w => g w i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Lw : W → (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ) := fun w =>
    (LinearMap.mulLeft ℂ (M.map (fun z => z w))).restrictScalars ℝ
  have hconj : (e : _ →ₗ[ℝ] _) ∘ₗ L ∘ₗ (e.symm : _ →ₗ[ℝ] _) =
      LinearMap.pi (fun w => Lw w ∘ₗ LinearMap.proj w) := by
    apply LinearMap.ext; intro g; funext w i j
    change (M * Matrix.of (fun i j w => g w i j)) i j w = (M.map (fun z => z w) * Matrix.of (g w)) i j
    simp [Matrix.mul_apply, Finset.sum_apply, Matrix.map_apply]
  have hdetw : ∀ w, LinearMap.det (Lw w) = Complex.normSq (M.det w) ^ n := by
    intro w
    have := GroundTheory.Automorphic.det_restrictScalars_mulLeft (M.map (fun z => z w))
    rw [Fintype.card_fin, ← Complex.normSq_eq_norm_sq] at this
    show LinearMap.det ((LinearMap.mulLeft ℂ (M.map fun z => z w)).restrictScalars ℝ) = _
    rw [this]
    congr 2
    exact (RingHom.map_det (Pi.evalRingHom (fun _ : W => ℂ) w) M).symm
  have hdet : LinearMap.det L = jacInf M := by
    rw [← LinearMap.det_conj L e, hconj, LinearMap.det_pi]
    simp only [hdetw]
    rfl
  have hpos : 0 < jacInf M := by
    have hdA : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
    refine Finset.prod_pos fun w _ => pow_pos (Complex.normSq_pos.2 ?_) n
    intro h0
    have hu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
    have : IsUnit (M.det w) := hu.map (Pi.evalRingHom (fun _ : W => ℂ) w)
    exact this.ne_zero h0
  have hd0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hmap : Measure.map L (volume : Measure (Fin n → Fin n → Cinf E)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd0
  set Le : (Fin n → Fin n → Cinf E) ≃L[ℝ] (Fin n → Fin n → Cinf E) :=
    (LinearMap.equivOfDetNeZero L hd0).toContinuousLinearEquiv
  have hLe : (Le : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) = L := rfl
  have hemb : MeasurableEmbedding (L : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) := by
    rw [← hLe]; exact Le.toHomeomorph.measurableEmbedding
  simp_rw [← hL]
  rw [integral_const_mul, ← hemb.integral_map, hmap, integral_smul_measure, hdet,
    abs_of_pos (inv_pos.2 hpos), ENNReal.toReal_ofReal (inv_pos.2 hpos).le, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hpos.ne'), one_mul]

end GlobalTheory.JSW.MirCinf
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section
namespace GlobalTheory.AdelicCoordF

open GlobalTheory.AdelicCoord (incF incI incF_sndA incI_fstA pairA_mul_eq_zero_iff_snd pairA_mul_eq_zero_iff_fst)

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def secF : Af F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incF F) LinearMap.id

def secI : Ainf F ⊗[F] E →ₗ[F] AF F ⊗[F] E := TensorProduct.map (incI F) LinearMap.id

theorem secF_finPart (z : AF F ⊗[F] E) :
    secF F E (Formalism.IndefR.DatumF.finPartF F E z) = pairA F 0 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul a b =>
    have h1 : Formalism.IndefR.DatumF.finPartF F E (a ⊗ₜ b) = sndA F a ⊗ₜ b := rfl
    rw [h1, secF, TensorProduct.map_tmul, LinearMap.id_apply, incF_sndA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem secI_infPart (z : AF F ⊗[F] E) :
    secI F E (Formalism.IndefR.DatumF.infPartF F E z) = pairA F 1 0 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul a b =>
    have h1 : Formalism.IndefR.DatumF.infPartF F E (a ⊗ₜ b) = fstA F a ⊗ₜ b := rfl
    rw [h1, secI, TensorProduct.map_tmul, LinearMap.id_apply, incI_fstA, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem finPartF_smul (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.finPartF F E (pairA F 0 1 • z) = Formalism.IndefR.DatumF.finPartF F E z := by
  rw [Algebra.smul_def, map_mul]
  have : Formalism.IndefR.DatumF.finPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 1)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show sndA F (algebraMap (AF F) (AF F) (pairA F 0 1)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.AdelicCoord.sndA_pairA]
    rfl
  rw [this, one_mul]

theorem infPartF_smul (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.infPartF F E (pairA F 1 0 • z) = Formalism.IndefR.DatumF.infPartF F E z := by
  rw [Algebra.smul_def, map_mul]
  have : Formalism.IndefR.DatumF.infPartF F E (algebraMap (AF F) (AF F ⊗[F] E) (pairA F 1 0)) = 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show fstA F (algebraMap (AF F) (AF F) (pairA F 1 0)) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.AdelicCoord.fstA_pairA]
    rfl
  rw [this, one_mul]

theorem finPartF_eq_zero_iff (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.finPartF F E z = 0 ↔ pairA F 0 1 • z = 0 := by
  constructor
  · intro h; rw [← secF_finPart, h, map_zero]
  · intro h; rw [← finPartF_smul, h, map_zero]

theorem infPartF_eq_zero_iff (z : AF F ⊗[F] E) :
    Formalism.IndefR.DatumF.infPartF F E z = 0 ↔ pairA F 1 0 • z = 0 := by
  constructor
  · intro h; rw [← secI_infPart, h, map_zero]
  · intro h; rw [← infPartF_smul, h, map_zero]

theorem smul_vec_fin {N : ℕ} (u : Fin N → AF F) : pairA F 0 1 • u = 0 ↔ GlobalTheory.SWQ.fin u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_snd F (u l)

theorem smul_vec_inf {N : ℕ} (u : Fin N → AF F) : pairA F 1 0 • u = 0 ↔ GlobalTheory.SWQ.inf u = 0 := by
  rw [funext_iff, funext_iff]
  exact forall_congr' fun l => pairA_mul_eq_zero_iff_fst F (u l)

theorem smul_pair_eq_zero {N : ℕ} (c : AF F) (w : GlobalTheory.ThetaTransform.VA F N) :
    c • w = 0 ↔ c • w.1 = 0 ∧ c • w.2 = 0 :=
  Prod.ext_iff

theorem coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT N : ℕ)
    (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
    Continuous e ∧ Continuous e.symm ∧
      (∀ x : Formalism.IndefR.DatumF.WOF F E nS nT, x.map (Formalism.IndefR.DatumF.finPartF F E) = 0 ↔
        GlobalTheory.SWQ.fin (e x).1 = 0 ∧ GlobalTheory.SWQ.fin (e x).2 = 0) ∧
      (∀ x : Formalism.IndefR.DatumF.WOF F E nS nT, x.map (Formalism.IndefR.DatumF.infPartF F E) = 0 ↔
        GlobalTheory.SWQ.inf (e x).1 = 0 ∧ GlobalTheory.SWQ.inf (e x).2 = 0) := by
  intro F E _ _ _ _ _ nS nT N e
  haveI h0 : IsModuleTopology (AF F) (AF F ⊗[F] E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI hA : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  haveI h1 : IsModuleTopology (AF F) (Fin nS → AF F ⊗[F] E) := IsModuleTopology.instPi
  haveI h2 : IsModuleTopology (AF F) (Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) := IsModuleTopology.instPi
  refine ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap,
    IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, fun x => ?_, fun x => ?_⟩
  · have key : x.map (Formalism.IndefR.DatumF.finPartF F E) = 0 ↔ pairA F 0 1 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => finPartF_eq_zero_iff F E (x i j)
    rw [key, ← smul_vec_fin, ← smul_vec_fin, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]
  · have key : x.map (Formalism.IndefR.DatumF.infPartF F E) = 0 ↔ pairA F 1 0 • x = 0 := by
      rw [← Matrix.ext_iff, ← Matrix.ext_iff]
      simp only [Matrix.map_apply, Matrix.zero_apply, Matrix.smul_apply]
      exact forall_congr' fun i => forall_congr' fun j => infPartF_eq_zero_iff F E (x i j)
    rw [key, ← smul_vec_inf, ← smul_vec_inf, ← smul_pair_eq_zero, ← LinearEquiv.map_smul,
      LinearEquiv.map_eq_zero_iff]

end GlobalTheory.AdelicCoordF

end
end

end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_siegelParabolic_conj_invTranspose : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)),
    p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1 →
    ∀ g : GA D (GlobalTheory.Doubling.dblSp S), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp S) g =
      ((GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)⁻¹).1.1ᵀ →
    ∃ h : GlobalTheory.Doubling.siegel S, GlobalTheory.DiagThetaRule.epsD S * g = (h : GA D (GlobalTheory.Doubling.dblSp S)) * GlobalTheory.DiagThetaRule.epsD S ∧
      GlobalTheory.Doubling.aP S h = GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t) := by
  first | exact @GlobalTheory.SiegelTransposeInverse.exists_siegel_conj | exact GlobalTheory.SiegelTransposeInverse.exists_siegel_conj | (intros; apply GlobalTheory.SiegelTransposeInverse.exists_siegel_conj <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubledDarbouxCoords_rational_of_rational : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ x : Matrix (Fin T.rank) (Fin (GlobalTheory.Doubling.dblSp S).rank) D.host.E, ∃ y z : κ ⊕ κ → D.host.F,
      (GlobalTheory.DblSchr.ddr co).e (incM D.host.F x) =
        (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  first | exact @GlobalTheory.DblSchr.ddr_rat | exact GlobalTheory.DblSchr.ddr_rat | (intros; apply GlobalTheory.DblSchr.ddr_rat <;> assumption)

end
end

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.doubledGram_satisfies_xi_relation : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ξ • incM D.host.F (GlobalTheory.DblSchr.JBd S JB) = incM D.host.F (D.host.xi0 • (GlobalTheory.Doubling.dblSp S).gram⁻¹) := by
  first | exact @GlobalTheory.DblSchr.dblGram_xi | exact GlobalTheory.DblSchr.dblGram_xi | (intros; apply GlobalTheory.DblSchr.dblGram_xi <;> assumption)

end
end
