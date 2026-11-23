module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1946
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum NumberField Matrix
open GlobalTheory.Mem.Isom
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Rig)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped ComplexOrder

namespace GlobalTheory.TriMove

variable {D : D7} {S S' : HSp D}

theorem rdx_conj_diag {m n : ℕ} (h : m = n) (d : Fin m → ℂ) :
    (rdx (K := ℂ) h)ᴴ * diagonal d * rdx (K := ℂ) h = diagonal (d ∘ (finCongr h).symm) := by
  subst h
  ext i j
  simp [rdx, Matrix.one_apply, Matrix.diagonal_apply]

theorem diag_rdx {m n : ℕ} (h : m = n) (d : Fin m → ℂ) :
    diagonal d * rdx (K := ℂ) h = rdx (K := ℂ) h * diagonal (d ∘ (finCongr h).symm) := by
  subst h
  ext i j
  simp only [rdx, finCongr_refl, Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id, Matrix.mul_one, Matrix.one_mul,
    Function.comp_id]

theorem rdi_mulVec {K : Type} [CommRing K] {m n : ℕ} (h : m = n) (v : Fin m → K) (i : Fin n) :
    (rdi (K := K) h *ᵥ v) i = v ((finCongr h).symm i) := by
  subst h
  simp [rdi, Matrix.one_apply]

theorem cT_sig_eq (M : Matrix (Fin S'.rank) (Fin S.rank) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := by
  ext i j
  rfl

theorem mem_latMove (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (y : Fin S'.rank → D.host.E) :
    y ∈ latMove I Λ ↔ I.Q *ᵥ y ∈ Λ := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    show I.Q *ᵥ (I.P *ᵥ u) ∈ Λ
    rwa [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec]
  · intro hy
    refine ⟨I.Q *ᵥ y, hy, ?_⟩
    show I.P *ᵥ (I.Q *ᵥ y) = y
    rw [Matrix.mulVec_mulVec, I.PQ, Matrix.one_mulVec]

theorem sumForm_eq (G : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem form_move (I : IsoMat S S') (x y : Fin S.rank → D.host.E) :
    star (I.P *ᵥ x) ⬝ᵥ (S'.gram *ᵥ (I.P *ᵥ y)) = star x ⬝ᵥ (S.gram *ᵥ y) := by
  have hg : I.Pᴴ * S'.gram * I.P = S.gram := by rw [← cT_sig_eq]; exact I.gram
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem latS_mulVec_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (T : Subring (TensorProduct F E R)) {n N : ℕ}
    (M : Matrix (Fin N) (Fin n) E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E))
    (hM : ∀ x ∈ Λ', M *ᵥ x ∈ Λ) :
    ∀ x ∈ Formalism.UG.latS (F := F) R T Λ', (M.map (Formalism.UG.inclE (F := F) R)) *ᵥ x ∈ Formalism.UG.latS (F := F) R T Λ := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x0, hx0, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨M *ᵥ x0, hM x0 hx0, ?_⟩
    funext i

    simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have e : (M.map (Formalism.UG.inclE (F := F) R)) *ᵥ (a • x) = a • ((M.map (Formalism.UG.inclE (F := F) R)) *ᵥ x) := by
      rw [Subring.smul_def, Subring.smul_def, mulVec_smul]
    rw [e]; exact Submodule.smul_mem _ a hx

theorem mem_hatL_move (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (x : Fin S'.rank → Lev.EAf D) :
    x ∈ Formalism.L2.Herm.hatL (latMove I Λ) ↔ fQ I *ᵥ x ∈ Formalism.L2.Herm.hatL Λ := by
  constructor
  · intro hx
    exact latS_mulVec_mem _ _ I.Q (latMove I Λ) Λ (fun y hy => (mem_latMove I Λ y).1 hy) x hx
  · intro hx
    have h := latS_mulVec_mem _ _ I.P Λ (latMove I Λ)
      (fun y hy => (mem_latMove I Λ _).2 (by rwa [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec])) _ hx
    have e : I.P.map (Formalism.UG.inclE _) *ᵥ (fQ I *ᵥ x) = x := by
      show fP I *ᵥ (fQ I *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, fP_fQ, Matrix.one_mulVec]
    rwa [e] at h

theorem frame_inv (I : IsoMat S S') (β : GL (Fin S.rank) (Lev.EAf D)) :
    ((betaMove I β)⁻¹ : GL (Fin S'.rank) (Lev.EAf D)).val =
      HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) I.rank_eq) (β⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val) (fQ I) := rfl

theorem frame_move (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (β : GL (Fin S.rank) (Lev.EAf D))
    (hβ : Formalism.L2.DIV.IsFrame β Λ) :
    Formalism.L2.DIV.IsFrame (F := D.host.F) (E := D.host.E) (n := S'.rank) (betaMove I β) (latMove I Λ) := by
  intro x
  rw [mem_hatL_move, hβ, frame_inv]
  simp only [← Matrix.mulVec_mulVec, rdi_mulVec]
  exact ⟨fun H i => H _, fun H j => by simpa using H (finCongr I.rank_eq j)⟩

theorem selfDual_move (I : IsoMat S S') (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (h : IsSelfDualC S Λ) :
    IsSelfDualC S' (latMove I Λ) := by
  have hPQ : ∀ y, I.P *ᵥ (I.Q *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, I.PQ, Matrix.one_mulVec]
  have hQP : ∀ y, I.Q *ᵥ (I.P *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, I.QP, Matrix.one_mulVec]
  obtain ⟨hl, hd⟩ := h
  refine ⟨Submodule.IsLattice.of_fg D.host.E (hl.fg.map _), ?_⟩
  · intro y
    rw [mem_latMove, hd (I.Q *ᵥ y)]
    simp only [sumForm_eq]
    constructor
    · intro H x hx
      rw [mem_latMove] at hx
      obtain ⟨b, hb⟩ := H _ hx
      refine ⟨b, ?_⟩
      rw [hb, ← form_move I, hPQ, hPQ]
    · intro H x hx
      have hx' : I.P *ᵥ x ∈ latMove I Λ := by rw [mem_latMove, hQP]; exact hx
      obtain ⟨b, hb⟩ := H _ hx'
      refine ⟨b, ?_⟩
      rw [hb, ← form_move I, hPQ]

theorem cartan_conj {m n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} {G' : Matrix (Fin m) (Fin m) ℂ} {a : Matrix (Fin m) (Fin n) ℂ}
    {b : Matrix (Fin n) (Fin m) ℂ} (hab : a * b = 1) (hba : b * a = 1) (hb : bᴴ * G * b = G') (ha : aᴴ * G' * a = G)
    {s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCartanInv G' (a * s * b) := by
  obtain ⟨h1, h2, h3⟩ := hs
  refine ⟨?_, ?_, ?_⟩
  · calc a * s * b * (a * s * b) = a * (s * (b * a) * s) * b := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hba, Matrix.mul_one, h1, Matrix.mul_one, hab]
  · rw [conjTranspose_mul, conjTranspose_mul]
    calc bᴴ * (sᴴ * aᴴ) * G' * (a * s * b) = bᴴ * (sᴴ * (aᴴ * G' * a) * s) * b := by simp only [Matrix.mul_assoc]
      _ = G' := by rw [ha, h2, hb]
  · have e : G' * (a * s * b) = bᴴ * (G * s) * b := by
      rw [← hb]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc b a, hba, Matrix.one_mul]
    rw [e]
    refine h3.conjTranspose_mul_mul_same fun u v huv => ?_
    have := congrArg (a *ᵥ ·) huv
    simpa [Matrix.mulVec_mulVec, hab] using this

theorem onb_conj {m n : ℕ} (h : n = m) {G : Matrix (Fin n) (Fin n) ℂ} {G' : Matrix (Fin m) (Fin m) ℂ}
    {a : Matrix (Fin m) (Fin n) ℂ} {b : Matrix (Fin n) (Fin m) ℂ} (hba : b * a = 1) (ha : aᴴ * G' * a = G)
    {s B : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} (hs : IsONBasis G s B p) :
    IsONBasis G' (a * s * b) (a * B * rdx (K := ℂ) h) p := by
  obtain ⟨ε, hε, hd, hsB⟩ := hs
  refine ⟨fun i => ε ((finCongr h).symm i), fun i => ?_, ?_, ?_⟩
  · simpa using hε ((finCongr h).symm i)
  · rw [conjTranspose_mul, conjTranspose_mul]
    calc (rdx (K := ℂ) h)ᴴ * (Bᴴ * aᴴ) * G' * (a * B * rdx (K := ℂ) h)
        = (rdx (K := ℂ) h)ᴴ * (Bᴴ * (aᴴ * G' * a) * B) * rdx (K := ℂ) h := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hd]; exact rdx_conj_diag h _
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc b a, hba, Matrix.one_mul, ← Matrix.mul_assoc s B, hsB, Matrix.mul_assoc B, diag_rdx h]
    rfl

theorem rigMove_is {S S' : HSp D} (I : IsoMat S S') (r : Rig S) (hr : r.Is) : (rigMove I r).Is := by
  unfold Rig.Is at hr ⊢
  obtain ⟨h1, h2, h3⟩ := hr
  refine ⟨selfDual_move I r.Λ h1, frame_move I r.Λ r.β h2, fun τ => ?_⟩
  have hG' : (I.qT τ)ᴴ * gramAt D S τ * I.qT τ = gramAt D S' τ := I.qT_gram τ
  have hG : (I.pT τ)ᴴ * gramAt D S' τ * I.pT τ = gramAt D S τ := I.symm.qT_gram τ
  obtain ⟨hc, p, hp⟩ := h3 τ
  exact ⟨cartan_conj (I.pT_qT τ) (I.qT_pT τ) hG' hG hc, p, onb_conj I.rank_eq (I.qT_pT τ) hG hp⟩

end GlobalTheory.TriMove

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriMove

open GlobalTheory.Mem.Isom
open Formalism.UG (cT cT_mul cT_one)

variable {D : D7}

private theorem gram_inv_cT {V V' : HSp D} (I : IsoMat V V') :
    HMul.hMul (V'.gram⁻¹) (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.Q) = HMul.hMul I.P (V.gram⁻¹) := by
  set σ : D.host.E →+* D.host.E := ↑D.sp.cm.sig with hσ
  have hg : cT σ I.P * V'.gram * I.P = V.gram := I.gram
  have hg' : cT σ I.Q * V.gram * I.Q = V'.gram := I.symm.gram
  have hPQh : cT σ I.Q * cT σ I.P = 1 := by rw [← cT_mul, I.PQ, cT_one]
  have hQPh : cT σ I.P * cT σ I.Q = 1 := by rw [← cT_mul, I.QP, cT_one]
  by_cases hu : IsUnit V.gram.det
  · have hinv : V'.gram⁻¹ = I.P * V.gram⁻¹ * cT σ I.P := by
      refine Matrix.inv_eq_right_inv ?_
      rw [← hg']
      calc cT σ I.Q * V.gram * I.Q * (I.P * V.gram⁻¹ * cT σ I.P)
          = cT σ I.Q * (V.gram * (I.Q * I.P) * V.gram⁻¹) * cT σ I.P := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [I.QP, Matrix.mul_one, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hPQh]
    show V'.gram⁻¹ * cT σ I.Q = I.P * V.gram⁻¹
    rw [hinv, Matrix.mul_assoc, hQPh, Matrix.mul_one]
  · have hu' : ¬ IsUnit V'.gram.det := by
      intro h'
      apply hu
      refine Matrix.isUnit_det_of_right_inverse (B := I.Q * V'.gram⁻¹ * cT σ I.Q) ?_
      rw [← hg]
      calc cT σ I.P * V'.gram * I.P * (I.Q * V'.gram⁻¹ * cT σ I.Q)
          = cT σ I.P * (V'.gram * (I.P * I.Q) * V'.gram⁻¹) * cT σ I.Q := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [I.PQ, Matrix.mul_one, Matrix.mul_nonsing_inv _ h', Matrix.mul_one, hQPh]
    show V'.gram⁻¹ * cT σ I.Q = I.P * V.gram⁻¹
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hu, Matrix.nonsing_inv_apply_not_isUnit _ hu', Matrix.zero_mul,
      Matrix.mul_zero]

private theorem cT_gram {V V' : HSp D} (I : IsoMat V V') :
    HMul.hMul (cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P) V'.gram = HMul.hMul V.gram I.Q := by
  show cT (D.sp.cm.sig : D.host.E →+* D.host.E) I.P * V'.gram = V.gram * I.Q
  rw [← I.gram, Matrix.mul_assoc _ I.P, I.PQ, Matrix.mul_one]

private theorem sandwich {R : Type} [CommRing R] {s s' t t' : ℕ} (aQ : Matrix (Fin s) (Fin s') R) (aP : Matrix (Fin s') (Fin s) R)
    (G' : Matrix (Fin s') (Fin s') R) (cQ : Matrix (Fin s') (Fin s) R) (G : Matrix (Fin s) (Fin s) R) (Y : Matrix (Fin s) (Fin t) R)
    (cP : Matrix (Fin t) (Fin t') R) (H' : Matrix (Fin t') (Fin t') R) (H : Matrix (Fin t) (Fin t) R)
    (tQ : Matrix (Fin t) (Fin t') R) (tP : Matrix (Fin t') (Fin t) R)
    (h1 : G' * cQ = aP * G) (h2 : cP * H' = H * tQ) (hs : aQ * aP = 1) (ht : tQ * tP = 1) :
    aQ * (G' * (cQ * (Y * cP)) * H') * tP = G * Y * H := by
  calc _ = aQ * (G' * cQ) * Y * (cP * H') * tP := by simp only [Matrix.mul_assoc]
    _ = (aQ * aP) * G * Y * H * (tQ * tP) := by rw [h1, h2]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hs, ht, Matrix.one_mul, Matrix.mul_one]

private theorem adj_homMap {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (y : WO S T) :
    HMul.hMul (HMul.hMul IS.aQ (HMul.hMul (HMul.hMul ((S'.gram⁻¹).map (incA D))
      (((homMap IS IT y : Matrix (Fin T'.rank) (Fin S'.rank) (AE D)).map (cA D)).transpose)) (T'.gram.map (incA D)))) IT.aP
      = HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) (((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose))
          (T.gram.map (incA D)) := by
  set σ : D.host.E →+* D.host.E := ↑D.sp.cm.sig with hσ
  have hc : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E), (M.map (incA D)).map (cA D) = (M.map σ).map (incA D) := by
    intro m n M; ext i j; exact (rfl : cA D (incA D (M i j)) = incA D (σ (M i j)))
  have h1 : HMul.hMul ((S'.gram⁻¹).map (incA D)) ((IS.aQ.map (cA D)).transpose) = HMul.hMul IS.aP ((S.gram⁻¹).map (incA D)) := by
    rewrite [IsoMat.aQ, hc, ← Matrix.transpose_map, ← Matrix.map_mul, IsoMat.aP, ← Matrix.map_mul]
    exact congrArg (Matrix.map · (incA D)) (gram_inv_cT IS)
  have h2 : HMul.hMul ((IT.aP.map (cA D)).transpose) (T'.gram.map (incA D)) = HMul.hMul (T.gram.map (incA D)) IT.aQ := by
    rewrite [IsoMat.aP, hc, ← Matrix.transpose_map, ← Matrix.map_mul, IsoMat.aQ, ← Matrix.map_mul]
    exact congrArg (Matrix.map · (incA D)) (cT_gram IT)
  have hy : (((homMap IS IT y : Matrix (Fin T'.rank) (Fin S'.rank) (AE D)).map (cA D)).transpose) =
      HMul.hMul ((IS.aQ.map (cA D)).transpose) (HMul.hMul (((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose) ((IT.aP.map (cA D)).transpose)) := by
    rw [homMap_apply, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  rewrite [hy]
  exact sandwich _ _ _ _ _ _ _ _ _ _ _ h1 h2 IS.aQ_aP IT.aQ_aP

private theorem sandwich2 {R : Type} [CommRing R] {s s' t t' : ℕ} (ri : Matrix (Fin s') (Fin s) R) (bi : Matrix (Fin s) (Fin s) R)
    (fq : Matrix (Fin s) (Fin s') R) (N' : Matrix (Fin s') (Fin t') R) (fp : Matrix (Fin t') (Fin t) R)
    (b : Matrix (Fin t) (Fin t) R) (rx : Matrix (Fin t) (Fin t') R) (N : Matrix (Fin s) (Fin t) R) (h : fq * N' * fp = N) :
    ri * bi * fq * N' * (fp * b * rx) = ri * (bi * N * b) * rx := by
  rw [← h]; simp only [Matrix.mul_assoc]

private theorem fQ_eq {V V' : HSp D} (I : IsoMat V V') : fQ I = I.aQ.map (toEAf D) := by
  ext i j; rfl

private theorem fP_eq {V V' : HSp D} (I : IsoMat V V') : fP I = I.aP.map (toEAf D) := by
  ext i j; rfl

private theorem frMapAdj_homMap {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (y : WO S T) :
    frMapAdj S' T' (betaMove IS βS) (betaMove IT βT) (homMap IS IT y) =
      HMul.hMul (HMul.hMul (rdi (K := Lev.EAf D) IS.rank_eq) (frMapAdj S T βS βT y)) (rdx (K := Lev.EAf D) IT.rank_eq) := by
  have hk := congrArg (Matrix.map · (toEAf D)) (adj_homMap IS IT y)
  rewrite [Matrix.map_mul, Matrix.map_mul, ← fQ_eq, ← fP_eq] at hk
  exact sandwich2 (rdi (K := Lev.EAf D) IS.rank_eq) (βS⁻¹).val (fQ IS) _ (fP IT) βT.val (rdx (K := Lev.EAf D) IT.rank_eq) _ hk

private theorem rdi_mul_mul_rdx {K : Type} [CommRing K] {m m' n n' : ℕ} (h1 : m = m') (h2 : n = n') (N : Matrix (Fin m) (Fin n) K) :
    HMul.hMul (HMul.hMul (rdi (K := K) h1) N) (rdx (K := K) h2) = N.submatrix (finCongr h1).symm (finCongr h2).symm := by
  subst h1 h2
  ext i j
  simp [rdi, rdx, Matrix.one_apply]

private theorem dualCoord_homMap {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (y : WO S T) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S' T' (betaMove IS βS) (betaMove IT βT) (homMap IS IT y) =
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S T βS βT y).submatrix (finCongr IS.rank_eq).symm (finCongr IT.rank_eq).symm := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord
  rw [frMapAdj_homMap, rdi_mul_mul_rdx]
  rfl

private theorem isHalf_homMap {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (c : AE D) (y : WO S T) :
    IsHalf c (homMap IS IT y) ↔ IsHalf c y := by
  have hs : ∀ {m n : ℕ} (u : Mx D m n), IsHalf c u ↔ c • u = u := fun u =>
    ⟨fun h => Matrix.ext fun i j => (h i j : _), fun h i j => (congrFun (congrFun h i) j : _)⟩
  rw [hs, hs]
  have hm : c • homMap IS IT y = homMap IS IT (c • y) := by
    rw [homMap_apply, homMap_apply, Matrix.mul_smul, Matrix.smul_mul]
  rw [hm, (homMap IS IT).injective.eq_iff]

private theorem read_cond {m m' n n' : ℕ} (h1 : m = m') (h2 : n = n') (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E))
    (a : ℕ) (N : Matrix (Fin m) (Fin n) (Lev.EAf D)) :
    ((Formalism.IndefR.Datum.IsIntM (N.submatrix (finCongr h1).symm (finCongr h2).symm) ∧
        ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N.submatrix (finCongr h1).symm (finCongr h2).symm i j)) ↔
      (Formalism.IndefR.Datum.IsIntM N ∧ ∀ i j, j.1 < a → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (N i j))) ∧
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a (N.submatrix (finCongr h1).symm (finCongr h2).symm)) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.rightBlock a N) := by
  subst h1 h2
  have e0 : N.submatrix (finCongr (rfl : m = m)).symm (finCongr (rfl : n = n)).symm = N := by
    ext i j; rfl
  rw [e0]
  exact ⟨Iff.rfl, rfl⟩

theorem _root_.GlobalTheory.T.standardPairSecondMemberHalf_isometry_moved : ∀ {D : D7} {S S' T T' : HSp D} (IS : GlobalTheory.Mem.Isom.IsoMat S S') (IT : GlobalTheory.Mem.Isom.IsoMat T T') (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
  GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S' T' (GlobalTheory.TriMove.betaMove IS βS) (GlobalTheory.TriMove.betaMove IT βT) = GlobalTheory.TriMove.trH IS IT (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S T βS βT) := by
  intro D S S' T T' IS IT ν e I a βS βT
  funext w
  obtain ⟨y, rfl⟩ : ∃ y, w = homMap IS IT y := ⟨(homMap IS IT).symm w, ((homMap IS IT).apply_symm_apply w).symm⟩
  have hy : GlobalTheory.TriMove.trH IS IT (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S T βS βT) (homMap IS IT y) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S T βS βT y := by
    show GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd ν e I a S T βS βT ((homMap IS IT).symm (homMap IS IT y)) = _
    rw [(homMap IS IT).symm_apply_apply]
  rw [hy]
  obtain ⟨h1, h2⟩ := read_cond IS.rank_eq IT.rank_eq ν e I a (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.dualCoord S T βS βT y)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd
  split_ifs with hA hB hB
  · rw [dualCoord_homMap, h2]
  · exfalso; apply hB; rw [isHalf_homMap, dualCoord_homMap, h1] at hA; exact hA
  · exfalso; apply hA; rw [isHalf_homMap, dualCoord_homMap, h1]; exact hB
  · rfl

end GlobalTheory.TriMove

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.selfDual_localImage_latticeSupportedAtPlace : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (Λ : AddSubgroup W), (∀ γ ∈ Λ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) γ) →
    (∀ z : W, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (z ∈ Λ ↔ ∀ γ ∈ Λ, ψ (B z γ) = 1)) →
    ∀ w : (κ → Fv F v) × (κ → Fv F v), w ∈ Λ.map (GlobalTheory.LatVac.locCo co v) ↔
      ∀ l ∈ Λ.map (GlobalTheory.LatVac.locCo co v), GlobalTheory.LatVac.psiAt ψ v (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1 := by
  first | exact @GlobalTheory.LatVac.DualLoc.map_selfDual | exact GlobalTheory.LatVac.DualLoc.map_selfDual | (intros; apply GlobalTheory.LatVac.DualLoc.map_selfDual <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.tensorLattice_localDarbouxCoords_bounded : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {B : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ), X.L.IsLattice E → Y.L.IsLattice E →
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ i,
      c * (GlobalTheory.LatVac.locCo co v γ).1 i ∈ v.adicCompletionIntegers F ∧
      c * (GlobalTheory.LatVac.locCo co v γ).2 i ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.LatBound.locCo_latAtV_bounded | exact GlobalTheory.LatBound.locCo_latAtV_bounded | (intros; apply GlobalTheory.LatBound.locCo_latAtV_bounded <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels


theorem _root_.GlobalTheory.T.heisenbergEigen_latticePointAtPlace_localIdentity : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {W : Type} [AddCommGroup W]
    [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (γ : W) (f : (κ → Fv F v) → ℂ) (χ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) γ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (co.rho ψ γ) f (χ • f) →
    ∀ r : (κ → AF F) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) f r → ∀ x₀, r x₀ ≠ 0 →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = χ * f ξ := by
  first | exact @GlobalTheory.LatVac.heis_at_local_identity | exact GlobalTheory.LatVac.heis_at_local_identity | (intros; apply GlobalTheory.LatVac.heis_at_local_identity <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.localIdentity_of_tensorHeisenbergEigen : ∀ {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ)
    (R : (κ → AF F) → ℂ) (c : ℂ), At (evFin F v) γ → (∀ x z, At (evFin F v) z → R (x + z) = R x) →
    ∀ x₀, R x₀ ≠ 0 → co.rho ψ γ (tens (evFin F v) f R) = c • tens (evFin F v) f R →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = c * f ξ := by
  first | exact @GlobalTheory.DblVacEigen.local_identity_of_tens_eigen | exact GlobalTheory.DblVacEigen.local_identity_of_tens_eigen | (intros; apply GlobalTheory.DblVacEigen.local_identity_of_tens_eigen <;> assumption)
end
