module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
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
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilPairPartner

theorem map_mul_map_inv {R S : Type} [Field R] [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (h : M.det ≠ 0) : M.map f * (M⁻¹).map f = 1 := by
  rw [← Matrix.map_mul, M.mul_nonsing_inv (isUnit_iff_ne_zero.mpr h), Matrix.map_one _ f.map_zero f.map_one]

theorem map_inv_mul_map {R S : Type} [Field R] [CommRing S] (f : R →+* S) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (h : M.det ≠ 0) : (M⁻¹).map f * M.map f = 1 := by
  rw [← Matrix.map_mul, M.nonsing_inv_mul (isUnit_iff_ne_zero.mpr h), Matrix.map_one _ f.map_zero f.map_one]

theorem map_smul_eq {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : Type} (r : R) (M : Matrix m n R) :
    (r • M).map f = f r • M.map f := by
  ext i j
  simp

theorem conj_inv_transpose {S : Type} [CommRing S] (c : S →+* S) {n : Type} [Fintype n] [DecidableEq n] (ξ u : S)
    (hu : IsUnit u) (B Bi K G N : Matrix n n S) (hb : Bᵀ * K * B.map c = K) (hBB : B * Bi = 1) (hBB' : Bi * B = 1)
    (hK : ξ • K = u • N) (hGN : G * N = 1) (hNG : N * G = 1) : Bi.map c * G * Biᵀ = G := by
  have hbN : Bᵀ * N * B.map c = N := by
    have h1 : Bᵀ * (ξ • K) * B.map c = ξ • K := by rw [Matrix.mul_smul, Matrix.smul_mul, hb]
    rw [hK, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact hu.smul_left_cancel.mp h1
  have hcc : Bi.map c * B.map c = 1 := by
    rw [← Matrix.map_mul, hBB', Matrix.map_one _ c.map_zero c.map_one]
  have hTT : Biᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  calc Bi.map c * G * Biᵀ = Bi.map c * G * Biᵀ * (N * G) := by rw [hNG, Matrix.mul_one]
    _ = Bi.map c * G * Biᵀ * ((Bᵀ * N * B.map c) * G) := by rw [hbN]
    _ = Bi.map c * G * (Biᵀ * Bᵀ) * N * B.map c * G := by simp only [Matrix.mul_assoc]
    _ = Bi.map c * (G * N) * B.map c * G := by rw [hTT, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = G := by rw [hGN, Matrix.mul_one, hcc, Matrix.one_mul]

theorem pair_partner : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  intro D S T JA JB ξ hA hB a b
  have hmap : ∀ {m n : Type} (X : Matrix m n (AE D)),
      X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) :=
    fun X => Matrix.ext fun i j => rfl

  have ha : (a.1.val)ᵀ * incM D.host.F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JA := a.2
  set A : Matrix (Fin T.rank) (Fin T.rank) (AE D) := a.1.val with hAdef
  have hJA : incM D.host.F JA = (incM D.host.F T.gram)ᵀ := by
    rw [hA]; rfl
  rw [hJA] at ha
  have ha' := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'
  have hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig T.gram := by
    show Formalism.UG.cT _ a.1.val * _ * a.1.val = _
    simp only [Formalism.UG.cT, hmap]
    rw [Matrix.mul_assoc]
    exact ha'

  obtain ⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig = f := ⟨_, rfl⟩
  have hb : (b.1.val)ᵀ * incM D.host.F JB * (b.1.val).map cR = incM D.host.F JB := by
    rw [← hcR, hmap]; exact b.2
  have hBB : b.1.val * (b⁻¹).1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).mul_inv
  have hBB' : (b⁻¹).1.val * b.1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).inv_mul
  obtain ⟨B, hBdef⟩ : ∃ B : Matrix (Fin S.rank) (Fin S.rank) (AE D), b.1.val = B := ⟨_, rfl⟩
  obtain ⟨Bi, hBidef⟩ : ∃ B : Matrix (Fin S.rank) (Fin S.rank) (AE D), (b⁻¹).1.val = B := ⟨_, rfl⟩
  rw [hBdef] at hb hBB hBB'
  rw [hBidef] at hBB hBB'
  have hGN := GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) S.gram
    (GlobalTheory.VolHeckeCompare.gram_det_ne_zero S)
  have hNG := GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) S.gram
    (GlobalTheory.VolHeckeCompare.gram_det_ne_zero S)
  have hsm : incM D.host.F (D.host.xi0 • S.gram⁻¹) = inclR (F := D.host.F) (AF D.host.F) D.host.xi0 •
      incM D.host.F S.gram⁻¹ :=
    GlobalTheory.WeilPairPartner.map_smul_eq _ _ _
  have hu : IsUnit (inclR (F := D.host.F) (AF D.host.F) D.host.xi0) :=
    (isUnit_iff_ne_zero.mpr (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have hcore := GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu B Bi (incM D.host.F JB) (incM D.host.F S.gram)
    (incM D.host.F S.gram⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG
  have hTT : Biᵀ * Bᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  let gU : GL (Fin S.rank) (AE D) :=
    ⟨Biᵀ, Bᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩
  have hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig S.gram := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) Biᵀ * incM D.host.F S.gram * Biᵀ =
      incM D.host.F S.gram
    rw [hcR]
    simp only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]
    exact hcore
  refine ⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩
  show Biᵀ = ((b⁻¹).1.val)ᵀ
  rw [hBidef]

end GlobalTheory.WeilPairPartner
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger

theorem matchPair_cA_eq_sigR (D : D7) (x : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig x = sigR (AF D.host.F) D.sp.cm.sig x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, sigR]
  | add x y hx hy => simp_all

theorem matchPair_inv_transpose {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (Bm Bi P Q Cm Ci : Matrix n n R) (hBB : Bm * Bi = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hCC : Ci * Cm = 1) (hb : Bmᵀ * P * Cm = P) : Ci * Q * Biᵀ = Q := by
  have e1 : Biᵀ * Bmᵀ = 1 := by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  have e2 : P * Cm = Biᵀ * P := by
    calc P * Cm = (Biᵀ * Bmᵀ) * P * Cm := by rw [e1, Matrix.one_mul]
      _ = Biᵀ * (Bmᵀ * P * Cm) := by simp only [Matrix.mul_assoc]
      _ = Biᵀ * P := by rw [hb]
  have e3 : Cm * Q = Q * Biᵀ := by
    calc Cm * Q = (Q * P) * Cm * Q := by rw [hQP, Matrix.one_mul]
      _ = Q * (P * Cm) * Q := by simp only [Matrix.mul_assoc]
      _ = Q * Biᵀ * (P * Q) := by rw [e2]; simp only [Matrix.mul_assoc]
      _ = Q * Biᵀ := by rw [hPQ, Matrix.mul_one]
  calc Ci * Q * Biᵀ = Ci * (Q * Biᵀ) := Matrix.mul_assoc _ _ _
    _ = Ci * (Cm * Q) := by rw [e3]
    _ = Q := by rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]

theorem matchPair_map_cA (D : D7) {n m : ℕ} (M : Matrix (Fin n) (Fin m) (AE D)) :
    M.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = M.map (sigR (AF D.host.F) D.sp.cm.sig) := by
  ext i j; exact matchPair_cA_eq_sigR D (M i j)

theorem matchPair_memT (D : D7) (T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (hA : JA = T.gramᵀ)
    (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)) : (a.1 : GL (Fin T.rank) (AE D)) ∈ HR (AF D.host.F) D.sp.cm.sig T.gram := by
  have ha : a.1.1ᵀ * incM D.host.F JA * a.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JA := a.2
  show Formalism.UG.cT _ _ * _ * _ = _
  have := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA] at this
  unfold Formalism.UG.cT JR
  rw [← matchPair_map_cA]
  have e : (incM D.host.F T.gramᵀ)ᵀ = incM D.host.F T.gram := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_map]
  rw [e] at this
  exact (Matrix.mul_assoc _ _ _).trans this

theorem matchPair_keeps_inv_gram (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) :
    b.1.1ᵀ * incM D.host.F S.gram⁻¹ * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F S.gram⁻¹ := by
  have hb : b.1.1ᵀ * incM D.host.F JB * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JB := b.2
  have hxi : IsUnit (incA D D.host.xi0) := (isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have hsc : (incM D.host.F (D.host.xi0 • S.gram⁻¹) : Matrix (Fin S.rank) (Fin S.rank) (AE D)) =
      (incA D D.host.xi0 : AE D) • (incM D.host.F S.gram⁻¹ : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, incA]
  have t1 : ∀ (r : AE D) (X Y : Matrix (Fin S.rank) (Fin S.rank) (AE D)), X * (r • Y) = r • (X * Y) :=
    fun r X Y => Matrix.mul_smul X r Y
  have t2 : ∀ (r : AE D) (X Y : Matrix (Fin S.rank) (Fin S.rank) (AE D)), (r • X) * Y = r • (X * Y) :=
    fun r X Y => Matrix.smul_mul r X Y
  have e1 := congrArg (fun M => ξ • M) hb
  rw [← t2, ← t1, hB, hsc] at e1
  have e2 : b.1.1ᵀ * ((incA D D.host.xi0 : AE D) • incM D.host.F S.gram⁻¹) * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (incA D D.host.xi0 : AE D) • (b.1.1ᵀ * incM D.host.F S.gram⁻¹ * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) := by
    rw [t1, t2]
  rw [e2] at e1
  exact hxi.smul_left_cancel.1 e1



theorem matchPair_memS (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) :
    ∃ G : GL (Fin S.rank) (AE D), G.1 = (b⁻¹).1.1ᵀ ∧ G ∈ HR (AF D.host.F) D.sp.cm.sig S.gram := by
  have hBB : b.1.1 * (b⁻¹).1.1 = 1 := Units.mul_inv b.1
  have hBB' : (b⁻¹).1.1 * b.1.1 = 1 := Units.inv_mul b.1
  have hdet : IsUnit S.gram.det := (Formalism.L2.Theta.gram_det_ne S).isUnit
  have hPQ : incM D.host.F S.gram⁻¹ * incM D.host.F S.gram = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP : incM D.host.F S.gram * incM D.host.F S.gram⁻¹ = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hCC : (b⁻¹).1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = 1 := by
    have := map_mul ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig).toRingHom.mapMatrix :
      Matrix (Fin S.rank) (Fin S.rank) (AE D) →+* Matrix (Fin S.rank) (Fin S.rank) (AE D)) (b⁻¹).1.1 b.1.1
    rw [hBB', map_one] at this
    exact this.symm
  have key := matchPair_inv_transpose _ _ _ _ _ _ hBB hPQ hQP hCC (matchPair_keeps_inv_gram D S JB ξ hB b)
  refine ⟨⟨(b⁻¹).1.1ᵀ, b.1.1ᵀ, by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩, rfl, ?_⟩
  show Formalism.UG.cT _ _ * _ * _ = _
  unfold Formalism.UG.cT JR
  rw [← matchPair_map_cA, Matrix.transpose_map, Matrix.transpose_transpose]
  exact key

theorem match_pair : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  intro D S T JA JB ξ hA hB a b
  obtain ⟨G, hG, hGm⟩ := matchPair_memS D S JB ξ hB b
  exact ⟨⟨G, hGm⟩, ⟨a.1, matchPair_memT D T JA hA a⟩, rfl, hG⟩

end GlobalTheory.WeilSchrodinger

end
end

section

open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.HermIso

theorem posIndex_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) :
    GlobalTheory.Inertia.posIndex M = r := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
    Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))
  have hD : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1) = D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [D, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map (starRingEnd ℂ) = D.submatrix e.symm e.symm := by
    rw [← hD, ← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply]
  have hdet : A'.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hA'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, Matrix.det_submatrix_equiv_self,
      Matrix.det_diagonal] at h1
    simp [Fintype.prod_sum_type] at h1
    exact pow_ne_zero s (by norm_num) h1.symm
  rw [← GlobalTheory.Inertia.posIndex_congr M hdet, hA', GlobalTheory.Inertia.posIndex_submatrix_equiv,
    GlobalTheory.Inertia.posIndex_diagonal]
  rw [Finset.card_filter, Fintype.sum_sum_type]
  simp

theorem exists_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), 3 ≤ n → 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∃ x : Fin n → E, x ≠ 0 ∧ form σ Y.J x x = 0 := by
  intro F E _ _ _ _ _ σ B hB n Y r s hn hr hs hY
  obtain ⟨-, hEC, h2, hconj⟩ := hB.cm
  obtain ⟨w0⟩ : Nonempty (InfinitePlace E) := inferInstance
  have invol : ∀ x, σ (σ x) = x := fun x =>
    w0.embedding.injective (by rw [hconj, hconj, star_star])
  let σe : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext invol) (AlgHom.ext invol)
  have hne : σe ≠ 1 := by
    intro h
    have hid : ∀ x, σ x = x := fun x => by simpa [σe] using DFunLike.congr_fun h x
    have hre : ComplexEmbedding.IsReal w0.embedding :=
      ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
        rw [ComplexEmbedding.conjugate_coe_eq]
        have := hconj w0.embedding x
        rw [hid] at this
        exact this.symm)
    exact InfinitePlace.not_isReal_iff_isComplex.2 (hEC.isComplex w0) (InfinitePlace.isReal_iff.2 hre)
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨hc, hF, θ, hθ0, hθ⟩ := GlobalTheory.HermGlobal.involutive_and_fixed hne
  obtain ⟨P, g, hP, hPg, hgf, hg0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E))
    two_ne_zero (fun t => invol t) (G := Y.J) (fun a b => hY.herm b a)
  have hgf' : ∀ i, σ (g i) = g i := fun i => hgf i
  have key : ∀ y : Fin n → E,
      form σ Y.J (P *ᵥ y) (P *ᵥ y) = y ⬝ᵥ Matrix.diagonal g *ᵥ (fun i => σ (y i)) := by
    intro y
    have h1 : (fun i => σ ((P *ᵥ y) i)) = (P.map (σ : E →+* E)) *ᵥ (fun i => σ (y i)) := by
      funext i

      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [form, h1, ← hPg]
    simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec]
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  by_cases hz : ∃ i, g i = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨P *ᵥ Pi.single i 1, fun h => ?_, ?_⟩
    · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) i
      simp at this
    · rw [key]
      simp [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply, hi]
  push_neg at hz
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsg : ∀ τ : E →+* ℂ, (∀ x, τ (σe x) = conj (τ x)) →
      ∃ i : Fin m, (0 < (τ (g i.succ)).re ↔ 0 < (τ (-g 0)).re) := by
    intro τ _
    have hre : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
      ComplexEmbedding.isReal_iff.2 (RingHom.ext fun c => by
        rw [ComplexEmbedding.conjugate_coe_eq]
        have := hconj τ (algebraMap F E c)
        rw [AlgHom.commutes] at this
        exact this.symm)
    have hw : (InfinitePlace.mk (τ.comp (algebraMap F E))).embedding = τ.comp (algebraMap F E) :=
      InfinitePlace.embedding_mk_eq_of_isReal hre
    set w := InfinitePlace.mk (τ.comp (algebraMap F E))
    set τ' := (B.emb w).1
    have hτ' : ∀ c : F, τ' (algebraMap F E c) = τ (algebraMap F E c) := fun c => by
      have := congrArg (fun f => f c) ((B.emb w).2.trans hw)
      simpa using this
    have hgτ : ∀ k, τ' (g k) = τ (g k) := fun k => by
      obtain ⟨c, hc'⟩ := (hF (g k)).1 (hgf' k)
      rw [← hc', hτ']
    have hcong : (Matrix.diagonal g).map τ' =
        (P.map τ')ᵀ * Y.J.map τ' * (P.map τ').map (starRingEnd ℂ) := by
      rw [← hPg, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
      congr 1
      ext a b
      simp [hconj]
    have hPd : (P.map τ').det ≠ 0 := by
      rw [show (P.map τ').det = τ' P.det from (RingHom.map_det τ' P).symm]
      exact (map_ne_zero τ').2 hP
    have hcount : (Finset.univ.filter fun k => 0 < (τ (g k)).re).card = r := by
      have := GlobalTheory.Inertia.posIndex_congr (Y.J.map τ') hPd
      rw [← hcong, posIndex_of_hasSig (hY.sig w), Matrix.diagonal_map (map_zero _),
        GlobalTheory.Inertia.posIndex_diagonal] at this
      simpa [hgτ] using this
    have hrn : r < m + 1 := by have := (hY.sig w).1; omega
    have him : (τ (g 0)).im = 0 := by
      have h := hconj τ (g 0)
      rw [hgf' 0] at h
      exact Complex.conj_eq_iff_im.1 h.symm
    have hne0 : τ (g 0) ≠ 0 := (map_ne_zero τ).2 (hz 0)
    by_cases hp : 0 < (τ (g 0)).re
    · obtain ⟨k, hk⟩ : ∃ k, ¬ 0 < (τ (g k)).re := by
        by_contra hall
        push_neg at hall
        have h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = Finset.univ :=
          Finset.filter_true_of_mem fun k _ => hall k
        rw [h', Finset.card_univ, Fintype.card_fin] at hcount
        omega
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hk hp)
      refine ⟨i, iff_of_false hk ?_⟩
      simp only [map_neg, Complex.neg_re]
      linarith
    · have hneg : (τ (g 0)).re < 0 := by
        rcases lt_or_eq_of_le (not_lt.1 hp) with h | h
        · exact h
        · exact absurd (Complex.ext (by simpa using h) (by simpa using him)) hne0
      obtain ⟨k, hk⟩ : ∃ k, 0 < (τ (g k)).re := by
        by_contra hall
        push_neg at hall
        have h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = ∅ :=
          Finset.filter_false_of_mem fun k _ => not_lt.2 (hall k)
        rw [h', Finset.card_empty] at hcount
        omega
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hp hk)
      refine ⟨i, iff_of_true hk ?_⟩
      simp only [map_neg, Complex.neg_re]
      linarith
  obtain ⟨z, hz'⟩ := GlobalTheory.HermGlobal.exists_represent hc hF hθ0 hθ (r := m) (by omega)
    (g := fun i => g i.succ) (fun i => hgf' _) (fun i => hz _) (b := -g 0)
    (by simp [σe, hgf']) (neg_ne_zero.2 (hz 0)) hsg
  refine ⟨P *ᵥ Fin.cons 1 z, fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) 0
    simp at this
  · rw [key]
    simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      map_one, one_mul, mul_one] at hz' ⊢
    simp only [σe, Function.comp_apply, RingHom.coe_coe, AlgEquiv.ofAlgHom_apply] at hz'
    linear_combination hz'

end GlobalTheory.HermIso
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaDerivQuasi

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symplOHF_add_left' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 (x + x') y = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x' y := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem symplOHF_add_right' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT xi0 x (y + y') = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x y' := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

end GlobalTheory.ThetaDerivQuasi

theorem GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
      deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w)) 0 = B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) * deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ _ f hf L _ _ γ w
  have key : ∀ t : ℝ, Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w) =
      B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
        Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f w := by
    intro t
    simp only [Formalism.IndefR.DatumF.heisOF]
    rw [add_assoc, hf.quasi γ (w + L t), GlobalTheory.ThetaDerivQuasi.symplOHF_add_left',
      GlobalTheory.ThetaDerivQuasi.symplOHF_add_right', neg_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    have h1 : B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) (L t)) *
        B.ψ (-Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) (L t)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L t)) *
      B.ψ (-Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w) * f (w + L t)) * h1
  simp_rw [key]
  exact congrFun (deriv_const_mul_field' _) 0

end
end
