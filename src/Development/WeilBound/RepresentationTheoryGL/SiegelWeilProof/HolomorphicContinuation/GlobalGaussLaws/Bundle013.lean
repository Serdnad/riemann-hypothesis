module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle011
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle008
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle020
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.PosDef
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
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

noncomputable section

open Matrix Topology
open scoped Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.StdUnn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DenseP

open Formalism.IndefR.Eqv (psiT psiT_inclR)

variable {D : D7} {n : ℕ}

theorem denseRange_of_not_isReal' {K : Type} [Field K] (σ : K →+* ℂ)
    (h : ¬ NumberField.ComplexEmbedding.IsReal σ) : DenseRange σ := by
  have hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ) :=
    Subfield.isClosed_topologicalClosure _
  rcases Complex.subfield_eq_of_closed hc with h1 | h1
  · exfalso
    apply h
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have hx : σ x ∈ σ.fieldRange.topologicalClosure := Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h1] at hx
    obtain ⟨r, hr⟩ := hx
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · have : closure (Set.range σ) = Set.univ := by
      have := congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1
      exact this
    exact dense_iff_closure_eq.2 this

theorem tauE_not_real (τ : D.what₂.Tau) : ¬ NumberField.ComplexEmbedding.IsReal (tauE D τ) := by
  intro h
  rw [NumberField.ComplexEmbedding.isReal_iff] at h
  have h1 : starRingEnd ℂ (tauE D τ D.host.xi0) = tauE D τ D.host.xi0 := by
    have := congrArg (fun f : D.host.E →+* ℂ => f D.host.xi0) h
    simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this
  have h2 : tauE D τ (star D.host.xi0) = starRingEnd ℂ (tauE D τ D.host.xi0) := Formalism.IndefR.Eqv.tauE_star D τ _
  rw [Formalism.IndefR.Datum.Brg.star_purely_imaginary_eq_neg, map_neg, h1] at h2
  have h3 : tauE D τ D.host.xi0 = 0 := by
    have : (2 : ℂ) * tauE D τ D.host.xi0 = 0 := by linear_combination -h2
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  exact Formalism.IndefR.Fin.embedding_xi_zero_ne_zero ((map_eq_zero_iff _ (tauE D τ).injective).1 h3)

theorem denseRange_tauE (τ : D.what₂.Tau) : DenseRange (tauE D τ) := denseRange_of_not_isReal' _ (tauE_not_real τ)

theorem sig_apply (x : D.host.E) : D.sp.cm.sig x = star x := rfl

theorem cT_map_tauE (τ : D.what₂.Tau) {k : ℕ} (u : Matrix (Fin k) (Fin k) D.host.E) :
    (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u).map (tauE D τ) = (u.map (tauE D τ))ᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply, sig_apply, Formalism.IndefR.Eqv.tauE_star]

theorem block_matrix_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  rw [blk4, blk4, ← Matrix.submatrix_map, Matrix.fromBlocks_map]

theorem map0 (τ : D.what₂.Tau) : (0 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = 0 :=
  map_zero (RingHom.mapMatrix (tauE D τ))

theorem map1 (τ : D.what₂.Tau) : (1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = 1 :=
  map_one (RingHom.mapMatrix (tauE D τ))

theorem mapn1 (τ : D.what₂.Tau) : (-1 : Matrix (Fin n) (Fin n) D.host.E).map (tauE D τ) = -1 := by
  show RingHom.mapMatrix (tauE D τ) (-1) = -1
  rw [map_neg, map_one]

theorem map_smul_E (τ : D.what₂.Tau) {k : ℕ} (c : D.host.E) (X : Matrix (Fin k) (Fin k) D.host.E) :
    (c • X).map (tauE D τ) = (tauE D τ c) • X.map (tauE D τ) := by
  ext i j; simp [Matrix.map_apply, Matrix.smul_apply]

theorem Jst_map (τ : D.what₂.Tau) : (Jst D n).map (tauE D τ) = Glob.reidx (JJ n) := by
  rw [Jst, block_matrix_map, map0, map1, mapn1]
  rfl

theorem reidx_mul (a b : M2 n) : Glob.reidx (a * b) = Glob.reidx a * Glob.reidx b := by
  simp [Glob.reidx, Matrix.submatrix_mul_equiv]

theorem reidx_one : Glob.reidx (1 : M2 n) = 1 := by
  simp [Glob.reidx, Matrix.submatrix_one_equiv]

theorem reidx_conjTranspose (a : M2 n) : Glob.reidx aᴴ = (Glob.reidx a)ᴴ := by
  simp [Glob.reidx, Matrix.conjTranspose_submatrix]

theorem inG_JJc : InG (JJ n) := by
  simp only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp

theorem mat_one : mat (1 : G D n) = 1 := by simp [mat]

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by simp [mat]

theorem ratPt_of (τ : D.what₂.Tau) (u : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (M : M2 n) (hM : InG M)
    (hu : u.map (tauE D τ) = Glob.reidx M) : ∃ γ ∈ GF D n, (mat γ).map (psiT D τ) = Glob.reidx M := by
  have hdet : IsUnit u.det := by
    have h1 : tauE D τ u.det = M.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hu, Glob.reidx, Matrix.det_submatrix_equiv_self]
    have h2 : M.det ≠ 0 := (isUnit_det_of_inG hM).ne_zero
    refine isUnit_iff_ne_zero.2 fun h0 => h2 ?_
    rw [← h1, h0, map_zero]
  let U : GL (Fin (n + n)) D.host.E := ⟨u, u⁻¹, Matrix.mul_nonsing_inv u hdet, Matrix.nonsing_inv_mul u hdet⟩
  have hU : U ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (Jst D n) := by
    show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u * Jst D n * u = Jst D n
    have key : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) u * Jst D n * u).map (tauE D τ) =
        (Jst D n).map (tauE D τ) := by
      rw [Matrix.map_mul, Matrix.map_mul, cT_map_tauE, Jst_map, hu, ← reidx_conjTranspose, ← reidx_mul, ← reidx_mul, hM]
    exact Matrix.map_injective (tauE D τ).injective key
  refine ⟨GlobalTheory.AdelicU.ratEmb D.sp.cm.sig (Jst D n) ⟨U, hU⟩, ?_, ?_⟩
  · show _ ∈ GlobalTheory.AdelicU.ratPts D.sp.cm.sig (Jst D n)
    rw [← GlobalTheory.AdelicU.range_ratEmb]; exact MonoidHom.mem_range.2 ⟨_, rfl⟩
  · show (u.map (inclR (AF D.host.F))).map (psiT D τ) = _
    rw [Matrix.map_map]
    have : (⇑(psiT D τ) ∘ ⇑(inclR (AF D.host.F))) = ⇑(tauE D τ) := funext fun e => psiT_inclR D τ e
    rw [this, hu]

def gam (D : D7) (n : ℕ) (τ : D.what₂.Tau) : Subgroup (GR n) where
  carrier := {y | ∃ γ ∈ GF D n, (mat γ).map (psiT D τ) = Glob.reidx (mR y)}
  one_mem' := ⟨1, one_mem _, by
    rw [mat_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact reidx_one.symm⟩
  mul_mem' := by
    rintro a b ⟨γ, hγ, ea⟩ ⟨γ', hγ', eb⟩
    refine ⟨γ * γ', mul_mem hγ hγ', ?_⟩
    rw [mat_mul, Matrix.map_mul, ea, eb]
    exact (reidx_mul _ _).symm
  inv_mem' := by
    rintro a ⟨γ, hγ, ea⟩
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    have h1 : (mat γ⁻¹).map (psiT D τ) * (mat γ).map (psiT D τ) = 1 := by
      rw [← Matrix.map_mul, ← mat_mul, inv_mul_cancel, mat_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : Glob.reidx (mR a) * Glob.reidx (mR a⁻¹) = 1 := by
      rw [← reidx_mul]
      show Glob.reidx (mR (a * a⁻¹)) = 1
      rw [mul_inv_cancel]; exact reidx_one
    calc (mat γ⁻¹).map (psiT D τ) = (mat γ⁻¹).map (psiT D τ) * (Glob.reidx (mR a) * Glob.reidx (mR a⁻¹)) := by
          rw [h2, Matrix.mul_one]
      _ = Glob.reidx (mR a⁻¹) := by rw [← Matrix.mul_assoc, ← ea, h1, Matrix.one_mul]

theorem mkGR_ext {g : M2 n} (hg : InG g) {h : GR n} (e : mR h = g) : h = mkGR g hg :=
  Subtype.ext (Units.ext e)

theorem gens_mem (τ : D.what₂.Tau) (h : GR n) (hh : IsNElt h ∨ IsMElt h ∨ IsWElt h) :
    h ∈ (gam D n τ).topologicalClosure := by
  rcases hh with ⟨b, hb, e⟩ | ⟨A, hA, e⟩ | e
  · have hh : h = nuE b := by
      rw [mkGR_ext (inG_nUh (hpart_herm b)) (show mR h = nU (hpart b) by rw [hpart_of_herm hb]; exact e)]; rfl
    rw [hh]
    refine closure_mono ?_ (nuE_mem_closure (tauE D τ) (denseRange_tauE τ) b)
    rintro _ ⟨e', rfl⟩
    have hβ : ((2 : D.host.E)⁻¹ • (e' + Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')).map (tauE D τ) =
        hpart (e'.map (tauE D τ)) := by
      rw [map_smul_E, Matrix.map_add _ (map_add (tauE D τ)), cT_map_tauE, map_inv₀, map_ofNat, hpart, one_div]
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (blk4 1 ((2 : D.host.E)⁻¹ • (e' + Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')) 0 1)
      (nU (hpart (e'.map (tauE D τ)))) (inG_nUh (hpart_herm _)) (by
        rw [block_matrix_map, map0, map1, hβ]
        rfl)
    exact ⟨γ, hγ, he⟩
  · have hh : h = mlE A := by rw [mlE_of hA]; exact mkGR_ext (inG_mL hA) e
    rw [hh]
    refine closure_mono ?_ (mlE_mem_closure (tauE D τ) (denseRange_tauE τ) A hA)
    rintro _ ⟨B, ⟨hB, e', rfl⟩, rfl⟩
    have hdet : IsUnit e'.det := by
      have h1 : tauE D τ e'.det = (e'.map (tauE D τ)).det := by rw [RingHom.map_det, RingHom.mapMatrix_apply]
      refine isUnit_iff_ne_zero.2 fun h0 => (hB : IsUnit (e'.map (tauE D τ)).det).ne_zero ?_
      rw [← h1, h0, map_zero]
    have hcd : IsUnit (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e').det := by
      have h1 : tauE D τ (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e').det = ((e'.map (tauE D τ))ᴴ).det := by
        rw [RingHom.map_det, RingHom.mapMatrix_apply, cT_map_tauE]
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have : ((e'.map (tauE D τ))ᴴ).det = 0 := by rw [← h1, h0, map_zero]
      rw [Matrix.det_conjTranspose, star_eq_zero] at this
      exact (hB : IsUnit (e'.map (tauE D τ)).det).ne_zero this
    have hinv : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')⁻¹).map (tauE D τ) =
        ((e'.map (tauE D τ))⁻¹)ᴴ := by
      rw [Matrix.conjTranspose_nonsing_inv, ← cT_map_tauE]
      refine (Matrix.inv_eq_right_inv ?_).symm
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hcd, Matrix.map_one _ (map_zero _) (map_one _)]
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (blk4 e' 0 0 (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e')⁻¹)
      (fromBlocks (e'.map (tauE D τ)) 0 0 ((e'.map (tauE D τ))⁻¹)ᴴ) (inG_mL hB) (by
        rw [block_matrix_map, hinv, map0]
        rfl)
    refine ⟨γ, hγ, ?_⟩
    rw [he, mlE_of hB]
    rfl
  · refine (gam D n τ).le_topologicalClosure ?_
    obtain ⟨γ, hγ, he⟩ := ratPt_of τ (Jst D n) (JJ n) inG_JJc (Jst_map τ)
    exact ⟨γ, hγ, by rw [he, e]⟩

theorem gam_dense (hgen : GenSt) (τ : D.what₂.Tau) (g : GR n) : g ∈ closure (gam D n τ : Set (GR n)) := by
  have h1 : Subgroup.closure {h : GR n | IsNElt h ∨ IsMElt h ∨ IsWElt h} ≤ (gam D n τ).topologicalClosure :=
    (Subgroup.closure_le _).2 fun h hh => gens_mem τ h hh
  exact h1 (hgen n g)

end PositivityTheory.Rg.Sw.Glob.DenseP
end
end

section

noncomputable section

set_option linter.style.haveILetI false

open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {R : Type} [CommRing R] {n : ℕ}

theorem uni_blocks (σ : R →+* R) (h : Matrix (Fin (n + n)) (Fin (n + n)) R) (hu : Uni σ h) :
    Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₁ - Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₁ = 1 ∧
      Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₂ = Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₂ := by
  have e := congrArg bf hu
  unfold J2 at e
  rw [bf_mul, bf_mul, bf_cT, block_matrix_to_fromBlocks, ← fromBlocks_toBlocks (bf h), cT_fromBlocks, fromBlocks_multiply,
    fromBlocks_multiply] at e
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add] at e
  obtain ⟨-, -, e3, e4⟩ := fromBlocks_inj.1 e
  refine ⟨?_, ?_⟩
  · have : -(Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₁) + Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₁ = -1 := e3
    rw [← neg_neg (1 : Matrix (Fin n) (Fin n) R), ← this]; abel
  · have : -(Formalism.UG.cT σ (bf h).toBlocks₂₂ * (bf h).toBlocks₁₂) + Formalism.UG.cT σ (bf h).toBlocks₁₂ * (bf h).toBlocks₂₂ = 0 := e4
    rw [neg_add_eq_zero] at this; exact this

theorem schur {K : Type} [CommRing K] (P Q A B C D : Matrix (Fin n) (Fin n) K) (h1 : P * A - Q * C = 1) (h2 : P * B = Q * D)
    (hD : IsUnit D.det) : IsUnit P.det := by
  have hQ : Q = P * B * D⁻¹ := by rw [h2, Matrix.mul_assoc, mul_nonsing_inv _ hD, Matrix.mul_one]
  have : P * (A - B * D⁻¹ * C) = 1 := by
    rw [← h1, hQ]; simp only [Matrix.mul_sub, Matrix.mul_assoc]
  have hd := congrArg Matrix.det this
  rw [det_mul, det_one] at hd
  exact ⟨⟨_, _, hd, by rw [mul_comm]; exact hd⟩, rfl⟩

theorem lift2 (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal] (hne : 𝔪.comap σ ≠ 𝔪)
    (s t : R ⧸ 𝔪) : ∃ x : R, Ideal.Quotient.mk 𝔪 x = s ∧ Ideal.Quotient.mk 𝔪 (σ x) = t := by
  have hsurj : Function.Surjective σ := fun y => ⟨σ y, hσ y⟩
  have h' : (𝔪.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
  have hsup : 𝔪 ⊔ 𝔪.comap σ = ⊤ := Ideal.IsMaximal.coprime_of_ne h𝔪 h' (Ne.symm hne)
  have h1 : (1 : R) ∈ 𝔪 ⊔ 𝔪.comap σ := hsup ▸ Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.1 h1
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective t
  have hf' : σ f ∈ 𝔪 := hf
  have he0 : Ideal.Quotient.mk 𝔪 e = 0 := Ideal.Quotient.eq_zero_iff_mem.2 he
  have hf1 : Ideal.Quotient.mk 𝔪 f = 1 := by
    rw [show f = 1 - e by rw [← hef]; ring, map_sub, map_one, he0, sub_zero]
  have hsf : Ideal.Quotient.mk 𝔪 (σ f) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hf'
  have hse : Ideal.Quotient.mk 𝔪 (σ e) = 1 := by
    rw [show e = 1 - f by rw [← hef]; ring, map_sub, map_one, map_sub, map_one, hsf, sub_zero]
  refine ⟨u * f + σ y * e, ?_, ?_⟩
  · rw [map_add (f := _), map_mul, map_mul, hf1, he0]; ring
  · rw [map_add (f := _), map_mul, map_mul, map_add (f := _), map_mul, map_mul, hσ, hsf, hse]; ring

theorem caseB (hS : LocRedSplit) (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) (𝔪 : Ideal R) [h𝔪 : 𝔪.IsMaximal]
    (hne : 𝔪.comap σ ≠ 𝔪) (horb : ∀ 𝔫 : Ideal R, 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap σ)
    (g : Matrix (Fin (n + n)) (Fin (n + n)) R) (hg : Uni σ g) (hgu : IsUnit g.det) :
    ∃ (a : Matrix (Fin n) (Fin n) R) (I : Finset (Fin n)), IsUnit a.det ∧
      IsUnit (blkDm (g * GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹ * wIm I)).det := by
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hdet : IsUnit (g.map (Ideal.Quotient.mk 𝔪)).det := by rw [← det_map]; exact hgu.map _
  obtain ⟨ab, db, I, hI⟩ := hS (R ⧸ 𝔪) n (Matrix.nonsingInvUnit _ hdet)
  choose x hx using fun i j => lift2 σ hσ 𝔪 hne ((ab : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) i j)
    (((db⁻¹ : GL (Fin n) (R ⧸ 𝔪)) : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) j i)
  let a : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => x i j
  have ha1 : a.map (Ideal.Quotient.mk 𝔪) = ab := by ext i j; exact (hx i j).1
  have ha2 : (Formalism.UG.cT σ a).map (Ideal.Quotient.mk 𝔪) = ((db⁻¹ : GL (Fin n) (R ⧸ 𝔪)) : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) := by
    ext i j; exact (hx j i).2
  have hab : IsUnit (ab : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)).det := Matrix.isUnits_det_units ab
  have hdb : IsUnit ((db⁻¹ : GL (Fin n) (R ⧸ 𝔪)) : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)).det := Matrix.isUnits_det_units _
  have hadet : IsUnit a.det := by
    refine isUnit_of σ 𝔪 horb _ ?_ ?_
    · intro hm
      have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
      rw [det_map, ha1] at h0
      exact hab.ne_zero h0
    · intro hm
      have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
      rw [← det_cT, det_map, ha2] at h0
      exact hdb.ne_zero h0
  have hca : IsUnit (Formalism.UG.cT σ a).det := by rw [det_cT]; exact hadet.map σ
  have hinv : ((Formalism.UG.cT σ a)⁻¹).map (Ideal.Quotient.mk 𝔪) = (db : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) := by
    rw [map_nonsing_inv _ _ hca, ha2, Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnits_det_units db)]
  set h := g * GlobalTheory.StdUnn.blk4 a 0 0 (Formalism.UG.cT σ a)⁻¹ * wIm I with hh
  have hmap : h.map (Ideal.Quotient.mk 𝔪) =
      g.map (Ideal.Quotient.mk 𝔪) * GlobalTheory.StdUnn.blk4 (ab : Matrix (Fin n) (Fin n) (R ⧸ 𝔪)) 0 0 db * wIm I := by
    rw [hh, Matrix.map_mul, Matrix.map_mul, block_matrix_map, ha1, hinv, wIm_map, Matrix.map_zero _ (map_zero _)]
  have hδ : IsUnit ((blkDm h).map (Ideal.Quotient.mk 𝔪)).det := by rw [blkDm_map, hmap]; exact hI
  refine ⟨a, I, hadet, isUnit_of σ 𝔪 horb _ ?_ ?_⟩
  · intro hm
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [det_map] at h0
    exact hδ.ne_zero h0
  · have hu : Uni σ h := (hg.mul (uni_levi σ hσ a hadet)).mul (uni_wIm σ I)
    obtain ⟨e1, e2⟩ := uni_blocks σ h hu
    have hπσ : ∀ y : Matrix (Fin n) (Fin n) R, (Formalism.UG.cT σ y).map (Ideal.Quotient.mk 𝔪) =
        (Formalism.UG.cT σ y).map (Ideal.Quotient.mk 𝔪) := fun _ => rfl
    have e1' := congrArg (fun M => M.map (Ideal.Quotient.mk 𝔪)) e1
    have e2' := congrArg (fun M => M.map (Ideal.Quotient.mk 𝔪)) e2
    simp only [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at e1' e2'
    have hD : IsUnit ((bf h).toBlocks₂₂.map (Ideal.Quotient.mk 𝔪)).det := hδ
    have hP := schur _ _ _ _ _ _ e1' e2' hD
    intro hm
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 hm
    rw [blkDm_eq, ← det_cT, det_map] at h0
    exact hP.ne_zero h0

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
end
end

section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix Formalism.IndefR.Datum

namespace PositivityTheory.Rg.Sw.Glob

theorem exists_unitary_diag {k : ℕ} {T : Matrix (Fin k) (Fin k) ℂ} (hT : T.IsHermitian) :
    ∃ (W : Matrix (Fin k) (Fin k) ℂ) (lam : Fin k → ℝ), Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      Wᴴ * T * W = diagonal (fun i => (lam i : ℂ)) := by
  refine ⟨(hT.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ), hT.eigenvalues, ?_, ?_, ?_⟩
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  · have := hT.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [star_eq_conjTranspose, Function.comp_def] using this

theorem exists_normal {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ} (hM : M.PosDef) : ∃ C : Matrix (Fin k) (Fin k) ℂ,
    Cᴴ * M * C = 1 := by
  have hpos := hM.eigenvalues_pos
  have hUU : (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)ᴴ * (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = 1 := by
    rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hd : (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ)ᴴ * M * (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) =
      diagonal (fun i => (hM.1.eigenvalues i : ℂ)) := by
    have := hM.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [star_eq_conjTranspose, Function.comp_def] using this
  generalize (hM.1.eigenvectorUnitary : Matrix (Fin k) (Fin k) ℂ) = U at hUU hd
  generalize hM.1.eigenvalues = μ at hpos hd
  refine ⟨U * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)), ?_⟩
  have hCd : (diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)))ᴴ = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp [Complex.conj_ofReal]
  rw [conjTranspose_mul, hCd]
  calc diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * Uᴴ * M * (U * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)))
      = diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) * (Uᴴ * M * U) * diagonal (fun i => ((Real.sqrt (μ i))⁻¹ : ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hd, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        have hp := hpos i
        have hs : (Real.sqrt (μ i)) ^ 2 = μ i := Real.sq_sqrt hp.le
        have hs0 : Real.sqrt (μ i) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
        have hc : ((Real.sqrt (μ i) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
        field_simp
        rw [← Complex.ofReal_pow, hs]

theorem frame_of_cartan {k : ℕ} (G S : Matrix (Fin k) (Fin k) ℂ) (h : IsCartanInv G S) :
    ∃ (ε : Fin k → Bool) (fr : Matrix (Fin k) (Fin k) ℂ), IsUnit fr.det ∧ frᴴ * G * fr = diagonal (sgn ε) ∧
      frᴴ * (G * S) * fr = 1 := by
  obtain ⟨hSS, hSG, hM⟩ := h
  have hMh : (G * S)ᴴ = G * S := hM.1
  have hGh : Gᴴ = G := by
    have h1 : Sᴴ * Sᴴ = 1 := by rw [← conjTranspose_mul, hSS, conjTranspose_one]
    have h2 : Sᴴ * Gᴴ = G * S := by rw [← conjTranspose_mul]; exact hMh
    calc Gᴴ = Sᴴ * Sᴴ * Gᴴ := by rw [h1, Matrix.one_mul]
      _ = Sᴴ * (Sᴴ * Gᴴ) := by rw [Matrix.mul_assoc]
      _ = Sᴴ * (G * S) := by rw [h2]
      _ = Sᴴ * G * S := by rw [Matrix.mul_assoc]
      _ = G := hSG
  obtain ⟨C, hCMC⟩ := exists_normal hM
  have hCCM : C * (Cᴴ * (G * S)) = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl (Fin k))).mp hCMC
  have hTh : (Cᴴ * G * C).IsHermitian := by
    show (Cᴴ * G * C)ᴴ = Cᴴ * G * C
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hGh, Matrix.mul_assoc]
  have hTT : (Cᴴ * G * C) * (Cᴴ * G * C) = 1 := by
    have e1 : C * Cᴴ * G = S := by
      have : G = G * S * S := by rw [Matrix.mul_assoc, hSS, Matrix.mul_one]
      calc C * Cᴴ * G = C * (Cᴴ * (G * S)) * S := by
            conv_lhs => rw [this]
            simp only [Matrix.mul_assoc]
        _ = S := by rw [hCCM, Matrix.one_mul]
    calc (Cᴴ * G * C) * (Cᴴ * G * C) = Cᴴ * G * (C * Cᴴ * G) * C := by simp only [Matrix.mul_assoc]
      _ = Cᴴ * (G * S) * C := by rw [e1]; simp only [Matrix.mul_assoc]
      _ = 1 := hCMC
  obtain ⟨W, lam, hWW, hWW', hTd⟩ := exists_unitary_diag hTh
  have hsq : ∀ i, lam i = 1 ∨ lam i = -1 := by
    have hD : diagonal (fun i => (lam i : ℂ)) * diagonal (fun i => (lam i : ℂ)) = 1 := by
      rw [← hTd]
      calc Wᴴ * (Cᴴ * G * C) * W * (Wᴴ * (Cᴴ * G * C) * W)
          = Wᴴ * (Cᴴ * G * C) * (W * Wᴴ) * (Cᴴ * G * C) * W := by simp only [Matrix.mul_assoc]
        _ = 1 := by
          rw [hWW', Matrix.mul_one, Matrix.mul_assoc Wᴴ (Cᴴ * G * C) (Cᴴ * G * C), hTT, Matrix.mul_one, hWW]
    intro i
    have := congrFun (congrFun hD i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, one_apply_eq] at this
    have h2 : (lam i) * (lam i) = 1 := by exact_mod_cast this
    have h3 : (lam i - 1) * (lam i + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h3 with h | h
    · left; linarith
    · right; linarith
  refine ⟨fun i => decide (lam i = 1), C * W, ?_, ?_, ?_⟩
  · have hinv : ((C * W)ᴴ * (G * S)) * (C * W) = 1 := by
      rw [conjTranspose_mul]
      calc Wᴴ * Cᴴ * (G * S) * (C * W) = Wᴴ * (Cᴴ * (G * S) * C) * W := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hCMC, Matrix.mul_one, hWW]
    exact isUnit_det_of_left_inverse hinv
  · rw [conjTranspose_mul]
    calc Wᴴ * Cᴴ * G * (C * W) = Wᴴ * (Cᴴ * G * C) * W := by simp only [Matrix.mul_assoc]
      _ = diagonal (fun i => (lam i : ℂ)) := hTd
      _ = diagonal (sgn fun i => decide (lam i = 1)) := by
          congr 1; funext i
          simp only [sgn]
          rcases hsq i with h | h
          · simp [h]
          · simp [h] <;> norm_num
  · rw [conjTranspose_mul]
    calc Wᴴ * Cᴴ * (G * S) * (C * W) = Wᴴ * (Cᴴ * (G * S) * C) * W := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCMC, Matrix.mul_one, hWW]

theorem sFrame : SFrame := by
  intro D V τ s h
  exact frame_of_cartan _ _ h

end PositivityTheory.Rg.Sw.Glob
end
end
