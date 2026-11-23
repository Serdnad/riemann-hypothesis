module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle195
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle005
import Formalism.LocalToGlobal.HermitianForms.TiedBrCl
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

noncomputable section

namespace GlobalTheory.FormsRatOfInt

theorem intSpan_le_ratSpan (D : D7) {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) :
    Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w lam ≤ Formalism.L2.Forms.RatSpan D lam := by
  unfold Formalism.MainNotions.product_first_zeroth_parts.IntSpan Formalism.L2.Forms.RatSpan
  apply AddSubgroup.closure_mono
  rintro p ⟨r, f, -, hf, rfl⟩
  exact ⟨r, f, hf, rfl⟩

theorem exists_ptEmb_of_coord_int : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → GL (Fin (D.R.N D.R.m - 1)) D.host.E) (w : D.what₂.places.Pl), ∀ z ∈ (D.fm u).ptC, (∀ c, Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w z c ∈ Formalism.MainNotions.product_first_zeroth_parts.IntSpan D w (D.fm u).sg) → ∃ y, (D.fm u).ptEmb y = z := by
  intro D u Ch chOf Tf B w z hz hint
  refine (Tf.valP.rat z).2 ⟨hz, fun c => ?_⟩
  have hB : IsUnit ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (B w c))
  obtain ⟨Q, hQ, hq⟩ := Formalism.L2.GlobalTheoryTheory.Br.eW_repS Tf _ hB z hz c
  have hco : Formalism.L2.GlobalTheoryTheory.Br.coPTS Tf (fun w c => ((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) :
      Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)) w z c = Q := by
    change fnInv (gramC (gramP D) (_root_.Formalism.L2.Forms.embT D)) (shiftOf (sgT u))
      (atInf (_root_.Formalism.L2.embT D) (↑(B w c))⁻¹) (Tf.valP.eW z c) = Q
    rw [hq]
    erw [fnInv_fnOf _ _ _ (atInf_inv_isUnit _ hB)]
  have hQr : Q ∈ Formalism.L2.Forms.RatSpan D (D.fm u).sg := intSpan_le_ratSpan D w _ (hco ▸ hint c)
  obtain ⟨Q', hQ', he⟩ := GlobalTheory.LevelHecke.exists_ratSpan_fnOf_atInf (D.fm u).sg _ (shiftOf (sgT u))
    (((B w c : GL (Fin (D.R.N D.R.m - 1)) D.host.E) : Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)⁻¹) hQr
  exact ⟨Q', hQ', hq.trans he⟩

end GlobalTheory.FormsRatOfInt
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

noncomputable section

namespace GlobalTheory

open Matrix MvPolynomial Formalism.L2.GlobalTheoryTheory.Br



theorem coMTS_of_gaInv : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf) (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E) (w : D.what₂.places.Pl) (c : (D.fm u).clsP) (B' : GL (Fin (D.R.N D.R.m)) D.host.E), IsUnit (B w c).det → (B' : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) = ((((Tf.til.ga c).1)⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) * bZg u Tf.til.z0 (B w c) → ∀ (f : (D.mem u).C.Y D.R.m → ℂ) (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ), (∀ z, f z = fnOf _ (shiftOf (lamT u D.R.m)) (atInf (_root_.Formalism.L2.Forms.embT D) ((B'⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E)) P ((Tf.val D.R.m le_rfl (Or.inr rfl)).eY z)) → Formalism.L2.GlobalTheoryTheory.Br.coMTS Tf B w c f = ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) • P := by
  intro D u Ch chOf Tf B w c B' hBdet hB' f P hf
  have hg : ∃ g : GL (Fin (D.R.N D.R.m)) D.host.E, g = (Tf.til.ga c).1 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ := hg
  rw [← hg] at hB'
  have hbZg := bZg_isUnitS Tf (B w c) hBdet
  have hU2 := atInf_inv_isUnit _ hbZg

  have hprod : ∀ τ, atInf (_root_.Formalism.L2.Forms.embT D) ((B'⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) τ *
      atInf (_root_.Formalism.L2.Forms.embT D) ((g⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) τ =
      atInf (_root_.Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹ τ := by
    intro τ
    simp only [atInf]
    rw [← Matrix.map_mul]
    congr 1
    have e1 : ((B'⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) *
        ((g⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) =
        (((g * B')⁻¹ : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) := by
      rw [_root_.mul_inv_rev, Units.val_mul]
    have e2 : ((g * B' : GL (Fin (D.R.N D.R.m)) D.host.E) : Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E) = bZg u Tf.til.z0 (B w c) := by
      rw [Units.val_mul, hB', ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [e1, Matrix.coe_units_inv, e2]
  subst hg
  have hemb : _root_.Formalism.L2.embT D = _root_.Formalism.L2.Forms.embT D := rfl
  have hT : trEvS Tf c f = ((((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi (Tf.tilAd.ka c))⁻¹ : ℂˣ) : ℂ) •
      fnOf (gramC (gramN D D.R.m le_rfl) (_root_.Formalism.L2.Forms.embT D)) (shiftOf (lamT u D.R.m))
        (atInf (_root_.Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹) P := by
    funext y
    simp only [trEvS, LinearMap.smul_apply, LinearMap.funLeft_apply, Pi.smul_apply, hf, Equiv.apply_symm_apply]
    congr 1
    simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Frames.tr, hemb, ← Matrix.mul_assoc, hprod]
  change fnInv (gramC (gramN D D.R.m le_rfl) (_root_.Formalism.L2.Forms.embT D))
    (shiftOf (lamT u D.R.m)) (atInf (_root_.Formalism.L2.Forms.embT D) (bZg u Tf.til.z0 (B w c))⁻¹)
    (trEvS Tf c f) = _
  rw [hT, map_smul, fnInv_fnOf _ _ _ hU2]

end GlobalTheory
end
end
