module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import GroundTheory.GlobalFields.Adele.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle162
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
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
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.GlobalFields.Adele.Bundle002
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (piInf)

namespace GlobalTheory.VacDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def IsGaussEq (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (Φ : (Fin n × Fin d → AF F) → ℂ) : Prop :=
  ∃ ε : InfinitePlace F → ℤˣ, ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
    (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
    ∀ x, deriv (fun t : ℝ => M.heisLine ψ u' t Φ x) 0 = Complex.I * deriv (fun t : ℝ => M.heisLine ψ u t Φ x) 0

end GlobalTheory.VacDatum

end
end

section

noncomputable section

namespace GlobalTheory.CoinvKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

def IsStabW (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  N ≤ A ∧ (∀ v : Pl F, ∀ h ∈ UAt σ W (evFin F v), ∀ Φ ∈ N, om (1, h) Φ ∈ N) ∧
    (∀ k ∈ KInf σ W emb, ∀ Φ ∈ N, om (1, k) Φ ∈ N) ∧
    ∀ γ ∈ Lines σ W, ∀ Φ ∈ N, ∀ Φ₁ ∈ A,
      (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

def HasRelY (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  (∀ v : Pl F, ∀ g ∈ UAt σ Y (evFin F v), ∀ Φ ∈ A, om (g, 1) Φ - Φ ∈ N) ∧
    (∀ k ∈ KInf σ Y emb, ∀ Φ ∈ A, om (k, 1) Φ - Φ ∈ N) ∧
    ∀ γ ∈ Lines σ Y, ∀ Φ ∈ A, ∀ Φ₁ ∈ A,
      (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → Φ₁ ∈ N

def IsThetaSub (om : Rep σ Y W) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (A N : Submodule ℂ ((Fin n × Fin d → AF F) → ℂ)) : Prop :=
  IsStabW om emb A N ∧ HasRelY om emb A N

end GlobalTheory.CoinvKer

end
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PolKerCpt

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem pure_sub {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : SInf F κ)
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, sub_mul]

end GlobalTheory.PolKerCpt
end
end

section

noncomputable section

namespace GlobalTheory.HoweGlobal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def opInf (Bs : Base F E) (G : Geo σ a a') (om : Rep σ G.V G.W) : Set (Module.End ℂ ↥(G.M.Pol Bs.ψ Bs.emb)) :=
  {g | (∃ k ∈ KInf σ G.W Bs.emb, ∀ f : ↥(G.M.Pol Bs.ψ Bs.emb),
      Acts (evI F) (om (1, k)) ⇑(f : SInf F (Fin a × Fin (a + a'))) ⇑((g f : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F _)) ∨
    ∃ γ ∈ Lines σ G.W, ∀ f : ↥(G.M.Pol Bs.ψ Bs.emb),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) ⇑(f : SInf F (Fin a × Fin (a + a')))
        ⇑((g f : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F _)}

def relInf (Bs : Base F E) (G : Geo σ a a') (om : Rep σ G.V G.W) : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb) :=
  Submodule.span ℂ {x | (∃ γ ∈ Lines σ G.V, ∃ f ∈ G.M.Pol Bs.ψ Bs.emb,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) ⇑f ⇑(x : SInf F (Fin a × Fin (a + a')))) ∨
    ∃ k ∈ KInf σ G.V Bs.emb, ∃ f f₁ : ↥(G.M.Pol Bs.ψ Bs.emb),
      Acts (evI F) (om (k, 1)) ⇑(f : SInf F (Fin a × Fin (a + a'))) ⇑(f₁ : SInf F (Fin a × Fin (a + a'))) ∧ x = f₁ - f}

def opFin (G : Geo σ a a') (om : Rep σ G.V G.W) (v : Pl F) :
    Set (Module.End ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v))) :=
  {g | ∃ h ∈ UAt σ G.W (evFin F v), ∀ φ : ↥(SB (Fin a × Fin (a + a') → Fv F v)),
    Acts (evFin F v) (om (1, h)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ)
      ((g φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) : (Fin a × Fin (a + a') → Fv F v) → ℂ)}

def relFin (G : Geo σ a a') (om : Rep σ G.V G.W) (v : Pl F) : Submodule ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)) :=
  (augAt om v).comap (SB (Fin a × Fin (a + a') → Fv F v)).subtype

end GlobalTheory.HoweGlobal

end
end

section

noncomputable section

namespace GlobalTheory.HoweGlobalPair

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def opInf (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W) :
    Set (Module.End ℂ ↥(M.Pol ψ emb)) :=
  {g | (∃ k ∈ KInf σ W emb, ∀ f : ↥(M.Pol ψ emb),
      Acts (evI F) (om (1, k)) ⇑(f : SInf F (Fin n × Fin d)) ⇑((g f : ↥(M.Pol ψ emb)) : SInf F _)) ∨
    ∃ γ ∈ Lines σ W, ∀ f : ↥(M.Pol ψ emb),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) ⇑(f : SInf F (Fin n × Fin d))
        ⇑((g f : ↥(M.Pol ψ emb)) : SInf F _)}

def relInf (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (om : Rep σ X W) :
    Submodule ℂ ↥(M.Pol ψ emb) :=
  Submodule.span ℂ {x | (∃ γ ∈ Lines σ X, ∃ f ∈ M.Pol ψ emb,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) ⇑f ⇑(x : SInf F (Fin n × Fin d))) ∨
    ∃ k ∈ KInf σ X emb, ∃ f f₁ : ↥(M.Pol ψ emb),
      Acts (evI F) (om (k, 1)) ⇑(f : SInf F (Fin n × Fin d)) ⇑(f₁ : SInf F (Fin n × Fin d)) ∧ x = f₁ - f}

def opFin (om : Rep σ X W) (v : Pl F) : Set (Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v))) :=
  {g | ∃ h ∈ UAt σ W (evFin F v), ∀ φ : ↥(SB (Fin n × Fin d → Fv F v)),
    Acts (evFin F v) (om (1, h)) (φ : (Fin n × Fin d → Fv F v) → ℂ)
      ((g φ : ↥(SB (Fin n × Fin d → Fv F v))) : (Fin n × Fin d → Fv F v) → ℂ)}

def relFin (om : Rep σ X W) (v : Pl F) : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
  (augAt om v).comap (SB (Fin n × Fin d → Fv F v)).subtype

end GlobalTheory.HoweGlobalPair

end
end

section

open Matrix

namespace GlobalTheory.ExpCartan

open scoped Matrix.Norms.L2Operator ComplexOrder


open scoped MatrixOrder in
theorem exists_posDef_mul_self {n : ℕ} {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosDef) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ, S.PosDef ∧ S * S = P := by
  refine ⟨CFC.sqrt P, ?_, CFC.sqrt_mul_sqrt_self _ hP.posSemidef.nonneg⟩
  have hP' := hP
  rw [← isStrictlyPositive_iff_posDef] at hP' ⊢
  exact IsStrictlyPositive.sqrt _ hP'

theorem im_star_dotProduct_mulVec {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M)
    (x : Fin n → ℂ) : (star x ⬝ᵥ M *ᵥ x).im = 0 := by
  have h : star (star x ⬝ᵥ M *ᵥ x) = star x ⬝ᵥ M *ᵥ x := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hM]
  exact Complex.conj_eq_iff_im.1 h

theorem exists_exp_eq_of_commute_cartan : ∀ {n : ℕ} {G C g : Matrix (Fin n) (Fin n) ℂ}, Gᴴ = G →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan Gᵀ C → gᴴ * G * g = G → Commute g C →
    ∃ Z : Matrix (Fin n) (Fin n) ℂ, Zᴴ * G + G * Z = 0 ∧ Commute Z C ∧ NormedSpace.exp Z = g := by
  intro n G C g hG hC hg hgC
  obtain ⟨hCC, hCG, hpos⟩ := hC
  have hCG' : Cᴴ * G * C = G := by
    have h := congrArg Matrix.transpose hCG
    simpa [Matrix.transpose_mul, Matrix.conjTranspose, Matrix.transpose_map, Matrix.mul_assoc] using h
  have hCG2 : Cᴴ * G = G * C := by
    calc Cᴴ * G = Cᴴ * G * (C * C) := by rw [hCC, Matrix.mul_one]
      _ = G * C := by rw [← Matrix.mul_assoc, hCG']
  set P := G * C with hPdef
  have hPh : Pᴴ = P := by rw [hPdef, Matrix.conjTranspose_mul, hG, hCG2]
  have hPpd : P.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hPh, fun x hx => ?_⟩
    have h1 := hpos x hx
    have he : (C *ᵥ x) ⬝ᵥ Gᵀ *ᵥ star x = star x ⬝ᵥ P *ᵥ x := by
      rw [dotProduct_comm, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
        hPdef, ← Matrix.mulVec_mulVec]
    rw [he] at h1
    exact Complex.lt_def.2 ⟨by simpa using h1, by simpa using (im_star_dotProduct_mulVec hPh x).symm⟩
  obtain ⟨S, hSpd, hSS⟩ := exists_posDef_mul_self hPpd
  have hSh : Sᴴ = S := hSpd.isHermitian
  have hSu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hSpd.isUnit
  set Si := S⁻¹ with hSidef
  have h1 : S * Si = 1 := Matrix.mul_nonsing_inv _ hSu
  have h2 : Si * S = 1 := Matrix.nonsing_inv_mul _ hSu
  have hSih : Siᴴ = Si := by rw [hSidef, Matrix.conjTranspose_nonsing_inv, hSh]
  have hgP : gᴴ * P * g = P := by
    calc gᴴ * P * g = gᴴ * G * (C * g) := by rw [hPdef]; simp only [Matrix.mul_assoc]
      _ = gᴴ * G * g * C := by rw [← hgC.eq]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hg]
  set u := S * g * Si with hudef
  have hsu : star u = Si * gᴴ * S := by
    rw [hudef, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hSih,
      Matrix.mul_assoc]
  have huu : star u * u = 1 := by
    rw [hsu, hudef]
    calc Si * gᴴ * S * (S * g * Si) = Si * (gᴴ * (S * S) * g) * Si := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSS, hgP, ← hSS, ← Matrix.mul_assoc, h2, Matrix.one_mul, h1]
  have hu : u ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := ⟨huu, mul_eq_one_comm.1 huu⟩
  set C' := S * C * Si with hC'def
  have hSC : S * C = C' * S := by rw [hC'def, Matrix.mul_assoc _ Si, h2, Matrix.mul_one]
  have hSiC' : Si * C' = C * Si := by
    rw [hC'def, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  have huC : Commute u C' := by
    show u * C' = C' * u
    rw [hudef, hC'def]
    calc S * g * Si * (S * C * Si) = S * g * (Si * S) * C * Si := by simp only [Matrix.mul_assoc]
      _ = S * (C * g) * Si := by rw [h2, Matrix.mul_one, Matrix.mul_assoc S g C, hgC.eq]
      _ = S * C * (Si * S) * g * Si := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = S * C * Si * (S * g * Si) := by simp only [Matrix.mul_assoc]
  have huC' : Commute (star u) C' := by
    have hus : u * star u = 1 := mul_eq_one_comm.1 huu
    show star u * C' = C' * star u
    calc star u * C' = star u * (C' * (u * star u)) := by rw [hus, Matrix.mul_one]
      _ = star u * (u * C' * star u) := by rw [huC.eq]; simp only [Matrix.mul_assoc]
      _ = (star u * u) * C' * star u := by simp only [Matrix.mul_assoc]
      _ = C' * star u := by rw [huu, Matrix.one_mul]
  have hN : IsStarNormal u := ⟨by
    show star u * u = u * star u
    rw [huu, mul_eq_one_comm.1 huu]⟩
  have hfin : (spectrum ℂ u).Finite := Matrix.finite_spectrum u
  have hsph : ∀ z ∈ spectrum ℂ u, ‖z‖ = 1 := fun z hz => by
    simpa using spectrum.subset_circle_of_unitary hu hz
  set Y := cfc Complex.log u with hYdef
  have hlog : ContinuousOn Complex.log (spectrum ℂ u) := hfin.continuousOn _
  have hexp : NormedSpace.exp Y = u := by
    rw [hYdef, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← Complex.exp_eq_exp_ℂ,
      ← cfc_comp Complex.exp Complex.log u (hf := hlog) (ha := hN)]
    conv_rhs => rw [← cfc_id' ℂ u hN]
    refine cfc_congr fun z hz => ?_
    have hz0 : z ≠ 0 := by intro h; have := hsph z hz; rw [h] at this; simp at this
    simp [Complex.exp_log hz0]
  have hstar : star Y = -Y := by
    rw [hYdef, ← cfc_star, ← cfc_neg]
    refine cfc_congr fun z hz => ?_
    apply Complex.ext
    · simp [Complex.log_re, hsph z hz]
    · simp
  have hYC : Commute Y C' := huC.cfc huC' Complex.log
  have hYh : Yᴴ = -Y := by rw [← Matrix.star_eq_conjTranspose, hstar]
  refine ⟨Si * Y * S, ?_, ?_, ?_⟩
  · have hGP : G = S * S * C := by
      rw [hSS, hPdef, Matrix.mul_assoc, hCC, Matrix.mul_one]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSh, hSih, hYh, hGP]
    calc S * (-Y * Si) * (S * S * C) + S * S * C * (Si * Y * S)
        = -(S * Y * (Si * S) * (S * C)) + S * ((S * C) * Si) * Y * S := by
          simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
      _ = -(S * (Y * C') * S) + S * (C' * Y) * S := by
          rw [h2, Matrix.mul_one, hSC, Matrix.mul_assoc C' S Si, h1, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hYC.eq, neg_add_cancel]
  · show Si * Y * S * C = C * (Si * Y * S)
    calc Si * Y * S * C = Si * (Y * C') * S := by rw [Matrix.mul_assoc _ S C, hSC]; simp only [Matrix.mul_assoc]
      _ = (Si * C') * Y * S := by rw [hYC.eq]; simp only [Matrix.mul_assoc]
      _ = C * (Si * Y * S) := by rw [hSiC']; simp only [Matrix.mul_assoc]
  · have hSun : IsUnit S := hSpd.isUnit
    rw [hSidef, Matrix.exp_conj' S Y hSun, hexp, hudef, ← hSidef]
    calc Si * (S * g * Si) * S = (Si * S) * g * (Si * S) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [h2, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.ExpCartan
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.VacTransfer

variable {D : D7} {S X : HSp D} {n d : ℕ}

def archLine (cS : Matrix (Fin n) (Fin d) (AE D) ≃+ WO S X) (u : Matrix (Fin n) (Fin d) (AE D)) : ℝ →+ WO S X where
  toFun t := cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)
  map_zero' := by
    have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 0 = 0 := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd
      simp only [map_zero]
    show cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F 0 • u) = 0
    rw [h, zero_smul]
    exact map_zero cS
  map_add' s t := by
    have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F (s + t) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd
      simp only [map_add (f := _)]
    show cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F (s + t) • u) =
      cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F s • u) + cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u)
    rw [h, add_smul]
    exact map_add cS _ _

theorem archLine_apply (cS : Matrix (Fin n) (Fin d) (AE D) ≃+ WO S X) (u : Matrix (Fin n) (Fin d) (AE D)) (t : ℝ) :
    archLine cS u t = cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • u) := rfl

end GlobalTheory.VacTransfer

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchRest

theorem exists_rest_arch : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ f : SInf F κ, Rest (evI F) (⇑f) R := by
  intro F _ _ κ _
  classical
  let I : Set (FiniteAdeleRing (𝓞 F) F) := (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set _)
  have hIo : IsOpen I := GroundTheory.Global.isOpen_integralFiniteAdeles
  have hIc : IsClosed I :=
    AddSubgroup.isClosed_of_isOpen (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).toAddSubgroup hIo
  have hIk : IsCompact I := GroundTheory.Global.isCompact_integralFiniteAdeles F
  let S : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => I
  have hSo : IsOpen S := isOpen_set_pi Set.finite_univ fun _ _ => hIo
  have hSc : IsClosed S := isClosed_set_pi fun _ _ => hIc
  have hSk : IsCompact S := isCompact_univ_pi fun _ => hIk
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := S.indicator 1
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨?_, HasCompactSupport.intro hSk fun x hx => Set.indicator_of_notMem hx _⟩
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    by_cases hx : x ∈ S
    · exact ⟨S, hSo, hx, fun y hy => by simp only [g, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]⟩
    · exact ⟨Sᶜ, hSc.isOpen_compl, hx, fun y hy => by simp only [g, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  refine ⟨fun x => g fun i => (x i).2, ?_, fun f => ⟨?_, ?_⟩⟩
  · have h0 : (fun i => ((0 : κ → AF F) i).2) ∈ S := fun i _ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F).zero_mem
    simp only [g, Set.indicator_of_mem h0, Pi.one_apply]
    exact one_ne_zero
  · intro x z hz
    have hz2 : ∀ i, (z i).2 = 0 := by
      let u : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))
      have e := hz u (by
        show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
        exact map_zero _)
      intro i
      have e' := congrFun e i
      have h1 : (u • z) i = u * z i := rfl
      rw [h1] at e'
      have h2 : (u * z i).2 = 1 * (z i).2 := rfl
      have := congrArg Prod.snd e'
      rw [h2, one_mul] at this
      exact this
    show g (fun i => ((x + z) i).2) = g (fun i => (x i).2)
    congr 1
    funext i
    show (x i).2 + (z i).2 = (x i).2
    rw [hz2 i, add_zero]
  · have e : tens (evI F) (⇑f) (fun x => g fun i => (x i).2) = pureA F (⇑f) g := rfl
    rw [e]
    exact Submodule.subset_span ⟨f, g, hg, rfl⟩

end GlobalTheory.ArchRest
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symplecticHalf_isotropicParts_add_self_eq_trace : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → ∀ u y : Mx D W.rank r, symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace) := by
  first | exact @GlobalTheory.IsoPartPairing.symplOH_isoPart_add_self | exact GlobalTheory.IsoPartPairing.symplOH_isoPart_add_self | (intros; apply GlobalTheory.IsoPartPairing.symplOH_isoPart_add_self <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weilAction_isotropicPartHom_of_frameMul : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (a : GL (Fin r) (AE D)) (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → ∀ (h : GA D W) (z : Mx D W.rank r), actO V W m h (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C z) = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt W h) z) (GlobalTheory.MixModel.adj a.val)) := by
  first | exact @GlobalTheory.IsoFrameAct.actO_isoPart_of_mul | exact GlobalTheory.IsoFrameAct.actO_isoPart_of_mul | (intros; apply GlobalTheory.IsoFrameAct.actO_isoPart_of_mul <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_parametric_unfold_rationalTranslates : ∀ (D : D7) (m n : ℕ) (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (ν : Measure X) [IsFiniteMeasure ν] (μ : Measure (Mx D m n)) (𝓨 : Set (Mx D m n)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D m n) μ 𝓨 → ∀ (h : X → Mx D m n → ℂ), Continuous (Function.uncurry h) → ∀ M : ℝ, (∀ x u, Summable (fun ξ : Matrix (Fin m) (Fin n) D.host.E => ‖h x (ξ.map (incA D) + u)‖) ∧ ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, ‖h x (ξ.map (incA D) + u)‖ ≤ M) → Integrable (fun u => ∫ x, h x u ∂ν) μ ∧ ∫ u, (∫ x, h x u ∂ν) ∂μ = ∫ t in 𝓨, (∫ x, ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, h x (ξ.map (incA D) + t) ∂ν) ∂μ := by
  first | exact @GlobalTheory.UnfoldRat.unfold | exact GlobalTheory.UnfoldRat.unfold | (intros; apply GlobalTheory.UnfoldRat.unfold <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_eq_setIntegral_tsum_rationalTranslates : ∀ (D : D7) (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratMx D m n) 𝓕 μ → ∀ c : Mx D m n → ℂ, Integrable c μ → (∀ᵐ y ∂(μ.restrict 𝓕), Summable fun a : Matrix (Fin m) (Fin n) D.host.E => ‖c (y + a.map (incA D))‖) ∧ ∫ y, c y ∂μ = ∫ y in 𝓕, ∑' a : Matrix (Fin m) (Fin n) D.host.E, c (y + a.map (incA D)) ∂μ := by
  first | exact @GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum | exact GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum | (intros; apply GlobalTheory.Twist.Periodize.integral_eq_setIntegral_tsum <;> assumption)
end
