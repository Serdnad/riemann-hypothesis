import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY

open WeierstrassCurve WeierstrassCurve.Projective

namespace GlobalTheory.AddLaw

variable {R : Type*} [CommRing R]

def originN (W : Projective R) (z₁ w₁ z₂ : R) : R :=
  z₁ ^ 2 + z₁ * z₂ + z₂ ^ 2 + W.a₁ * w₁ + W.a₂ * w₁ * (z₁ + z₂) + W.a₄ * w₁ ^ 2

def originD (W : Projective R) (w₁ z₂ w₂ : R) : R :=
  1 - W.a₁ * z₂ - W.a₂ * z₂ ^ 2 - W.a₃ * (w₁ + w₂) - W.a₄ * z₂ * (w₁ + w₂)
    - W.a₆ * (w₁ ^ 2 + w₁ * w₂ + w₂ ^ 2)

def lineCubicCoeff (W : Projective R) (n d : R) : R :=
  d ^ 3 + W.a₂ * n * d ^ 2 + W.a₄ * n ^ 2 * d + W.a₆ * n ^ 3

def lineQuadCoeff (W : Projective R) (n v d : R) : R :=
  W.a₁ * n * d ^ 2 + W.a₂ * v * d ^ 2 + W.a₃ * n ^ 2 * d + 2 * W.a₄ * n * v * d
    + 3 * W.a₆ * n ^ 2 * v

variable {W : Projective R}

lemma sub_mul_originD {z₁ w₁ z₂ w₂ : R} (h₁ : W.Equation ![z₁, -1, w₁])
    (h₂ : W.Equation ![z₂, -1, w₂]) :
    (w₂ - w₁) * originD W w₁ z₂ w₂ = (z₂ - z₁) * originN W z₁ w₁ z₂ := by
  have h := (equation_iff _).mp h₁
  have h' := (equation_iff _).mp h₂
  linear_combination (norm := (simp only [originN, originD, fin3_def_ext]; ring1)) h' - h

lemma addZ_line (z₁ w₁ z₂ l : R) :
    W.addZ ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] =
      l * W.addX ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      - (w₁ - l * z₁) * W.negAddY ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] := by
  simp only [addX, addZ, negAddY, fin3_def_ext]
  ring1

section
-- Substitution of the line equation produces deeply nested polynomials.
set_option maxRecDepth 8192

lemma negAddY_line {z₁ w₁ z₂ l : R} (h₁ : W.Equation ![z₁, -1, w₁])
    (hl : originN W z₁ w₁ z₂ = l * originD W w₁ z₂ (w₁ + l * (z₂ - z₁))) :
    (-lineQuadCoeff W l (w₁ - l * z₁) 1 - lineCubicCoeff W l 1 * (z₁ + z₂))
        * W.negAddY ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      + lineCubicCoeff W l 1 * W.addX ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] = 0 := by
  simp only [equation_iff, fin3_def_ext] at h₁
  simp only [originN, originD] at hl
  simp only [lineCubicCoeff, lineQuadCoeff, addX, negAddY, fin3_def_ext]
  grobner

lemma diagZ_line {z₁ w₁ z₂ l : R} (h₁ : W.Equation ![z₁, -1, w₁])
    (hl : originN W z₁ w₁ z₂ = l * originD W w₁ z₂ (w₁ + l * (z₂ - z₁))) :
    diagZ W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] =
      l * diagX W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      - (w₁ - l * z₁) * negDiagY W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] := by
  simp only [equation_iff, fin3_def_ext] at h₁
  simp only [originN, originD] at hl
  simp only [diagX, diagZ, negDiagY, fin3_def_ext]
  grobner

lemma negDiagY_line {z₁ w₁ z₂ l : R} (h₁ : W.Equation ![z₁, -1, w₁])
    (hl : originN W z₁ w₁ z₂ = l * originD W w₁ z₂ (w₁ + l * (z₂ - z₁))) :
    (-lineQuadCoeff W l (w₁ - l * z₁) 1 - lineCubicCoeff W l 1 * (z₁ + z₂))
        * negDiagY W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)]
      + lineCubicCoeff W l 1 * diagX W ![z₁, -1, w₁] ![z₂, -1, w₁ + l * (z₂ - z₁)] = 0 := by
  simp only [equation_iff, fin3_def_ext] at h₁
  simp only [originN, originD] at hl
  simp only [lineCubicCoeff, lineQuadCoeff, diagX, negDiagY, fin3_def_ext]
  grobner (ringSteps := 500000)

end

end GlobalTheory.AddLaw
