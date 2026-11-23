module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle007
public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfB
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

@[expose] public section

section

noncomputable section

open scoped Classical TensorProduct
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Matrix

namespace Formalism.L2.SG.Pf.NormSteps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LeviOntoSPf

variable {D : D7}

def fixV (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : Set (VA X.B.I) :=
  Set.range (fun a => incl X.B.I (X.eR a)) ∪ Set.range (fun a => incl X.B.I (X.fR a)) ∪
    {X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)}

variable {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) (u : D.what₂.Word)

def KappaOnto : Prop :=
  ∀ s : Iof TR, ∃ κ : X.B.I.Gf, κ ∈ X.B.I.Kset ∧ (∀ y ∈ fixV X u, X.B.I.fmat κ *ᵥ y = y) ∧ levi TR κ = s

variable (X)

def IsDualFrame (η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (b d : Fin D.R.k → VA X.B.I) : Prop :=
  η ∈ IntAf X.B.I.F X.B.I.E ∧ η * η = η ∧ η * X.ew = η ∧ ZMod' X.B.I X.B.g (X.ew - η) ∧
    (∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      η * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = η) ∧
    (∀ i, b i ∈ X.B.I.Lf ∧ d i ∈ X.B.I.Lf ∧ η • b i = b i ∧ sigA X.B.I η • d i = d i) ∧
    (∀ y ∈ fixV X u, ∀ i, hA X.B.I y (b i) = 0 ∧ hA X.B.I y (d i) = 0) ∧
    (∀ i j, hA X.B.I (d i) (b j) = if i = j then η else 0) ∧
    ∀ i j, ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) (b j) - if i = j then X.ew else 0) ∧
      ZMod' X.B.I X.B.g (hA X.B.I (d i) (X.bw j) - if i = j then X.ew else 0)

def DualFrame : Prop := ∃ η b d, IsDualFrame X u η b d

def SIdem : Prop :=
  ∃ ε ∈ IntAf X.B.I.F X.B.I.E, ε * ε = ε ∧ sigA X.B.I ε = ε ∧ ZMod' X.B.I X.B.g (1 - ε) ∧
    ∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      ε * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = ε

def FrameOfS : Prop := SIdem X → DualFrame X u

variable {X}

def LeviElt : Prop :=
  ∀ η b d, IsDualFrame X u η b d → ∀ C C' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
    (∀ i j, C i j ∈ IntAf X.B.I.F X.B.I.E ∧ C' i j ∈ IntAf X.B.I.F X.B.I.E) →
    η • (C * C') = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) →
    η • (C' * C) = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) →
    ∃ κ : X.B.I.Gf, κ ∈ X.B.I.Kset ∧ (∀ y ∈ fixV X u, X.B.I.fmat κ *ᵥ y = y) ∧
      ∀ v, leviM TR κ v = C.map (resT TR v)

def MatLift : Prop :=
  ∀ η : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, η ∈ IntAf X.B.I.F X.B.I.E → η * η = η → η * X.ew = η →
    ZMod' X.B.I X.B.g (X.ew - η) →
    (∀ s ∈ IntAf X.B.I.F X.B.I.E, ∃ s' ∈ IntAf X.B.I.F X.B.I.E,
      η * ((1 + (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s) * s') = η) →
    ∀ s : Iof TR, ∃ C C' : Matrix (Fin D.R.k) (Fin D.R.k) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F),
      (∀ i j, C i j ∈ IntAf X.B.I.F X.B.I.E ∧ C' i j ∈ IntAf X.B.I.F X.B.I.E) ∧
      η • (C * C') = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) ∧
      η • (C' * C) = η • (1 : Matrix (Fin D.R.k) (Fin D.R.k) _) ∧
      ∀ v, C.map (resT TR v) = ((s v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v))

theorem kappaOnto_of (hF : DualFrame X u) (hE : LeviElt TR u) (hL : MatLift TR) : KappaOnto TR u := by
  intro s
  obtain ⟨η, b, d, hfr⟩ := hF
  obtain ⟨C, C', hint, hCC, hC'C, hres⟩ :=
    hL η hfr.1 hfr.2.1 hfr.2.2.1 hfr.2.2.2.1 hfr.2.2.2.2.1 s
  obtain ⟨κ, hκK, hfix, hlev⟩ := hE η b d hfr C C' hint hCC hC'C
  refine ⟨κ, hκK, hfix, ?_⟩
  funext v
  have hM : leviM TR κ v = ((s v : GL (Fin D.R.k) (TR.Fq v)) : Matrix (Fin D.R.k) (Fin D.R.k) (TR.Fq v)) := by
    rw [hlev, hres]
  have hu : IsUnit (leviM TR κ v).det := by
    rw [hM]
    exact Matrix.isUnits_det_units (s v)
  simp only [levi, dif_pos hu]
  exact Units.ext hM

theorem LeviOntoS_xu_inv_fix (y : Fin X.B.I.n → X.B.I.E)
    (hy : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y = incl X.B.I y) :
    X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I y = incl X.B.I y := by
  have e : X.B.I.fmat (X.xu u)⁻¹ * X.B.I.fmat (X.xu u) = 1 := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  calc X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I y
      = X.B.I.fmat (X.xu u)⁻¹ *ᵥ (X.B.I.fmat (X.xu u) *ᵥ incl X.B.I y) := by rw [hy]
    _ = incl X.B.I y := by rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]

theorem LeviOntoS_conj_mem (κ : X.B.I.Gf) (hfix : ∀ y ∈ fixV X u, X.B.I.fmat κ *ᵥ y = y) :
    X.xu u * κ * (X.xu u)⁻¹ ∈ Hfin X u := by
  have hmul : ∀ a b : X.B.I.Gf, X.B.I.fmat (a * b) = X.B.I.fmat a * X.B.I.fmat b := by
    intro a b
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have hinv : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = 1 := by
    simp [Formalism.MainNotions.S.AutInst.fmat]
  have he : ∀ a, X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) :=
    fun a => (X.xu_fix u a).1
  have hf : ∀ a, X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) :=
    fun a => (X.xu_fix u a).2
  show ∀ y ∈ fixSet X u, X.B.I.fmat (X.xu u * κ * (X.xu u)⁻¹) *ᵥ incl X.B.I y = incl X.B.I y
  intro y hy
  rw [hmul, hmul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
  · rw [LeviOntoS_xu_inv_fix u _ (he a), hfix (incl X.B.I (X.eR a)) (Or.inl (Or.inl ⟨a, rfl⟩)), he a]
  · rw [LeviOntoS_xu_inv_fix u _ (hf a), hfix (incl X.B.I (X.fR a)) (Or.inl (Or.inr ⟨a, rfl⟩)), hf a]
  · rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [hfix (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) (Or.inr rfl), Matrix.mulVec_mulVec, hinv,
      Matrix.one_mulVec]

theorem LeviOntoS_K_inv {κ : X.B.I.Gf} (hκ : κ ∈ X.B.I.Kset) : κ⁻¹ ∈ X.B.I.Kset := by
  exact Subgroup.inv_mem (Formalism.UG.stabGL X.B.I.Lf) hκ

variable {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂)

theorem leviOntoS_of (hK : KappaOnto TR u) : LeviOntoS TR cs := by
  intro q s
  obtain ⟨κ, hκK, hfix, hlev⟩ := hK s
  have e1 : colDS (cs.h (cs.base q.1))
      (cs.h (cs.base q.1) * ⟨X.xu u * κ * (X.xu u)⁻¹, LeviOntoS_conj_mem u κ hfix⟩) = κ := by
    simp only [colDS, Subgroup.coe_mul, Subgroup.coe_mk]
    group
  have e2 : colDS (cs.h (cs.base q.1) * ⟨X.xu u * κ * (X.xu u)⁻¹, LeviOntoS_conj_mem u κ hfix⟩)
      (cs.h (cs.base q.1)) = κ⁻¹ := by
    simp only [colDS, Subgroup.coe_mul, Subgroup.coe_mk]
    group
  refine ⟨cs.h (cs.base q.1) * ⟨X.xu u * κ * (X.xu u)⁻¹, LeviOntoS_conj_mem u κ hfix⟩, ?_, ?_, ?_⟩
  · rw [e1]
    exact hκK
  · rw [e2]
    exact LeviOntoS_K_inv hκK
  · rw [e1]
    exact hlev

theorem leviOntoS_of_steps (hS : SIdem X) (hFS : FrameOfS X u) (hE : LeviElt TR u) (hL : MatLift TR) : LeviOntoS TR cs :=
  leviOntoS_of (TR := TR) (u := u) (cs := cs) (kappaOnto_of (TR := TR) (u := u) (hFS hS) hE hL)

end LeviOntoSPf

end Formalism.L2.SG.Pf.NormSteps
end
end

section

noncomputable section

open MeasureTheory Filter Topology Classical
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

def rhoS (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (x : Mt k r) : ℝ≥0∞ :=
  ⨅ (Y : Formalism.MainNotions.S.lieE S)
    (_ : (fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j : Mt k r) = x),
    (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)

def Qf (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : ℝ≥0∞ :=
  rhoS k r (Nset k r) n ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + rhoS k r (Formalism.FourierDecayAlt.B2.UWb k r) m ^ 2 +
    rhoS k r (Nset k r) n' ^ 2

def Psi (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : Mt k r :=
  fun i j => (w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹)) i j

def Sandwich : Prop :=
  ∀ (k r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
    ∀ (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r), Matrix.of n ∈ Nset k r → Matrix.of m ∈ Formalism.FourierDecayAlt.B2.UWb k r →
      Matrix.of n' ∈ Nset k r →
      (Psi k r n c m n' ∈ gBall k r ρ → Qf k r n c m n' < ENNReal.ofReal (((1 + ε) * ρ) ^ 2)) ∧
      (Qf k r n c m n' < ENNReal.ofReal (((1 - ε) * ρ) ^ 2) → Psi k r n c m n' ∈ gBall k r ρ)

def Vol (k r : ℕ) (μb : Measure (Mt k r)) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
    ∫⁻ n, ∫⁻ m, ∫⁻ n', (if Qf k r n c m n' < ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0)
      ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) ∂μb ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1)

def VolLim : Prop :=
  ∀ (k r : ℕ) (μb : Measure (Mt k r)), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    Tendsto (fun s : ℝ => (Vol k r μb s).toReal / gVol k r s) (𝓝[>] 0) (𝓝 ((2 : ℝ) ^ r)⁻¹)

end Formalism.L2.SG.Pf.BH
end
end

section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB

def RhsHaar : Prop :=
  ∀ (k r : ℕ) (μb : Measure (Mt k r)), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    ∃ ν : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) ν ∧
      ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂ν = rhs k r μb φ

def RhsWHaar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec →
    ∃ ν : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) ν ∧
      ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂ν = rhsW k r z z' μW μW' μsec φ

def WbDataEx : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), WbData k r z z' μW μW' a a' μsec

def ExistsGaugeMeasureForEachRank : Prop := ∀ r : ℕ, ∃ μ : Measure (Mt 0 r), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb 0 r) μ

end Formalism.L2.SG.Pf.GE
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.WB

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem wbConst_pos {k : ℕ} {T T' a a' : ℝ} (hT : 0 < T) (hT' : 0 < T') (ha : 0 < a) (ha' : 0 < a') :
    0 < wbConst k T T' a a' := by
  unfold wbConst
  have h1 : ∀ j, 0 < Formalism.MainNotions.S.UnitaryVolumeMass.volU j := fun j => by
    unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU
    exact Finset.prod_pos fun i _ => by positivity
  have := h1 k
  have := h1 (k - 1)
  positivity

theorem wbHaar_of (hI : RankGauge) (hS : GaugeShiftW) (hR : RhsWLim) : WbHaar := by
  intro k r z z' hk hz hz' hT hT' μb μW μW' hμb hW hW' a a' ha ha' hma hma' μsec hsec φ hφ
  have D : WbData k r z z' μW μW' a a' μsec := ⟨hk, hz, hz', hT, hT', hW, hW', ha, ha', hma, hma', hsec⟩
  obtain ⟨C, hC, hF⟩ := hI k r z z' μb μW μW' a a' μsec D hμb
  have hlim1 : Tendsto (fun ρ : ℝ => (μb (bBall k r ρ)).toReal / bVol k r ρ) (𝓝[>] 0) (𝓝 1) := hμb.2
  have hlim2 := (hR k r z z' μW μW' a a' μsec D).const_mul (C : ℝ)
  have heq : ∀ᶠ ρ in 𝓝[>] (0:ℝ), (μb (bBall k r ρ)).toReal / bVol k r ρ =
      (C : ℝ) * ((rhsW k r z z' μW μW' μsec ((mBall k r z z' μsec ρ).indicator 1)).toReal / bVol k r ρ) := by
    filter_upwards [self_mem_nhdsWithin] with ρ hρ
    obtain ⟨hm, he⟩ := hS k r z z' μb μW μW' a a' μsec D hμb.1 ρ hρ
    have h1 : ∫⁻ x, (mBall k r z z' μsec ρ).indicator 1 x ∂μb = μb (mBall k r z z' μsec ρ) :=
      lintegral_indicator_one hm
    have h2 := hF _ (measurable_one.indicator hm)
    rw [h1, he] at h2
    rw [h2, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_div_assoc]
  have hu := tendsto_nhds_unique (hlim1.congr' heq) hlim2
  have hw := wbConst_pos (k := k) hT hT' ha ha'
  have hCr : (C : ℝ) = wbConst k (Tz k r z) (Tz k r z') a a' := by
    field_simp at hu
    linarith
  have hCe : (C : ℝ≥0∞) = ENNReal.ofReal (wbConst k (Tz k r z) (Tz k r z') a a') := by
    rw [← hCr, ENNReal.ofReal_coe_nnreal]
  rw [hF φ hφ, hCe]
  rfl

end Formalism.L2.SG.Pf.WB
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Concrete

variable {D : D7} (Z : LocDat D) (p : PlF D)

def IotaEl (Λ : Submodule (𝓞 D.host.E) (VS D).V) (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V)
    (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ g : Loc.SplitG (Z.M p).L, (Z.M p).split = some g →
    IotaG (locH Z p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp)) (lattice₂ D Z.M p Λ)
      (fun a => sF Z p a • baseChange₂ D p (f a)) (fun b => sF' Z p b • baseChange₂ D p (g1 b))
      (fun b => sF' Z p b • baseChange₂ D p (g2 b)) (betaP p β)

theorem omp_combine (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (P K : (D.s.atP p).Ep) :
    (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g1)) -
      (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g2)) =
    (P * K) • baseChange₂ D p (GDl f g2 (D.R.rS + 1) • Gom' f g1 - GDl f g1 (D.R.rS + 1) • Gom' f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2 <;> ring

theorem om_combine (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (P K : (D.s.atP p).Ep) :
    (Z.M p).L.cj (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (β (Gom f g1))) -
      (Z.M p).L.cj (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom f g2)) =
    ((Z.M p).L.cj P * K) • baseChange₂ D p (star (GDl f g2 (D.R.rS + 1)) • β (Gom f g1) -
      star (GDl f g1 (D.R.rS + 1)) • Gom f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, map_mul, map_mul,
    cj_iota (Z.hcj p), cj_iota (Z.hcj p)]
  congr 2 <;> ring

end Concrete

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

section Quot

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem perp_map (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h21 : ∀ y ∈ X2, e.symm y ∈ X1) {x : V} (hx : x ∈ H.perp X1) : e x ∈ H.perp X2 := by
  intro y hy
  rw [show y = e (e.symm y) from (e.apply_symm_apply y).symm, hiso]
  exact hx _ (h21 y hy)

theorem perp_map_symm (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) {y : V} (hy : y ∈ H.perp X2) : e.symm y ∈ H.perp X1 := by
  intro x hx
  rw [← hiso, e.apply_symm_apply]
  exact hy _ (h12 x hx)

def perpEquiv (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) : ↥(H.perp X1) ≃ₗ[E] ↥(H.perp X2) :=
  e.ofSubmodules (H.perp X1) (H.perp X2) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact perp_map H e hiso X1 X2 h21 hx
    · intro hy
      exact ⟨e.symm y, perp_map_symm H e hiso X1 X2 h12 hy, e.apply_symm_apply y⟩)

def qEquiv (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) :
    (↥(H.perp X1) ⧸ X1.comap (H.perp X1).subtype) ≃ₗ[E] (↥(H.perp X2) ⧸ X2.comap (H.perp X2).subtype) :=
  Submodule.Quotient.equiv _ _ (perpEquiv H e hiso X1 X2 h12 h21) (by
    ext ⟨y, hy⟩
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨⟨x, hx⟩, hx1, hxy⟩
      have h' : e x = y := congrArg Subtype.val hxy
      rw [← h']
      exact h12 x hx1
    · intro hy2
      refine ⟨⟨e.symm y, perp_map_symm H e hiso X1 X2 h12 hy⟩, h21 y hy2, ?_⟩
      apply Subtype.ext
      show e (e.symm y) = y
      exact e.apply_symm_apply y)

theorem qEquiv_mk (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w) (X1 X2 : Submodule E V)
    (h12 : ∀ x ∈ X1, e x ∈ X2) (h21 : ∀ y ∈ X2, e.symm y ∈ X1) (x : ↥(H.perp X1)) :
    qEquiv H e hiso X1 X2 h12 h21 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (perpEquiv H e hiso X1 X2 h12 h21 x) := rfl

theorem mk_eq_iff (X : Submodule E V) (x y : ↥(H.perp X)) :
    (Submodule.Quotient.mk x : ↥(H.perp X) ⧸ X.comap (H.perp X).subtype) = Submodule.Quotient.mk y ↔
      (x : V) - y ∈ X := by
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub]

theorem smul_mk_eq (X : Submodule E V) (c₁ c₂ : E) (x y : ↥(H.perp X)) (h : c₁ • (x : V) - c₂ • (y : V) ∈ X) :
    c₁ • (Submodule.Quotient.mk x : ↥(H.perp X) ⧸ X.comap (H.perp X).subtype) = c₂ • Submodule.Quotient.mk y := by
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, mk_eq_iff]
  simpa using h

theorem iso_span {ι : Type} (w : ι → V) (hw : ∀ i j, H.h (w i) (w j) = 0) :
    ∀ a ∈ Submodule.span E (Set.range w), ∀ b ∈ Submodule.span E (Set.range w), H.h a b = 0 := by
  have hle : Submodule.span E (Set.range w) ≤ H.perp (Submodule.span E (Set.range w)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_perp_span]
    rintro _ ⟨j, rfl⟩
    exact hw i j
  intro a ha b hb
  exact hle ha b hb

end Quot

end Formalism.L2.SG.Pf.ScalarFramePf
end
end
