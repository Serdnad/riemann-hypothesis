module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

def MemIsomOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (g : GL (Fin X.B.I.n) X.B.I.E), g ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J →
    ∃ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
      ∀ y, X.crd (n y) = (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y

def MemFlagOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (Z : Matrix (Kap X) (Kap X) X.B.I.E)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), InPat (lvk X) 1 Z → (∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y) →
    (∀ j, ∀ x ∈ Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Xflag (lf D (X.Fu u)) j) ∧
      ∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u))), n x - x ∈ Xsp (lf D (X.Fu u))

def MemLatOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsFullLattice D.host.E Λ →
    ∃ d : ℕ, 1 ≤ d ∧ ∀ (Z : Matrix (Kap X) (Kap X) X.B.I.E) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
      InPat (lvk X) 1 Z → (∃ A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), Z = (d : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) →
      (∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y) → Formalism.HermitianLatticesTheory.gmap n Λ = Λ

def MemConjOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (M : GL (Fin X.B.I.n) X.B.I.E), M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J →
    (∀ Z : Matrix (Kap X) (Kap X) X.B.I.E, (↑M⁻¹ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * gE X Z *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) =
        gE X (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _))) ∧
    (∀ Z : Matrix (Kap X) (Kap X) X.B.I.E, Zᴴ * JB X = -(JB X * Z) →
      (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _))ᴴ * JB X =
        -(JB X * (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _)))) ∧
    ∃ c : ℕ, 1 ≤ c ∧ ∀ (d : ℕ) (A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E)),
      ∃ A' : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E),
        Gr X (↑M⁻¹ : Matrix _ _ _) * (((c * d : ℕ) : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) *
          Gr X (M : Matrix _ _ _) = (d : X.B.I.E) • A'.map (fun a => (a : X.B.I.E))

def MemPtOf : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Z : Matrix (Kap X) (Kap X) X.B.I.E) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y) →
    ∃ x : X.B.I.GA, RatLink X x n ∧ ∀ v, Mv X v x.1 = (cay (2 * D.R.rS + 2) Z).map (X.B.I.φ v)

theorem ratMem_of (h1 : MemIsomOf) (h2 : MemFlagOf) (h3 : MemLatOf) (h4 : MemConjOf) (h5 : MemPtOf) : RatMem := by
  intro D X Y u u' t M hM hlin
  obtain ⟨d1, hd1, H1⟩ := h3 D X t.lam ((Y.rowsOK u).1 t.lam t.mem).1.1
  obtain ⟨d2, hd2, H2⟩ := h3 D X t.lam' ((Y.rowsOK u').1 t.lam' t.mem').1.1
  obtain ⟨hc1, hsk, c, hc, hdiv⟩ := h4 D X M hM
  have crd_inj : ∀ a b : (VS D).V, X.crd a = X.crd b → a = b := fun a b h => by
    rw [← Formalism.L2.SG.Pf.Level.toV_crd X a, h, Formalism.L2.SG.Pf.Level.toV_crd]
  refine ⟨c * d2 * d1, Nat.one_le_iff_ne_zero.2 (by positivity), fun Z hZ hZ' hZs hA => ?_⟩
  obtain ⟨A, hA⟩ := hA
  obtain ⟨n, hni, hn⟩ := h1 D X (gGL X le_rfl hZ) (gGL_mem X le_rfl hZ hZs)
  have hn' : ∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y := hn
  have hZs' := hsk Z hZs
  obtain ⟨m, hmi, hm⟩ := h1 D X (gGL X le_rfl hZ') (gGL_mem X le_rfl hZ' hZs')
  have hm' : ∀ y, X.crd (m y) =
      gE X (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _)) *ᵥ X.crd y := hm
  have hinv : ∀ y, X.crd (t.lin⁻¹ y) = (↑M⁻¹ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := by
    intro y
    have e := hlin (t.lin⁻¹ y)
    have : t.lin (t.lin⁻¹ y) = y := by
      show (t.lin * t.lin⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    rw [this] at e
    rw [e, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hconj : t.lin⁻¹ * n * t.lin = m := by
    apply LinearEquiv.ext
    intro y
    apply crd_inj
    show X.crd (t.lin⁻¹ (n (t.lin y))) = _
    rw [hinv, hn', hlin, hm', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc1]
  have e1 : Z = (d1 : X.B.I.E) • ((((c * d2 : ℕ) : 𝓞 X.B.I.E)) • A).map (fun a => (a : X.B.I.E)) := by
    rw [hA]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    push_cast
    ring
  have e2 : Z = ((c * d2 : ℕ) : X.B.I.E) • ((((d1 : ℕ) : 𝓞 X.B.I.E)) • A).map (fun a => (a : X.B.I.E)) := by
    rw [hA]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    push_cast
    ring
  obtain ⟨A', hA'⟩ := hdiv d2 ((((d1 : ℕ) : 𝓞 X.B.I.E)) • A)
  have hnN : n ∈ NLam t.lam (lf D (X.Fu u)) :=
    ⟨⟨hni, H1 Z n hZ ⟨_, e1⟩ hn'⟩, h2 D X u Z n hZ hn'⟩
  have hmN : t.lin⁻¹ * n * t.lin ∈ NLam t.lam' (lf D (X.Fu u')) := by
    rw [hconj]
    refine ⟨⟨hmi, H2 _ m hZ' ⟨A', ?_⟩ hm'⟩, h2 D X u' _ m hZ' hm'⟩
    rw [← hA', ← e2]
  obtain ⟨x, hx, hMv⟩ := h5 D X Z n hni hn'
  exact ⟨x.1, ⟨x, n, hx, rfl, hnN, hmN⟩, hMv⟩

end Formalism.L2.SG.TermOp.Vanish
end
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def JacEx : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → 0 < sc →
    ∃ h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε, IsSecLoc ε sc e z z' T T' h ∧
      ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
        ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

def GoodPos {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) : Prop :=
  ∃ f : Fin r → Fin n → ℂ, (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, hJ ε (f a) (f b) = 0) ∧
    ∀ a, hJ ε (f a) z = 0 ∧ hJ ε (f a) z' = 0

def JacExGood : Prop :=
  ∀ (n r k : ℕ) (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (T T' sc : ℝ),
    FrameLoc ε k e z z' T T' → GoodPos ε e z z' → 0 < sc →
    ∃ h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε, IsSecLoc ε sc e z z' T T' h ∧
      ∀ μS μS' : Measure (Formalism.REAL.UJ ε), IsHaarS (SLoc ε e z) μS → IsHaarS (SLoc ε e z') μS' →
        ∃ C, 0 < C ∧ DisintLoc ε k T T' μS μS' h C

def HpkEx : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → Formalism.QuantumDeterminants.inWb k r z → Formalism.QuantumDeterminants.inWb k r z' →
    0 < Formalism.QuantumDeterminants.Tz k r z → 0 < Formalism.QuantumDeterminants.Tz k r z' →
    ∀ μ μW μW' μN : Measure (Formalism.QuantumDeterminants.Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μ →
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z') μW' →
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    ∀ μsec, Formalism.QuantumDeterminants.IsSection k r z z' μsec →
    ∃ K : ℝ, 0 < K ∧ ∀ φ : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Measurable φ →
      ∫⁻ x, φ x ∂μ = ENNReal.ofReal K * ∫⁻ q : (Fin r → ℂ) × ℂ,
        ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r (Formalism.QuantumDeterminants.Tz k r z) (Formalism.QuantumDeterminants.Tz k r z') q) *
          ∫⁻ s, ∫⁻ s', φ (fun i j => (Matrix.of s * Formalism.QuantumDeterminants.bigCell k r q.1 (μsec q.2) * (Matrix.of s')⁻¹) i j)
            ∂(Formalism.MainNotions.S.muS μW' μN) ∂(Formalism.MainNotions.S.muS μW μN)

def TransEx : Prop := HpkEx → RightInvS → JacExGood

def DegRed : Prop := RightInvS → JacExGood → JacEx

theorem jacLoc_of_ex (h1 : DiagDCLoc) (hR : RightInvS) (hE : JacEx) : JacLoc := by
  intro n r k ε e z z' T T' sc hF hsc μS μS' hμ hμ' h hh
  obtain ⟨h0, hh0, hD⟩ := hE n r k ε e z z' T T' sc hF hsc
  obtain ⟨C, hC, hDC⟩ := hD μS μS' hμ hμ'
  have hF' : FrameLoc ε k e z' z T' T :=
    ⟨hF.dim, hF.k_pos, hF.sig, hF.e_li, hF.ee, hF.ez', hF.ez, hF.zz', hF.zz, hF.T'_pos, hF.T_pos⟩
  refine ⟨C, hC, fun φ hφ => ?_⟩
  rw [hDC φ hφ]
  refine setLIntegral_congr_fun (measurableSet_goodLoc r T T') ?_
  intro c hc
  obtain ⟨s₁, hs₁, s₁', hs₁', hcs⟩ :=
    h1 n r k ε e z z' T T' sc hF c hc (h0 c) (h c) (hh0 c hc) (hh c hc)
  beta_reduce
  congr 1
  rw [hcs]
  symm
  have eS := hR n r k ε e z z' T T' hF μS hμ s₁ hs₁
  have eS' := hR n r k ε e z' z T' T hF' μS' hμ' s₁' hs₁'
  have hmap : ∀ (a : Formalism.REAL.UJ ε) (ν : Measure (Formalism.REAL.UJ ε)),
      ν.map (fun x => x * a) = ν → ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, ∫⁻ x, F (x * a) ∂ν = ∫⁻ x, F x ∂ν := by
    intro a ν hν F
    have := lintegral_map_equiv F (MeasurableEquiv.mulRight a) (μ := ν)
    rw [show ⇑(MeasurableEquiv.mulRight a) = (fun x => x * a) from rfl, hν] at this
    exact this.symm
  calc ∫⁻ s, ∫⁻ s', φ (s * (s₁ * h0 c * s₁'⁻¹) * s'⁻¹) ∂μS' ∂μS
      = ∫⁻ s, ∫⁻ s', φ ((s * s₁) * h0 c * (s' * s₁')⁻¹) ∂μS' ∂μS := by
        simp only [_root_.mul_inv_rev, mul_assoc]
    _ = ∫⁻ s, ∫⁻ s', φ (s * h0 c * (s' * s₁')⁻¹) ∂μS' ∂μS :=
        hmap s₁ μS eS (fun s => ∫⁻ s', φ (s * h0 c * (s' * s₁')⁻¹) ∂μS')
    _ = ∫⁻ s, ∫⁻ s', φ (s * h0 c * s'⁻¹) ∂μS' ∂μS := by
        congr 1
        funext s
        exact hmap s₁' μS' eS' (fun s' => φ (s * h0 c * s'⁻¹))

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

section

namespace Formalism.L2.SG.Pf.SlabCount

theorem countC_holds : Formalism.L2.SG.Pf.Slab.CountC := countC_of_leviFin levi_finite_index

end Formalism.L2.SG.Pf.SlabCount
end

section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.EnergyInt

def LocOrbG : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ → ∀ v : InfinitePlace X.B.I.F,
      ∫⁻ x, ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v ((γ v)⁻¹ * x)‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) < ⊤

def StepIntG : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (X : HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ c ∈ Good X u u', ∀ γ, HasDiag X u u' sc c γ →
      TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

theorem lint_prod {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) :
    ∫⁻ x, ‖X.Wu u x‖ₑ * ‖X.Wu u' (γ⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∏ v, ∫⁻ x, ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v ((γ v)⁻¹ * x)‖ₑ ∂(Formalism.REAL.muG (X.B.I.ε v)) := by
  have hm : ∀ v, Measurable (fun x : Formalism.REAL.UJ (X.B.I.ε v) =>
      ‖X.Wloc u v x‖ₑ * ‖X.Wloc u' v ((γ v)⁻¹ * x)‖ₑ) := by
    intro v
    exact ((X.Wloc_cont u v).enorm.measurable).mul
      (((X.Wloc_cont u' v).comp (continuous_const.mul continuous_id)).enorm.measurable)
  rw [← Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.lintegral_pi_prod (fun v => Formalism.REAL.muG (X.B.I.ε v)) _ hm]
  simp_rw [Formalism.L2.SG.Pf.WuDec.enorm_Wu, ← Finset.prod_mul_distrib]
  rfl

theorem stepIntG_of_loc (h : LocOrbG) : StepIntG := by
  intro D hG X u u' sc hsc c hc γ hγ
  apply Formalism.L2.SG.RealObj.StepIntOf.Steps.stIntOfLint D X u u' γ
  rw [lint_prod]
  exact ENNReal.prod_lt_top fun v _ => h D hG X u u' sc hsc c hc γ hγ v

end Formalism.L2.SG.RealObj.EnergyInt
end
end

section

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped Classical

namespace Formalism.L2.SG.Pf.RCoc

open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

variable {D : D7} (X : HidaSetting D)

theorem isInt_symm {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (X.ιE.symm x) :=
  hx.map (RingHom.toIntAlgHom (X.ιE.symm : D.host.E →+* X.B.I.E))

theorem isInt_fwd {x : X.B.I.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (X.ιE x) :=
  hx.map (RingHom.toIntAlgHom (X.ιE : X.B.I.E →+* D.host.E))

theorem natAbs_sq_cast {K : Type*} [Ring K] (z : ℤ) : (((z.natAbs ^ 2 : ℕ)) : K) = (z : K) * (z : K) := by
  rw [← Int.cast_natCast, Nat.cast_pow, Int.natCast_natAbs, sq_abs, sq, Int.cast_mul]

theorem crd_sub_lat (a b : (VS D).V) : X.crd (a - b) = X.crd a - X.crd b := by
  first
    | exact Formalism.L2.SG.Pf.Vanish2.crd_sub' (X := X) a b
    | exact map_sub _ a b
    | (funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf])

theorem repr_crd (a : (VS D).V) (i : Fin X.B.I.n) : X.bas.repr a i = X.ιE (X.crd a i) := by
  simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf]

theorem lat_pres (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Submodule.IsFullLattice D.host.E Λ) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ G : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E, IntDiv c (G - 1) →
      ∀ g : (VS D).V →ₗ[D.host.E] (VS D).V, (∀ y, X.crd (g y) = G *ᵥ X.crd y) → ∀ y ∈ Λ, g y ∈ Λ := by
  obtain ⟨d, hd0, hd⟩ := Formalism.HermitianLatticesTheory.majLattice_exists_d X.bas Λ hΛ.fg
  have hc : ∀ i, ∃ c : ℤ, c ≠ 0 ∧ c • X.bas i ∈ Λ := fun i =>
    Formalism.HermitianLatticesTheory.majLattice_exists_c Λ hΛ.span_eq_top (X.bas i)
  choose c hc0 hcm using hc
  set C : ℤ := ∏ i, c i with hC
  have hCm : ∀ i, (C * C) • X.bas i ∈ Λ := by
    intro i
    have e : C = (∏ j ∈ Finset.univ.erase i, c j) * c i := by
      rw [hC, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    have h1 : C • X.bas i ∈ Λ := by
      rw [e, mul_smul]
      exact zsmul_mem (hcm i) _
    rw [mul_smul]
    exact zsmul_mem h1 _
  have hC0 : C ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hc0 i
  refine ⟨d.natAbs ^ 2 * C.natAbs ^ 2, ?_, ?_⟩
  · have h1 : 0 < d.natAbs := Int.natAbs_pos.2 hd0
    have h2 : 0 < C.natAbs := Int.natAbs_pos.2 hC0
    have := Nat.mul_pos (pow_pos h1 2) (pow_pos h2 2)
    omega
  rintro G ⟨A, hA, hGA⟩ g hg y hy
  set v := A *ᵥ X.crd y with hv
  have hw : X.crd (g y - y) = ((d.natAbs ^ 2 * C.natAbs ^ 2 : ℕ) : X.B.I.E) • v := by
    rw [crd_sub_lat, hg, ← Matrix.one_mulVec (X.crd y), Matrix.mulVec_mulVec, Matrix.mul_one,
      ← Matrix.sub_mulVec, hGA, Matrix.smul_mulVec]
  have hvi : ∀ i, IsIntegral ℤ (((d.natAbs ^ 2 : ℕ) : X.B.I.E) * v i) := by
    intro i
    rw [hv, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine IsIntegral.sum _ fun j _ => ?_
    have e : ((d.natAbs ^ 2 : ℕ) : X.B.I.E) * (A i j * X.crd y j) =
        A i j * X.ιE.symm ((d : D.host.E) * ((d : D.host.E) * X.bas.repr y j)) := by
      rw [natAbs_sq_cast]
      simp only [HidaSetting.crd, crdOf, map_mul, map_intCast]
      ring
    rw [e]
    exact (hA i j).mul (isInt_symm X ((isInt_intCast d).mul (hd y hy j)))
  choose r hr using fun i => (⟨⟨X.ιE (((d.natAbs ^ 2 : ℕ) : X.B.I.E) * v i), isInt_fwd X (hvi i)⟩, rfl⟩ :
    ∃ r : 𝓞 D.host.E, (r : D.host.E) = X.ιE (((d.natAbs ^ 2 : ℕ) : X.B.I.E) * v i))
  have hsum : g y - y = ∑ i, r i • ((C * C) • X.bas i) := by
    conv_lhs => rw [← X.bas.sum_repr (g y - y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [repr_crd, hw, Pi.smul_apply, smul_eq_mul, ← algebraMap_smul D.host.E (r i), ← Int.cast_smul_eq_zsmul D.host.E,
      smul_smul]
    congr 1
    show _ = (r i : D.host.E) * _
    rw [hr, Nat.cast_mul, mul_assoc, mul_comm, map_mul, map_mul, map_natCast, natAbs_sq_cast]
    simp only [map_mul, map_natCast]
    push_cast
    ring
  have hmem : g y - y ∈ Λ := by
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hCm i)
  have e : g y = y + (g y - y) := by abel
  rw [e]
  exact Λ.add_mem hy hmem

theorem lat_den_two {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (P : Matrix α β X.B.I.E) (Q : Matrix γ δ X.B.I.E) :
    ∃ m : ℕ, 0 < m ∧ IntDiv 1 ((m : X.B.I.E) • P) ∧ IntDiv 1 ((m : X.B.I.E) • Q) := by
  have hint : ∀ k : ℕ, IsIntegral ℤ ((k : X.B.I.E)) := fun k => by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ X.B.I.E (k : ℤ)))
  obtain ⟨d1, hd1, A, hA, hAe⟩ := exists_den (fun x => Formalism.L2.SG.Pf.nt_int_mul_of X.B.I x) P
  obtain ⟨d2, hd2, B, hB, hBe⟩ := exists_den (fun x => Formalism.L2.SG.Pf.nt_int_mul_of X.B.I x) Q
  refine ⟨d1 * d2, Nat.mul_pos hd1 hd2, ⟨(d2 : X.B.I.E) • A, fun i j => ?_, ?_⟩,
    ⟨(d1 : X.B.I.E) • B, fun i j => ?_, ?_⟩⟩
  · simpa [Matrix.smul_apply, smul_eq_mul] using (hint d2).mul (hA i j)
  · rw [Nat.cast_mul, mul_comm, mul_smul, hAe]
    simp
  · simpa [Matrix.smul_apply, smul_eq_mul] using (hint d1).mul (hB i j)
  · rw [Nat.cast_mul, mul_smul, hBe]
    simp

theorem lat_gE_sub_one (Z : Matrix (Kap X) (Kap X) X.B.I.E) :
    Formalism.L2.SG.Pf.UnipB.gE X Z - 1 = Bm X * (cay (N0 D) Z - 1) * Bm' X := by
  show Bm X * cay (N0 D) Z * Bm' X - 1 = Bm X * (cay (N0 D) Z - 1) * Bm' X
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Bm_mul_Bm']

theorem lat_gE_intDiv (mB : ℕ) (hB : IntDiv 1 ((mB : X.B.I.E) • Bm X)) (hB' : IntDiv 1 ((mB : X.B.I.E) • Bm' X))
    (c : ℕ) (A : Matrix (Kap X) (Kap X) X.B.I.E) (hA : ∀ i j, IsIntegral ℤ (A i j))
    (Z : Matrix (Kap X) (Kap X) X.B.I.E) (hZ : Z = ((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A) :
    IntDiv (2 * c) (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) := by
  subst hZ
  have hh : (⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A) = ((c * mB ^ 2 : ℕ) : X.B.I.E) • A := by
    rw [smul_smul]
    congr 1
    rw [show ((2 * c * mB ^ 2 : ℕ) : X.B.I.E) = 2 * ((c * mB ^ 2 : ℕ) : X.B.I.E) by push_cast; ring,
      ← mul_assoc, invOf_mul_self, one_mul]
  have hAi : IntDiv 1 A := ⟨A, hA, by simp⟩
  have hhalf : IntDiv 1 ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A)) := by
    rw [hh]
    refine ⟨((c * mB ^ 2 : ℕ) : X.B.I.E) • A, fun i j => ?_, by simp⟩
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (isInt_natCast _).mul (hA i j)
  have hgeo : IntDiv 1 (geo (N0 D) ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A))) := by
    unfold geo
    refine intDiv_sum fun j _ => ?_
    have := intDiv_pow hhalf j
    rwa [one_pow] at this
  have hP := intDiv_mul (intDiv_mul hB (intDiv_mul hAi hgeo)) hB'
  rw [show (1 * (1 * 1) * 1 : ℕ) = 1 by norm_num] at hP
  obtain ⟨W, hW, hWe⟩ := hP
  refine ⟨W, hW, ?_⟩
  rw [lat_gE_sub_one]
  unfold cay
  rw [add_sub_cancel_left]
  have e : Bm X * ((((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A) *
      geo (N0 D) ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A))) * Bm' X =
      ((2 * c : ℕ) : X.B.I.E) • (((mB : X.B.I.E) • Bm X) *
        (A * geo (N0 D) ((⅟2 : X.B.I.E) • (((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • A))) * ((mB : X.B.I.E) • Bm' X)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [e, hWe, Nat.cast_one, one_smul]

end Formalism.L2.SG.Pf.RCoc

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Pf.RCoc Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

theorem memLatOf_holds (D : D7) (X : HidaSetting D) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hΛ : Submodule.IsFullLattice D.host.E Λ) :
    ∃ d : ℕ, 1 ≤ d ∧ ∀ (Z : Matrix (Kap X) (Kap X) X.B.I.E) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V),
      InPat (lvk X) 1 Z → (∃ A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), Z = (d : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) →
      (∀ y, X.crd (n y) = gE X Z *ᵥ X.crd y) → Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
  obtain ⟨c, hc, H⟩ := lat_pres X Λ hΛ
  obtain ⟨mB, hmB, hB, hB'⟩ := lat_den_two X (Bm X) (Bm' X)
  refine ⟨2 * c * mB ^ 2, Nat.mul_pos (Nat.mul_pos two_pos hc) (pow_pos hmB 2), fun Z n hZ hA hn => ?_⟩
  obtain ⟨A, hA⟩ := hA
  have hAi : ∀ i j, IsIntegral ℤ ((A.map (fun a => (a : X.B.I.E))) i j) := fun i j => (A i j).isIntegral_coe
  have h1 : IntDiv c (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) := by
    have := lat_gE_intDiv X mB hB hB' c _ hAi Z hA
    exact intDiv_dvd (d := 2) (by rwa [mul_comm c 2])
  have h2 : IntDiv c (Formalism.L2.SG.Pf.UnipB.gE X (-Z) - 1) := by
    have hneg : -Z = ((2 * c * mB ^ 2 : ℕ) : X.B.I.E) • (-(A.map (fun a => (a : X.B.I.E)))) := by
      rw [hA, smul_neg]
    have := lat_gE_intDiv X mB hB hB' c _ (fun i j => (hAi i j).neg) (-Z) hneg
    exact intDiv_dvd (d := 2) (by rwa [mul_comm c 2])
  have hinv : Formalism.L2.SG.Pf.UnipB.gE X (-Z) * Formalism.L2.SG.Pf.UnipB.gE X Z = 1 := gE_mul X le_rfl hZ
  have hn' : ∀ y, X.crd (n.symm y) = Formalism.L2.SG.Pf.UnipB.gE X (-Z) *ᵥ X.crd y := by
    intro y
    conv_rhs => rw [← n.apply_symm_apply y, hn, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  rw [Formalism.L2.SG.Pf.gmap_eq_iff]
  intro x
  constructor
  · intro hx
    have := H _ h2 n.symm.toLinearMap hn' (n x) hx
    simpa using this
  · intro hx
    exact H _ h1 n.toLinearMap hn x hx

end Formalism.L2.SG.TermOp.Vanish
end
end
