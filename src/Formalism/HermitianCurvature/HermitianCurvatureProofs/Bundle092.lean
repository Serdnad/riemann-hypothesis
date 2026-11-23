module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle043
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JointInstanceTheoremA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle047
public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle061
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle088
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle065
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
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
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBC

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

variable {H : Type} {f : ℕ}

def psiG (g : ℝ) (l c : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((2 * (l * c).re / g : ℝ) : ℂ))

def Fz (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ) (z : crystallineComparison.V f) : ℂ :=
  ∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * ∏ v, D v h h' (z v)

def Nz (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ) (z : crystallineComparison.V f) : ℝ :=
  if Good z then (Fz Y κ D z).re else 0

theorem Fz_nonneg (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z)) (z : crystallineComparison.V f) (hz : Good z) :
    0 ≤ Fz Y κ D z := by
  let k : Option (Fin f) → H → H → ℂ := fun o => match o with
    | none => κ
    | some v => fun h h' => D v h h' (z v)
  have hk : ∀ o, TB.PSDOn Y (k o) := by
    intro o; rcases o with _ | v
    · exact hκ
    · exact hD v (z v) (hz v)
  have hS := Formalism.FourierDecayAlt.P.schur_product _ (Option (Fin f)) Y k hk
  have hC := JCx1.decay.psd_compress Y _ hS (fun _ : Unit => Y) (fun _ => id) (fun _ h hh => hh)
  have := hC.diag_nonneg (i := ())
  simp only [Matrix.of_apply, id] at this
  convert this using 1
  unfold Fz
  simp [Fintype.prod_option, k]

theorem Nz_nonneg (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z)) (z : crystallineComparison.V f) : 0 ≤ Nz Y κ D z := by
  unfold Nz; split_ifs with hz
  · exact (Complex.nonneg_iff.1 (Fz_nonneg Y κ hκ D hD z hz)).1
  · exact le_rfl

theorem isOpen_good : IsOpen {z : crystallineComparison.V f | Good z} := by
  have : {z : crystallineComparison.V f | Good z} = ⋂ v, (fun z : crystallineComparison.V f => z v) ⁻¹' {0}ᶜ := by
    ext z; simp [Good]
  rw [this]
  exact isOpen_iInter_of_finite fun v => (continuous_apply v).isOpen_preimage _ isOpen_compl_singleton

theorem Fz_continuousAt (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ) (z : crystallineComparison.V f) (hz : Good z) :
    ContinuousAt (Fz Y κ D) z := by
  unfold Fz ContinuousAt
  refine tendsto_finsetSum _ fun h hh => tendsto_finsetSum _ fun h' hh' => ?_
  refine tendsto_const_nhds.mul (tendsto_finsetProd _ fun v _ => ?_)
  have := (hDc v h hh h' hh').continuousAt (isOpen_compl_singleton.mem_nhds (hz v))
  exact this.tendsto.comp (continuous_apply v).continuousAt.tendsto

theorem Nz_lsc (Y : Finset H) (κ : H → H → ℂ) (hκ : TB.PSDOn Y κ) (D : Fin f → H → H → ℂ → ℂ)
    (hD : ∀ v (z : ℂ), z ≠ 0 → TB.PSDOn Y (fun h h' => D v h h' z))
    (hDc : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, ContinuousOn (D v h h') {0}ᶜ) : LowerSemicontinuous (Nz Y κ D) := by
  intro z y hy
  by_cases hz : Good z
  · have hc : ContinuousAt (fun z => (Fz Y κ D z).re) z :=
      Complex.continuous_re.continuousAt.comp (Fz_continuousAt Y κ D hDc z hz)
    have h1 : ∀ᶠ z' in 𝓝 z, Good z' := isOpen_good.mem_nhds hz
    have hy' : y < (Fz Y κ D z).re := by simpa [Nz, hz] using hy
    filter_upwards [h1, hc.eventually (lt_mem_nhds hy')] with z' hg hl
    simpa [Nz, hg] using hl
  · have hy' : y < 0 := by simpa [Nz, hz] using hy
    exact Filter.Eventually.of_forall fun z' => hy'.trans_le (Nz_nonneg Y κ hκ D hD z')

theorem ae_good : ∀ᵐ z : crystallineComparison.V f, Good z := by
  have : ∀ v : Fin f, ∀ᵐ z : crystallineComparison.V f, z v ≠ 0 := by
    intro v
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [MeasureTheory.volume_pi]
    exact Measure.pi_hyperplane _ v 0
  exact (ae_all_iff.2 this).mono fun z hz => hz

theorem Fz_integrable (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) : Integrable (Fz Y κ D) := by
  unfold Fz
  refine integrable_finsetSum _ fun h hh => integrable_finsetSum _ fun h' hh' => ?_
  exact (Integrable.fintype_prod (f := fun v => D v h h') fun v => hDi v h hh h' hh').const_mul _

theorem Nz_integrable (Y : Finset H) (κ : H → H → ℂ) (D : Fin f → H → H → ℂ → ℂ)
    (hDi : ∀ v, ∀ h ∈ Y, ∀ h' ∈ Y, Integrable (D v h h')) : Integrable (Nz Y κ D) := by
  refine (Fz_integrable Y κ D hDi).re.congr ?_
  filter_upwards [ae_good] with z hz
  simp [Nz, hz]

end

end Formalism.FourierDecayAlt.P.PBC
end

section

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

def CapEig (P : M.Par) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)) (Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (ρ : M.Ty P) (X : Wq →L[ℂ] Wp) : Prop :=
  ∀ (Y : ℂ) (v : Wq), X (qdet (Qr.EB π' Fr) (Y + ((P.k : ℂ) - 2) / 2) v) = M.xC P ρ Y • X v

def FibAt (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (g : Q.Mx k r) : Set (Wq →L[ℂ] Wp) :=
  {X | ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', h * g * h' = g → (π h).comp (X.comp (π' h')) = X}

end preds

def KLEig : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ Qρ : M.Ty P → (Wq →L[ℂ] Wq), KapPt P Bs d Qρ →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [(NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] Fr →
    ∀ (ρ : M.Ty P), ∀ E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
      (E.comp (Qρ ρ) = E ↔ CapEig P Bs.π' Fr ρ E)

def KLAtMost : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ g : Q.Mx P.k P.r, g ∈ Q.Glev P.k P.r (Fin.last P.r) →
    Q.GGl P.k P.r z z' g ≠ 0 → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Fr →
    ∀ (ρ : M.Ty P) (E Z : Wq →L[ℂ] Wp), E ∈ FibAt P.k P.r z z' π π' g → Z ∈ FibAt P.k P.r z z' π π' g →
      CapEig P π' Fr ρ E → CapEig P π' Fr ρ Z → E ≠ 0 → ∃ c : ℂ, Z = c • E

def KLExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ g : Q.Mx P.k P.r, g ∈ Q.Glev P.k P.r (Fin.last P.r) →
    Q.GGl P.k P.r z z' g ≠ 0 → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Fr →
    ∀ ρ : M.Ty P, ∃ E ∈ FibAt P.k P.r z z' π π' g, CapEig P π' Fr ρ E ∧ E ≠ 0

def KLIsoAlg : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ V')
    (m : Fin n → ℂ), GlRel E → GlRel E' → Qr.Irr E → Qr.Irr E' → Qr.SDec m →
    (∀ (w : ℂ) (v : V), qdet E w v = Qr.cpol m w • v) → (∀ (w : ℂ) (v : V'), qdet E' w v = Qr.cpol m w • v) →
    ∃ A : V' →ₗ[ℂ] V, A ≠ 0 ∧ ∀ a b, A ∘ₗ E' a b = E a b ∘ₗ A

def KLLieGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → Qr.IsRepW k r z π → Qr.IsRepW k r z' π' →
    ∀ g : Q.Mx k r, g ∈ Q.Glev k r (Fin.last r) → Q.GGl k r z z' g ≠ 0 →
    ∀ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [g⁻¹ *ᵥ z, z'] Fr →
    ∀ A : Wq →L[ℂ] Wp, (∀ (a b : Fin (k - 1)) (v : Wq), A (Qr.EB π' Fr a b v) = Qr.EB π (fun i => g *ᵥ Fr i) a b (A v)) →
      A ∈ FibAt k r z z' π π' g

def KLExistsOf : Prop := KLIsoAlg → KLLieGrp → KLExists

def GTKLineOfCut : Prop := KLEig → KLAtMost → KLExists → GTKLine

section asm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem fib_iff_fibAt {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {ζ : ℂ} {X : Wq →L[ℂ] Wp} :
    X ∈ NF.Fib k r z z' μsec π π' ζ ↔ X ∈ FibAt k r z z' π π' (NF.muZ k r μsec ζ) := by
  first
  | exact Iff.rfl
  | (simp only [NF.Fib, FibAt, Set.mem_setOf_eq, NF.Stab, Prod.forall]
     constructor
     · intro h a ha b hb hab
       exact h a b ⟨ha, hb, hab⟩
     · rintro h a b ⟨ha, hb, hab⟩
       exact h a ha b hb hab)

theorem fibAt_smul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {g : Q.Mx k r} {X : Wq →L[ℂ] Wp} (hX : X ∈ FibAt k r z z' π π' g) (c : ℂ) :
    c • X ∈ FibAt k r z z' π π' g := by
  simp only [FibAt, Set.mem_setOf_eq] at hX ⊢
  intro h hh h' hh' hg
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hX h hh h' hh' hg]

theorem capEig_smul {P : M.Par} {π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)}
    {Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ} {ρ : M.Ty P} {X : Wq →L[ℂ] Wp}
    (hX : CapEig (Wp := Wp) P π' Fr ρ X) (c : ℂ) : CapEig P π' Fr ρ (c • X) := by
  unfold CapEig at hX ⊢
  intro Y v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hX Y v, smul_comm]

end asm

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsVec_ne_zero {A : Wq →L[ℂ] Wp} (hA : A ≠ 0) : B.hsVec A ≠ 0 := by
  intro h
  apply hA
  have hi : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := by
    intro i
    have h2 := congrArg
      (fun x : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) => (WithLp.ofLp x : Fin _ → Wp) i) h
    simpa [B.hsVec] using h2
  apply ContinuousLinearMap.coe_injective
  exact (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => by simpa using hi i)

end hs

theorem gTKLine_of_cut : GTKLineOfCut := by
  intro hEig hAt hEx Wp Wq _ _ _ _ _ _ P Bs X d hH Qρ hK ζ hζ ρ
  obtain ⟨hpl, hk, hcs, -, -, -, -⟩ := id hH
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hTz]; exact hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hTz']; exact hOK.T'_pos
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef
  have hg : g ∈ Q.Glev P.k P.r (Fin.last P.r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb hcs.1 hζ')
  have hGG : Q.GGl P.k P.r Bs.z Bs.z' g ≠ 0 := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' hcs.1 hζ']
    linarith
  obtain ⟨-, -, Fr, -, -, -, hFr, -⟩ := Formalism.FourierDecayAlt.P.Qx8.geom_at hOK.k_pos hz hz' hT hT' hg hGG
  obtain ⟨E0, hE0f, hE0e, hE0n⟩ := hEx Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk g hg hGG Fr hFr ρ
  set s : ℝ := ‖B.hsVec E0‖ with hs
  have hs0 : s ≠ 0 := by
    rw [hs]; exact norm_ne_zero_iff.mpr (hsVec_ne_zero hE0n)
  set E : Wq →L[ℂ] Wp := ((s : ℂ)⁻¹) • E0 with hEdef
  have hEf : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := fib_iff_fibAt.mpr (fibAt_smul hE0f _)
  have hEe : CapEig P Bs.π' Fr ρ E := capEig_smul hE0e _
  have hEn : E ≠ 0 := by
    rw [hEdef]
    exact smul_ne_zero (inv_ne_zero (by exact_mod_cast hs0)) hE0n
  have hunit : inner ℂ (B.hsVec E) (B.hsVec E) = (1 : ℂ) := by
    rw [hEdef, hsVec_smul, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, ← hs]
    simp only [map_inv₀, Complex.conj_ofReal]
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
    field_simp
    rfl
  refine ⟨E, hEf, (hEig Wp Wq P Bs X d hH Qρ hK ζ hζ Fr hFr ρ E hEf).mpr hEe, hunit, fun Z hZf hZq => ?_⟩
  have hZe : CapEig P Bs.π' Fr ρ Z := (hEig Wp Wq P Bs X d hH Qρ hK ζ hζ Fr hFr ρ Z hZf).mp hZq
  obtain ⟨c, hc⟩ := hAt Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk g hg hGG Fr hFr ρ E Z
    (fib_iff_fibAt.mp hEf) (fib_iff_fibAt.mp hZf) hEe hZe hEn
  have hi : inner ℂ (B.hsVec E) (B.hsVec Z) = c := by
    rw [hc, hsVec_smul c E, inner_smul_right, hunit, mul_one]
  rw [hi]
  exact hc

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Ent

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem smoothG_of_sf {a : Mx k ρ → ℂ}
    (h : SmoothFam k ρ (Fin.last ρ) (Set.univ : Set (Formalism.FourierDecayAlt.P.Qx3.XX k ρ)) (fun _ g => a g)) : SmoothG k ρ a := by
  intro y₀ hy₀
  obtain ⟨U, F, hU, hxU, hF, hfF⟩ := h ((0 : Fin ρ → ℂ), Matrix.of y₀) (Set.mem_univ _) hy₀
  have hm : Continuous fun y : Mt k ρ => (((0 : Fin ρ → ℂ), (Matrix.of y : Mx k ρ)) : Formalism.FourierDecayAlt.P.Qx3.XX k ρ) :=
    continuous_const.prodMk continuous_id
  have hmd : ContDiff ℝ ∞ fun y : Mt k ρ => (((0 : Fin ρ → ℂ), (Matrix.of y : Mx k ρ)) : Formalism.FourierDecayAlt.P.Qx3.XX k ρ) :=
    contDiff_const.prodMk contDiff_id
  refine ⟨(fun y : Mt k ρ => (((0 : Fin ρ → ℂ), (Matrix.of y : Mx k ρ)) : Formalism.FourierDecayAlt.P.Qx3.XX k ρ)) ⁻¹' U,
    fun y => F ((0 : Fin ρ → ℂ), Matrix.of y), hU.preimage hm, hxU, hF.comp hmd.contDiffOn (fun y hy => hy),
    fun y hy hG => hfF _ hy hG⟩

theorem smoothG_yv (z : Fin (2 * ρ + k + 1) → ℂ) (j : Fin (mdim k ρ (Fin.last ρ))) :
    SmoothG k ρ (fun g => yv k ρ z (Fin.last ρ) g j) :=
  smoothG_of_sf (Formalism.FourierDecayAlt.P.Qx3.sf_yv z j)

theorem smoothG_ybv (z : Fin (2 * ρ + k + 1) → ℂ) (j : Fin (mdim k ρ (Fin.last ρ))) :
    SmoothG k ρ (fun g => ybv k ρ z (Fin.last ρ) g j) :=
  smoothG_of_sf (Formalism.FourierDecayAlt.P.Qx3.sf_ybv z j)

theorem parOK_EH (a b : Fin (mdim k ρ (Fin.last ρ))) :
    ParOK k ρ (E := E) (EH k ρ (posL k ρ (Fin.last ρ) a) (posL k ρ (Fin.last ρ) b)) :=
  parOK_congr (parOK_add (parOK_rdV (Formalism.FourierDecayAlt.P.Qx3.lieLev_of (Formalism.FourierDecayAlt.P.Qx3.hpart_lie (Fin.last ρ) a b).1))
    (parOK_csmul Complex.I
      (parOK_rdV (Formalism.FourierDecayAlt.P.Qx3.lieLev_of (Formalism.FourierDecayAlt.P.Qx3.hpart_lie (Fin.last ρ) a b).2)))) (fun f g => rfl)

theorem parOK_Top (u : ℂ) (a b : Fin (mdim k ρ (Fin.last ρ))) :
    ParOK k ρ (E := E) (Top (EH k ρ) u (posL k ρ (Fin.last ρ) a) (posL k ρ (Fin.last ρ) b)) := by
  by_cases hab : posL k ρ (Fin.last ρ) a = posL k ρ (Fin.last ρ) b
  · exact parOK_congr (parOK_add (parOK_csmul u parOK_id) (parOK_EH a b)) (fun f g => by simp [Formalism.QuantumDeterminants.Top, hab])
  · exact parOK_congr (parOK_add parOK_zero (parOK_EH a b)) (fun f g => by simp [Formalism.QuantumDeterminants.Top, hab])

theorem parOK_qminor {t : ℕ} (a b : Fin t → Fin (mdim k ρ (Fin.last ρ))) (u : ℂ) :
    ParOK k ρ (E := E) (qminorOp (EH k ρ) (posL k ρ (Fin.last ρ) ∘ a) (posL k ρ (Fin.last ρ) ∘ b) u) := by
  have key : ∀ σ : Equiv.Perm (Fin t), ParOK k ρ (E := E) (fun f g =>
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun j : Fin t =>
        Top (E := E) (EH k ρ) (u - ((j : ℕ) : ℂ)) ((posL k ρ (Fin.last ρ) ∘ a) (σ j))
          ((posL k ρ (Fin.last ρ) ∘ b) j)).foldr (fun T h => T h) f g)) := by
    intro σ
    refine parOK_csmul _ (parOK_foldr _ ?_)
    intro T hT
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact parOK_Top _ _ _
  refine parOK_congr (parOK_sum Finset.univ (fun σ _ => key σ)) (fun f g => ?_)
  simp [qminorOp, Finset.sum_apply]

theorem parOK_chatL (u : ℂ) (a β : Mx k ρ → Fin (mdim k ρ (Fin.last ρ)) → ℂ)
    (ha : ∀ j, SmoothG k ρ (fun g => a g j)) (hβ : ∀ j, SmoothG k ρ (fun g => β g j)) :
    ParOK k ρ (E := E) (chatL (EH k ρ) (posL k ρ (Fin.last ρ)) u a β) := by
  refine parOK_congr (parOK_sum Finset.univ fun i' _ => parOK_sum Finset.univ fun j' _ =>
    parOK_smulG (smoothG_mul (smoothG_mul (smoothG_const _) (hβ i')) (ha j')) (parOK_qminor _ _ _))
    (fun f g => rfl)

theorem parOK_chat2L (u : ℂ) (a a' β β' : Mx k ρ → Fin (mdim k ρ (Fin.last ρ)) → ℂ)
    (ha : ∀ j, SmoothG k ρ (fun g => a g j)) (ha' : ∀ j, SmoothG k ρ (fun g => a' g j))
    (hβ : ∀ j, SmoothG k ρ (fun g => β g j)) (hβ' : ∀ j, SmoothG k ρ (fun g => β' g j)) :
    ParOK k ρ (E := E) (chat2L (EH k ρ) (posL k ρ (Fin.last ρ)) u a a' β β') := by
  refine parOK_congr (parOK_sum Finset.univ fun i₁ _ => parOK_sum Finset.univ fun i₂ _ =>
    parOK_sum Finset.univ fun j₁ _ => parOK_sum Finset.univ fun j₂ _ => ?_) (fun f g => rfl)
  by_cases hc : i₁ < i₂ ∧ j₁ < j₂
  · refine parOK_congr (parOK_smulG (smoothG_mul (smoothG_mul
      (smoothG_const ((-1 : ℂ) ^ ((i₁ : ℕ) + (i₂ : ℕ) + (j₁ : ℕ) + (j₂ : ℕ))))
      (smoothG_sub (smoothG_mul (hβ i₁) (hβ' i₂)) (smoothG_mul (hβ i₂) (hβ' i₁))))
      (smoothG_sub (smoothG_mul (ha j₁) (ha' j₂)) (smoothG_mul (ha j₂) (ha' j₁)))) (parOK_qminor (skip2 i₁ i₂) (skip2 j₁ j₂) u))
      (fun f g => by simp only [if_pos hc])
  · exact parOK_congr parOK_zero (fun f g => by simp only [if_neg hc])

theorem parOK_tL (z z' : Fin (2 * ρ + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    ParOK k ρ (E := E) (tL k ρ z z' (Fin.last ρ) Y p q) := by
  fin_cases p <;> fin_cases q
  · show ParOK k ρ (capL k ρ (Fin.last ρ) (uC k ρ (Fin.last ρ) Y))
    exact parOK_qminor id id _
  · show ParOK k ρ (fun f g => -(chatL (EH k ρ) (posL k ρ (Fin.last ρ)) (uC k ρ (Fin.last ρ) Y - 1)
      (fun _ => xv k ρ z' (Fin.last ρ)) (ybv k ρ z (Fin.last ρ)) f g))
    exact parOK_neg (parOK_chatL _ _ _ (fun j => smoothG_const _) (fun j => smoothG_ybv z j))
  · show ParOK k ρ (fun f g => -(chatL (EH k ρ) (posL k ρ (Fin.last ρ)) (uC k ρ (Fin.last ρ) Y) (yv k ρ z (Fin.last ρ))
      (fun _ => xbv k ρ z' (Fin.last ρ)) f g))
    exact parOK_neg (parOK_chatL _ _ _ (fun j => smoothG_yv z j) (fun j => smoothG_const _))
  · show ParOK k ρ (fun f g => -(chat2L (EH k ρ) (posL k ρ (Fin.last ρ)) (uC k ρ (Fin.last ρ) Y - 1)
      (yv k ρ z (Fin.last ρ)) (fun _ => xv k ρ z' (Fin.last ρ)) (ybv k ρ z (Fin.last ρ))
      (fun _ => xbv k ρ z' (Fin.last ρ)) f g))
    exact parOK_neg (parOK_chat2L _ _ _ _ _ (fun j => smoothG_yv z j) (fun j => smoothG_const _)
      (fun j => smoothG_ybv z j) (fun j => smoothG_const _))

end Ent

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

section

open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem quantum_minor_border_expansion_first {n m : ℕ} (E : Fin n → Fin n → A) (e : Fin n) (f b : Fin m → Fin n) (hE : GlRel E)
    (hf : ∀ j, f j ≠ e) (hb : ∀ j, b j ≠ e) (u : ℂ) :
    qminor E (bE e f) (bE e b) u = Tm E u e e * qminor E f b (u - 1) -
      ∑ w : Fin m, ∑ x : Fin m, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (E (f w) e * qminor E (f ∘ skip1 w) (b ∘ skip1 x) (u - 2) * E e (b x)) := by
  rw [Qx6.expFCE E expansion_first_column]
  refine Qx6.add_eq_sub_of ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Qx6.qm_dropE E expansion_last_line quantumMinorRowSkew_holds hE, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Qx6.Tm_ne E _ (hf w), Qx6.Tm_ne E _ (hb x).symm, ← zsmul_eq_mul, mul_smul_comm, smul_smul, ← pow_add,
    ← neg_smul, show u - 1 - 1 = u - 2 by ring, mul_assoc]
  congr 1
  rw [show (w : ℕ) + 1 + (x : ℕ) = (w : ℕ) + (x : ℕ) + 1 by ring, pow_succ]
  ring

end Formalism.FourierDecayAlt.P.CutMP.CapelliExpansionLemmas
end
end
