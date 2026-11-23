module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle196
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle217
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle197
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle181
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle180
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle010
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle220
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev

@[expose] public section

section

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.CsdBack

theorem invTOp_involutive {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} :
    Function.Involutive (invTOp : Op E a → Op E a) := by
  intro o
  cases o with
  | fin k => simp only [invTOp]; congr 1
  | cpt k => simp only [invTOp]; congr 1; ext i j; simp [barK, Matrix.star_apply]
  | lie X =>
    simp only [invTOp]; congr 1
    funext i j
    exact neg_neg (X i j)

theorem conjOp_involutive {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ} :
    Function.Involutive (conjOp : Op L a → Op L a) := by
  intro o
  cases o with
  | fin k => simp only [conjOp]; congr 1; ext i j; simp [GlobalTheory.ThetaPull.cFin_cFin]
  | cpt k => simp only [conjOp]; congr 1; ext i j; simp [barK, Matrix.star_apply]
  | lie X => simp only [conjOp]; congr 1; ext i j; simp

theorem isCsd_of_paired : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (a : ℕ) (π : CuspSub L a), Paired π π invTOp → DualIsConj π → π.IsCsd := by
  intro hP L _ _ _ a π h1 h2
  obtain ⟨B₁, l1, r1, f1, c1, x1⟩ := h1
  obtain ⟨B₂, l2, r2, f2, c2, x2⟩ := h2
  obtain ⟨P, hP0, hPP, hfin, hadj⟩ := GlobalTheory.T.exists_idempotent_finiteRank_adjoint_cuspidal hP L a π
  obtain ⟨P₁, e1⟩ := hadj invTOp (Or.inl rfl) B₁ l1 r1 f1 c1 x1
  obtain ⟨P₂, e2⟩ := hadj conjOp (Or.inr rfl) B₂ l2 r2 f2 c2 x2
  obtain ⟨v, hv⟩ : ∃ v, P v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP0 (LinearMap.ext h)
  obtain ⟨g, hg⟩ : ∃ g : Module.Dual ℂ π.V, g (P v) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ (P v)).1 h)
  have hf : (g ∘ₗ P) ∘ₗ P = g ∘ₗ P := by rw [LinearMap.comp_assoc, hPP]
  obtain ⟨ψ₁, hψ₁⟩ := GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate B₁ l1 r1 P P₁ hPP hfin e1 (g ∘ₗ P) hf
  obtain ⟨ψ₂, hψ₂⟩ := GlobalTheory.T.exists_representing_of_comp_idempotent_of_nondegenerate B₂ l2 r2 P P₂ hPP hfin e2 (g ∘ₗ P) hf
  have hne : ψ₁ ≠ 0 := by
    rintro rfl
    apply hg
    have := hψ₁ v
    simp only [map_zero, LinearMap.comp_apply] at this
    exact this.symm
  obtain ⟨S, hS⟩ := GlobalTheory.T.cuspRep_dual_iso_of_common_represented_functional L a π invTOp conjOp invTOp_involutive conjOp_involutive B₁ B₂ l1 r1 f1 c1 x1
    l2 r2 f2 c2 x2 ψ₁ ψ₂ hne (fun φ => (hψ₁ φ).trans (hψ₂ φ).symm)
  exact GlobalTheory.T.isConjSelfDual_of_invTranspose_iso_cmConj L a π S hS

end GlobalTheory.CsdBack

end
end

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

namespace GlobalTheory.KerCommon

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_scale : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ (ι : Type) [Fintype ι] (a b : ℕ) (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ g : 𝓞 D.host.E, (∃ k : 𝓞 D.host.E, g = 1 + (cl : 𝓞 D.host.E) * k) ∧ (∀ Q ∈ SS, g ∉ Q.asIdeal) ∧ ∀ i, ((∀ x ∈ N i, g • x ∈ N₀) ∧ ∀ x ∈ N₀, g • x ∈ N i) ∧ ((∀ x ∈ N' i, g • x ∈ N₀') ∧ ∀ x ∈ N₀', g • x ∈ N' i) := GlobalTheory.T.exists_common_scale_lattice_pairs_split_prime

theorem perO_scale : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA0 : Submodule (𝓞 E) E) (N₁ N₂ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (w : 𝓞 E), (∀ y ∈ N₂, w • y ∈ N₁) → (∀ y ∈ N₁', w • y ∈ N₂') → ∀ x ∈ perO AA0 N₁ N₁', (w * w) • x ∈ perO AA0 N₂ N₂' := by
  intro E _ _ _ a b AA0 N₁ N₂ N₁' N₂' w h2 h1 x hx
  unfold perO at hx ⊢
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, y, hy, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨r, hr, (w * w) • y, ?_, ?_⟩
    · intro v hv
      have h3 := h1 _ (hy _ (h2 v hv))
      have e : ((w * w) • y) v = w • y (w • v) := by
        rw [LinearMap.smul_apply, mul_smul, LinearMap.map_smul_of_tower]
      rw [e]
      exact h3
    · rw [smul_comm]
  | zero => rw [smul_zero]; exact zero_mem _
  | add _ _ _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o z _ h => rw [smul_comm]; exact Submodule.smul_mem _ o h

theorem common_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (cl : ℕ) (N₀ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₀' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (N : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (g : 𝓞 E), δ ≠ 0 → (∃ k : 𝓞 E, g = 1 + (cl : 𝓞 E) * k) → (∀ i, (∀ x ∈ perO AA0 (N i) (N' i), g • x ∈ perO AA0 N₀ N₀') ∧ ∀ x ∈ perO AA0 N₀ N₀', g • x ∈ perO AA0 (N i) (N' i)) → relIdx (LamC emb δ AA0 N₀ N₀') (AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (BC emb δ AA0 SS N₀ N₀' cl) (LamC emb δ AA0 N₀ N₀' ⊓ AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (LamC emb δ AA0 N₀ N₀') (BC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → ∃ SX SA SB : Finset (VV ι a b), ∀ i, IsReps (LamC emb δ AA0 (N i) (N' i)) (AC emb δ AA0 SS (N i) (N' i) cl) SX ∧ IsReps (BC emb δ AA0 SS (N i) (N' i) cl) (LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl) SA ∧ IsReps (LamC emb δ AA0 (N i) (N' i)) (BC emb δ AA0 SS (N i) (N' i) cl) SB := GlobalTheory.T.common_representatives_period_lattice_halves

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩

theorem unimod_iff {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E n)) :
    Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.L2.Col.hStd D.host.E n) L ↔
      ∀ y, y ∈ L ↔ ∀ x ∈ L, Formalism.BasicNotions.stdH D.host.E n x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hm : ∀ y, y ∈ Formalism.HermitianLatticesTheory.dual (Formalism.L2.Col.hStd D.host.E n) L ↔
      ∀ x ∈ L, Formalism.BasicNotions.stdH D.host.E n x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
      Submodule.mem_one, RingHom.mem_range]
    rfl
  unfold Formalism.HermitianLatticesTheory.IsUnimodular
  constructor
  · intro h y
    rw [← hm y, h]
  · intro h
    ext y
    rw [hm y]
    exact (h y).symm

theorem admissible_pair_twist {D : D7} {a b : ℕ} (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl) (ex : HeightOneSpectrum (𝓞 D.host.E) → ℤ)
    (h01 : ∀ Q, ex Q = 1 ∨ ex Q = 0 ∨ ex Q = -1) (hc : ∀ Q, ex (Formalism.L2.Col.conjPrime₂ Q) = -ex Q) :
    TaylorLogMetric.admitted D a b N (twist₂ N' cl ex) := by
  have hl := hh_tw_lattice N' ⟨hA.2.2.2.1, by
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli⟩ hcl ex h01
  have hspan : Submodule.span D.host.E (↑(twist₂ N' cl ex) : Set (Fin b → D.host.E)) = ⊤ := by
    apply top_unique
    rw [← hA.2.2.2.2.1]
    apply Submodule.span_le.mpr
    intro x hx
    change x ∈ Submodule.span D.host.E (↑(twist₂ N' cl ex) : Set (Fin b → D.host.E))
    have hx' : (cl : 𝓞 D.host.E) • x ∈ Submodule.span D.host.E (↑(twist₂ N' cl ex) : Set (Fin b → D.host.E)) :=
      Submodule.subset_span (hh_tw_of N' hcl ex h01 hx)
    have hc : (cl : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hcl.ne'
    have hx'' : (cl : D.host.E) • x ∈ Submodule.span D.host.E (↑(twist₂ N' cl ex) : Set (Fin b → D.host.E)) := by
      simpa only [Nat.cast_smul_eq_nsmul] using hx'
    have := Submodule.smul_mem (Submodule.span D.host.E (↑(twist₂ N' cl ex) : Set (Fin b → D.host.E))) (cl : D.host.E)⁻¹ hx''
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using this
  exact ⟨hA.1, hA.2.1, hA.2.2.1, hl.fg, hspan,
    (unimod_iff _).1 (twist_selfDual D.host.E b N' cl ex hA.2.2.2.1 hcl hc ((unimod_iff _).2 hA.2.2.2.2.2))⟩

theorem split_of_adm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl)
    (hSS : ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS) :
    SplitHyp (hK D cc δ a b) (alK D cc δ a b) (halfA cc δ SS cl N N') (halfB cc δ SS cl N N') (lamK cc δ N N') := by
  have := tau_nonempty D
  have he1 : ∀ Q, expS SS Q = 1 ∨ expS SS Q = 0 ∨ expS SS Q = -1 := expS_cases SS
  have he2 : ∀ Q, (fun Q => -expS SS Q) Q = 1 ∨ (fun Q => -expS SS Q) Q = 0 ∨ (fun Q => -expS SS Q) Q = -1 := by
    intro Q
    have := he1 Q
    show -expS SS Q = 1 ∨ -expS SS Q = 0 ∨ -expS SS Q = -1
    omega
  have hconj1 : ∀ Q, expS SS (Formalism.L2.Col.conjPrime₂ Q) = -expS SS Q := exponent_set_conjugate D.host.E SS hSS
  have hconj2 : ∀ Q, (fun Q => -expS SS Q) (Formalism.L2.Col.conjPrime₂ Q) = -(fun Q => -expS SS Q) Q := by
    intro Q
    show -expS SS (Formalism.L2.Col.conjPrime₂ Q) = - -expS SS Q
    rw [hconj1 Q]
  exact half_periods_of_lattice D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (aaOf D cc) SS N N' cl
    (KS.Lat.delta_ne hcc hδ) hcl hSS hA.2.2.1.1 (laFacts_of_adm B hcc hδ hA)
    (laFacts_of_adm B hcc hδ (admissible_pair_twist cl N N' hA hcl _ he1 hconj1)) (laFacts_of_adm B hcc hδ (admissible_pair_twist cl N N' hA hcl _ he2 hconj2))

theorem finIdx_of_adm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl) : FinIdx cc δ SS cl N N' :=
  finite_index_of_fg D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) SS N N' cl hcl
    (period_lattice_finitely_generated D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) N N' hA.2.2.2.1 hA.2.2.1.2.1 (aaOf_fg cc))

theorem eNat_fixed_of_vec {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hV : B.VecP χ) {a b : ℕ}
    {N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} (hA : TaylorLogMetric.admitted D a b N N') :
    B.eNat χ a b N N' ∈ fixedBy (hK D cc δ a b) (alK D cc δ a b) (lamK cc δ N N') := by
  have hm := (hV a b N N' hA).1
  intro x hx z
  have hx' : x ∈ TaylorLogMetric.La D B.tor N N' := by rw [← lamK_eq cc δ N N']; exact hx
  have h1 := hm.2 x hx' z
  rw [U_eq_opU] at h1
  have hal : alK D cc δ a b x = TaylorLogMetric.al D B.tor x := by
    rw [KS.Lat.al_eq_La B hcc hδ hA x hx']
    unfold alK alV
    rw [HV_eq_formV]
  rw [hal]
  exact h1

theorem locP_eq_of_scale {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]
    (M M₀ : Submodule (𝓞 E) W) (g : 𝓞 E) (Q : HeightOneSpectrum (𝓞 E)) (hg : g ∉ Q.asIdeal)
    (h1 : ∀ x ∈ M, g • x ∈ M₀) (h2 : ∀ x ∈ M₀, g • x ∈ M) :
    Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M = Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M₀ := by
  have hg' : g ∈ Q.asIdeal.primeCompl := hg
  ext x
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨g * s, Q.asIdeal.primeCompl.mul_mem hg' hs, by rw [mul_smul]; exact h1 _ hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨g * s, Q.asIdeal.primeCompl.mul_mem hg' hs, by rw [mul_smul]; exact h2 _ hx⟩

theorem kerTh_common_op : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.LatAll → B.VecP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ T : (TaylorLogMetric.VC D a b → ℂ) →ₗ[ℂ] (TaylorLogMetric.VC D a b → ℂ), ∀ i, kerTh B χ SS cl (N i) (N' i) Ξ = T (B.eNat χ a b (N i) (N' i)) := by
  intro D cc δ B χ hcc hδ hδ0 _hL hV SS cl hcl hSS a b P _hP hPS hPS' hcP _hcP' N₀ N₀' Ξ hA0 hD ι _ N N' hN
  have := tau_nonempty D
  obtain ⟨g, ⟨k, hk⟩, hgQ, hg⟩ := exists_scale D P SS cl hPS hPS' hcP ι a b N N₀ N' N₀' fun i => (hN i).2
  have hsc : ∀ i, (∀ x ∈ perO (aaOf D cc) (N i) (N' i), (g * g) • x ∈ perO (aaOf D cc) N₀ N₀') ∧
      ∀ x ∈ perO (aaOf D cc) N₀ N₀', (g * g) • x ∈ perO (aaOf D cc) (N i) (N' i) := fun i =>
    ⟨perO_scale D.host.E a b (aaOf D cc) (N i) N₀ (N' i) N₀' g (hg i).1.2 (hg i).2.1,
      perO_scale D.host.E a b (aaOf D cc) N₀ (N i) N₀' (N' i) g (hg i).1.1 (hg i).2.2⟩
  have hI0 := finIdx_of_adm (cc := cc) (δ := δ) SS cl N₀ N₀' hA0 hcl
  obtain ⟨SX, SA, SB, hR⟩ := common_reps D.host.E D.what₂.Tau ι a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) SS cl N₀ N₀' N N' (g * g) hδ0
    ⟨k + k + (cl : 𝓞 D.host.E) * k * k, by rw [hk]; ring⟩ hsc hI0.1 hI0.2.1 hI0.2.2
  have hxi0 : ∀ z, xiL (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) 0 z = 0 := by
    intro z
    have h := (twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB 1 (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ)
      (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) 0 0 z).2.2.2
    have e : (fun v : TaylorLogMetric.VC D a b => (1 : ℂ) * (0 : TaylorLogMetric.VC D a b → ℂ) v + (0 : TaylorLogMetric.VC D a b → ℂ) v) = 0 := by
      funext v; simp
    rw [e, one_mul] at h
    linear_combination -h
  refine ⟨{ toFun := fun θ => xiL (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) θ,
            map_add' := ?_, map_smul' := ?_ }, fun i => ?_⟩
  · intro x y
    funext z
    have h := (twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB 1 (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ)
      (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) x y z).2.2.2
    have e : (fun v => (1 : ℂ) * x v + y v) = x + y := by funext v; simp
    rw [e, one_mul] at h
    simpa using h
  · intro c x
    funext z
    have h := (twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB c (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ)
      (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) x 0 z).2.2.2
    have e : (fun v => c * x v + (0 : TaylorLogMetric.VC D a b → ℂ) v) = c • x := by funext v; simp
    rw [e, hxi0, add_zero] at h
    simpa using h
  · obtain ⟨hAi, -, -⟩ := hN i
    have hyp := split_of_adm B SS cl (N i) (N' i) hcc hδ hAi hcl hSS
    have hIi := finIdx_of_adm (cc := cc) (δ := δ) SS cl (N i) (N' i) hAi hcl
    have hθ := eNat_fixed_of_vec B χ hcc hδ hV hAi
    have hg2 : ∀ Q ∈ SS, g * g ∉ Q.asIdeal := fun Q hQ h =>
      (Q.isPrime.mem_or_mem h).elim (hgQ Q hQ) (hgQ Q hQ)
    have hDi : DatLoc D cc SS cl (N i) (N' i) Ξ :=
      hD.of_locP_eq fun Q hQ => locP_eq_of_scale _ _ (g * g) Q (hg2 Q hQ) (hsc i).1 (hsc i).2
    have hinv := hDi.invOn (fun τ => TaylorLogMetric.embT D τ) δ (embH_inj _ hδ0)
    funext z
    exact twist_representatives _ (hK D cc δ a b) (alK D cc δ a b) _ _ _ hyp SX SA SB _ _ _ (hR i).1 (hR i).2.1 (hR i).2.2
      (repsOf_spec _ _ hIi.1) (repsOf_spec _ _ hIi.2.1) (repsOf_spec _ _ hIi.2.2) 1 _ hθ _ hinv z

end GlobalTheory.KerCommon
end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.HeckeScalarDC

open GlobalTheory.HeckeScalarSph

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem dc_scalar_fin (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S)
    (s : SplitPlace L) (α : GAf L n) (hα : TrivOutside {s.v} α) (Rα : Finset (GAf L n))
    (hRα0 : (∀ γ ∈ Rα, ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, γ = k₁ * α * k₂) ∧
      ∀ x, (∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ Rα ∧ γ⁻¹ * x ∈ Umax L n) :
    ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) →
      ∑ γ ∈ Rα, NG.rt L n γ f = c • f := by
  classical
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose R hR using exists_repsU (n := n) s.v
  have hRα := reps_of_repsU hα hRα0
  have hRtriv : ∀ γ ∈ Rα, TrivOutside {s.v} γ := by
    intro γ hγ
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hRα0.1 γ hγ
    exact triv_mul (triv_mul h₁.2 hα) h₂.2
  let T : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W) := ∑ γ ∈ Rα, rtHom L n a.W γ
  have hT : ∀ x, T x = ∑ γ ∈ Rα, rtHom L n a.W γ x := fun x => LinearMap.sum_apply _ _ _
  have conv : ∀ {b x : GAf L n}, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * b * k₂) ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * b * k₂ :=
    ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
      fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ GlobalTheory.SphScalar.fixS (rtHom L n a.W) S (locK n s.v), T x = c • x := by
    refine GlobalTheory.SphScalar.abs_scalar (rtHom L n a.W) S hS.1.stable
      (fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, hst⟩ hle) (rank_le hS) (locK n s.v)
      {x | TrivOutside {s.v} x} {y | TrivOutside {s.v}ᶜ y}
      (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩)
      (fun κ hκ b hb => (hcomm κ b hκ.2 hb).eq) R (fun b hb => reps_of_repsU hb (hR b)) T ?_ ?_ ?_
    · intro x hx
      rw [hT]
      refine ⟨S.sum_mem fun γ _ => hS.1.stable γ x hx.1, fun κ hκ => ?_⟩

      rw [map_sum]
      have := hRα.sum_eq hRα hκ (fun g => rtHom L n a.W g x)
        (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
      simpa only [map_mul, Module.End.mul_apply] using this
    · intro b hb x _

      rw [hT, hT, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, (hcomm γ b (hRtriv γ hγ) hb).eq]
    · intro b hb x hx
      rw [hT, hT]
      exact GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical L n a.W s α b Rα (R b) hα hb (fun y hy => hRα0.2 y (conv.1 hy))
        (fun γ hγ => conv.2 (hRα0.1 γ hγ)) (fun y hy => (hR b).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hR b).1 γ hγ)) x (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
  refine ⟨c, fun f hf hfix => ?_⟩
  have e := hc f ⟨hf, fun κ hκ => hfix κ hκ.1 hκ.2⟩
  rw [hT] at e
  rw [← e]
  rfl

theorem dc_scalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (S : Submodule ℂ (Formalism.AUTREP.GAf L n → a.W)), Formalism.L2.NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (α : Formalism.AUTREP.GAf L n), TrivOutside {s.v} α → ∀ (ι : Type) (R : Finset ι) (r : ι → Formalism.AUTREP.GAf L n), (∀ γ ∈ R, ∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, r γ = k₁ * α * k₂) → (∀ x, (∃ k₁ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, ∃ k₂ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ (r γ)⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → Formalism.L2.NG.rt L n κ f = f) → ∑ γ ∈ R, Formalism.L2.NG.rt L n (r γ) f = c • f := by
  intro L _ _ _ n a S hS s α hα ι R r h1 h2
  classical
  have hinj : Set.InjOn r R := by
    intro γ hγ δ hδ e
    have hx := h1 γ hγ
    have hU : (r γ)⁻¹ * r γ ∈ Umax L n := by rw [inv_mul_cancel]; exact one_mem _
    exact (h2 (r γ) hx).unique ⟨hγ, hU⟩ ⟨hδ, by rw [← e]; exact hU⟩
  have hA : ∀ γ ∈ R.image r, ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, γ = k₁ * α * k₂ := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
    exact h1 δ hδ
  have hB : ∀ x, (∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * α * k₂) →
      ∃! γ, γ ∈ R.image r ∧ γ⁻¹ * x ∈ Umax L n := by
    intro x hx
    obtain ⟨γ, ⟨hγ, e⟩, hu⟩ := h2 x hx
    refine ⟨r γ, ⟨Finset.mem_image.2 ⟨γ, hγ, rfl⟩, e⟩, ?_⟩
    rintro y ⟨hy, ey⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hy
    rw [hu δ ⟨hδ, ey⟩]
  obtain ⟨c, hc⟩ := dc_scalar_fin a S hS s α hα (R.image r) ⟨hA, hB⟩
  refine ⟨c, fun f hf hfix => ?_⟩
  rw [← hc f hf hfix, Finset.sum_image (fun γ hγ δ hδ e => hinj hγ hδ e)]

end GlobalTheory.HeckeScalarDC

end
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd GlobalTheory.KerStd.HypCoord Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.HypCoord.Pair

theorem sum_bilin {R : Type*} [CommRing R] {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (F : κ → R) (G : μ → R) (X : ι → κ → R) (Y : ι → μ → R) :
    ∑ i, (∑ k, F k * X i k) * (∑ m, G m * Y i m) = ∑ k, ∑ m, F k * G m * ∑ i, X i k * Y i m := by
  have h1 : ∀ i, (∑ k, F k * X i k) * (∑ m, G m * Y i m) = ∑ k, ∑ m, F k * G m * (X i k * Y i m) := fun i => by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end GlobalTheory.KerStd.HypCoord.Pair


open GlobalTheory.KerStd.HypCoord.Pair in
theorem GlobalTheory.KerStd.HypCoord.hK_gK_dual : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → (IsResidueClassZero D p ∨ IsSg D p) → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Formalism.L2.KerInert.RepFrame.LamONB D lam b → ∀ w z a b₀ a₁ b₁, ∑ i, hK D lam P P' b w a b₀ i * gK D lam P P' b z a₁ b₁ i = if w = z ∧ a = a₁ ∧ b₀ = b₁ then 1 else 0 := by
  intro D p _ lam σ hσ hcl N N' L L' P P' hP hP' r b hL w z a b₀ a₁ b₁

  have hunit : ∀ {n : ℕ} (Q : D.what₂.Tau → Matrix (Fin n) (Fin n) D.host.E) (L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
      StdBases D lam L₀ Q → ∀ v, IsUnit ((Q (tauPl D v)).map (rhoK D lam v)).det := by
    intro n Q L₀ hQ v
    obtain ⟨ρ, hρ⟩ := exists_ringHom_rhoK D lam σ hσ hcl v
    have hf : rhoK D lam v = ⇑ρ := funext fun y => (hρ y).1
    have h1 := hQ.2.1 hcl v
    have hdet : IsUnit (Q (tauPl D v)).det :=
      Matrix.isUnit_det_of_left_inverse h1
    rw [hf, show ((Q (tauPl D v)).map ⇑ρ).det = ρ (Q (tauPl D v)).det from (RingHom.map_det ρ _).symm]
    exact hdet.map ρ

  have hker : ∀ (k m : Fin N' × Fin N), ∑ i, rhoK D lam w (b i k.1 k.2) * rhoK D lam z (D.host.conj (b i m.1 m.2)) =
      if (tauPl D w, k.1, k.2) = (tauPl D z, m.1, m.2) then 1 else 0 := by
    intro k m
    have e := hL (tauPl D w, k.1, k.2) (tauPl D z, m.1, m.2)
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [MulMemClass.coe_mul, coe_rhoK D lam σ hσ hcl]
    convert e using 1 <;> first | rfl | (split_ifs <;> simp)
  set A := ((P' (tauPl D w)).map (rhoK D lam w))⁻¹ with hA
  set B := ((P (tauPl D z)).map (rhoK D lam z))⁻¹ with hB
  have eh : ∀ i, hK D lam P P' b w a b₀ i =
      ∑ k : Fin N' × Fin N, (A b₀ k.1 * rhoK D lam w (P (tauPl D w) k.2 a)) * rhoK D lam w (b i k.1 k.2) := fun i => by
    rw [hK, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have eg : ∀ i, gK D lam P P' b z a₁ b₁ i =
      ∑ m : Fin N' × Fin N, (rhoK D lam z (P' (tauPl D z) m.1 b₁) * B a₁ m.2) * rhoK D lam z (D.host.conj (b i m.1 m.2)) := fun i => by
    rw [gK, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  simp only [eh, eg]
  rw [sum_bilin]
  simp only [hker]
  by_cases hwz : w = z
  · subst hwz
    have hsimp : ∀ k m : Fin N' × Fin N, ((tauPl D w, k.1, k.2) = (tauPl D w, m.1, m.2)) ↔ k = m := by
      intro k m
      simp [Prod.ext_iff]
    simp only [hsimp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have e1 : ∑ k : Fin N' × Fin N, A b₀ k.1 * rhoK D lam w (P (tauPl D w) k.2 a) *
        (rhoK D lam w (P' (tauPl D w) k.1 b₁) * B a₁ k.2) =
        (A * (P' (tauPl D w)).map (rhoK D lam w)) b₀ b₁ * (B * (P (tauPl D w)).map (rhoK D lam w)) a₁ a := by
      rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_mul_sum, Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by simp only [Matrix.map_apply]; ring
    rw [e1, hA, hB, Matrix.nonsing_inv_mul _ (hunit P' L' hP' w), Matrix.nonsing_inv_mul _ (hunit P L hP w),
      Matrix.one_apply, Matrix.one_apply]
    by_cases h1 : b₀ = b₁ <;> by_cases h2 : a = a₁ <;> simp [h1, h2, eq_comm]
  · have hne : tauPl D w ≠ tauPl D z := fun h => hwz ((tauPl_bij D).1 h)
    rw [if_neg (fun h => hwz h.1)]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg (fun h => hne (congrArg Prod.fst h)), mul_zero]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)

theorem _root_.GlobalTheory.T.exists_other_split_place_with_distinct_real_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w₀ : HeightOneSpectrum (𝓞 E)), ∃ w₁ : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w₁ ∧ w₁.under (𝓞 (maximalRealSubfield E)) ≠ w₀.under (𝓞 (maximalRealSubfield E)) := by
  first | exact @GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne | exact GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne | (intros; apply GlobalTheory.OtherSplitPlace.exists_isSplitAt_under_ne <;> assumption)
end
