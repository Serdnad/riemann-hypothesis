module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle005
public import Formalism.LocalToGlobal.HermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle300
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle101
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle096
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle091
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle269
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle081
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle158
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle262
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle209
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle301
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle302
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle263
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle278
public import Formalism.LocalToGlobal.HermitianForms.Bundle010
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.LocalToGlobal.IndefiniteReal.Bundle012
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.Match

theorem diag_lift : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (d : Fin n → (kv F v)ˣ), ∃ D : GL (Fin n) (v.adicCompletion F), (∀ x : Fin n → v.adicCompletion F, (∀ b, x b ∈ v.adicCompletionIntegers F) ↔ ∀ b, ((D : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ x) b ∈ v.adicCompletionIntegers F) ∧ ∀ M : Matrix (Fin n) (Fin n) (v.adicCompletion F), redM F v (((D⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * M * (D : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = diagonal (fun i => ((d i)⁻¹ : (kv F v)ˣ).1) * redM F v M * diagonal (fun i => ((d i : (kv F v)ˣ) : kv F v)) := by
  intro F _ _ v n d
  have hs := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers F)
  choose u hu using fun i => hs ((d i : (kv F v)ˣ) : kv F v)
  have hunit : ∀ i, IsUnit (u i) := fun i =>
    isUnit_of_map_unit (IsLocalRing.residue (v.adicCompletionIntegers F)) (u i) (by rw [hu i]; exact (d i).isUnit)
  let w : Fin n → (v.adicCompletionIntegers F)ˣ := fun i => (hunit i).unit
  let e : Fin n → (v.adicCompletion F)ˣ := fun i => Units.map (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)).toMonoidHom (w i)
  have he : ∀ i, ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := fun i => (w i : v.adicCompletionIntegers F).2
  have he' : ∀ i, (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := fun i => (((w i)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
  have hw : ∀ i, IsLocalRing.residue (v.adicCompletionIntegers F) ((w i : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) = ((d i : (kv F v)ˣ) : kv F v) := fun i => hu i
  have hw' : ∀ i, IsLocalRing.residue (v.adicCompletionIntegers F) (((w i)⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) = (((d i)⁻¹ : (kv F v)ˣ) : kv F v) := by
    intro i
    have h1 := congrArg Units.val (map_inv (Units.map (IsLocalRing.residue (v.adicCompletionIntegers F)).toMonoidHom) (w i))
    have h2 : Units.map (IsLocalRing.residue (v.adicCompletionIntegers F)).toMonoidHom (w i) = d i := Units.ext (hw i)
    rw [h2] at h1
    exact h1
  let D : GL (Fin n) (v.adicCompletion F) :=
    ⟨diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F)),
      diagonal (fun i => (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)),
      by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩
  refine ⟨D, fun x => ?_, fun M => ?_⟩
  · change _ ↔ ∀ b, (diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F)) *ᵥ x) b ∈ _
    simp only [mulVec_diagonal]
    refine ⟨fun h b => mul_mem (he b) (h b), fun h b => ?_⟩
    have := mul_mem (he' b) (h b)
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  · change redM F v (diagonal (fun i => (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * M *
      diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F))) = _
    ext a b
    have key : (diagonal (fun i => (((e i)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * M *
        diagonal (fun i => ((e i : (v.adicCompletion F)ˣ) : v.adicCompletion F))) a b =
        ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b) * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      simp only [diagonal_mul, mul_diagonal]
    simp only [diagonal_mul, mul_diagonal, redM]
    by_cases hM : M a b ∈ v.adicCompletionIntegers F
    · have hP : ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b) * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
        mul_mem (mul_mem (he' a) hM) (he b)
      rw [dite_eq_left (key ▸ hP), dite_eq_left hM, ← hw' a, ← hw b, ← map_mul, ← map_mul]
      congr 1
    · have hP : ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b) * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∉ v.adicCompletionIntegers F := by
        intro hP
        apply hM
        have := mul_mem (mul_mem (he a) hP) (he' b)
        have e1 : ((e a : (v.adicCompletion F)ˣ) : v.adicCompletion F) * ((((e a)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) * M a b * ((e b : (v.adicCompletion F)ˣ) : v.adicCompletion F)) * (((e b)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = M a b := by
          simp [mul_assoc]
        rwa [e1] at this
      rw [dite_eq_right (key ▸ hP), dite_eq_right hM]; simp

end GlobalTheory.St.G.Match

namespace GlobalTheory.St.G.Match

theorem nat_prime_not_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hpv : (p : 𝓞 F) ∈ v.asIdeal) : (q : 𝓞 F) ∉ v.asIdeal := by
  intro hqv
  have hc : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hc
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : (a : 𝓞 F) * (p : 𝓞 F) + (b : 𝓞 F) * (q : 𝓞 F) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 F) hab
    push_cast at this; exact this
  rw [← h1]
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hpv) (v.asIdeal.mul_mem_left _ hqv)

end GlobalTheory.St.G.Match

namespace GlobalTheory.St.G

theorem gmatch_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f t k a sk fc : ℕ) (gp : Fin 2 → ℕ) (S : StepLevel F E cm.sig J T f {v : HeightOneSpectrum (𝓞 F) | (gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal}) (G : GLoc F E cm.sig gp) (Gl : GLev S G a t 0 sk fc false), k = n → a = n → sk = n → fc = n → T.Prime → (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → (∀ i, T ≠ gp i) → (∀ i, SplitsIn E (gp i)) → ∀ (Fr : AdFrame cm.sig J (hat F S.Lb) (gp 0 * gp 1) k) (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (hv : (gp i : 𝓞 F) ∈ v.asIdeal), ∃ κ ∈ levelVL cm.sig J v S.Lb, ∀ y ∈ levelVL cm.sig J v S.Lb, (Fr.LocK S.Lb v y ↔ κ⁻¹ * y * κ ∈ S.Uloc v) ∧ (Fr.LocK S.Lb v y → Fr.locChi v y = (lamJ (G.psi0 i v hv) (G.chiB i v hv) a t 0 sk (redM F v (G.mat i v hv (Gl.fr i v hv) (κ⁻¹ * y * κ))))⁻¹) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f t k a sk fc gp S G Gl hk ha hsk hfc hT hgp hne hTg hspl Fr i v hv
  subst a sk fc
  have hTv : (T : 𝓞 F) ∉ v.asIdeal := fun h =>
    GlobalTheory.St.G.Match.nat_prime_not_mem v (gp i) T (hgp i) hT (fun e => hTg i e.symm) hv h
  have hTL := GlobalTheory.St.G.stepLevel_tLat F E n cm.sig J T f _ S
  have hSD := GlobalTheory.T.isLocallySelfDual_of_hermitianLatticeOfLevel F E cm n J hJ hdet T f S.Lb hTL v hTv
  have hLat : IsLat S.Lb := ⟨S.Lb_fin, S.Lb_span⟩
  obtain ⟨fr', ψ', hψ', hfr', hK⟩ := GlobalTheory.T.adelicLatticeFrame_local_basis_unitriangular F E cm n J hJ hdet k t gp G S.Lb Fr hk hgp hne hspl hLat i v hv hSD
  have hcard := ((GlobalTheory.T.cmField_splitCompletely_place_structure F E cm (gp i) (hgp i) (hspl i)).2 v hv).1
  haveI : Finite (kv F v) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (hgp i).ne_zero)
  obtain ⟨d, hd⟩ := GlobalTheory.T.diagonal_torus_transitive_generic_characters (kv F v) n t (G.psi0 i v hv) ψ' (G.chiB i v hv) (fun _ => 1) (G.psi_zero_nontrivial_character i v hv) hψ'
  obtain ⟨D, hDint, hDred⟩ := GlobalTheory.St.G.Match.diag_lift F v n d
  obtain ⟨κ, hκ, -⟩ := (GlobalTheory.T.split_place_lattice_components F E cm n J hJ hdet v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv)).2.1
    (fr' * D * (Gl.fr i v hv)⁻¹)
  have hphi : bc (G.phi i v hv) κ.1 = fr' * D * (Gl.fr i v hv)⁻¹ := hκ
  have hlev : κ.1 ∈ levelVL cm.sig J v S.Lb := by
    refine GlobalTheory.T.mem_level_of_preserves_first_components_split F E cm n J v (G.sp i v hv) (G.sp_sig i v hv) (G.sp_alg i v hv) S.Lb hSD κ.1 κ.2 ?_
    intro x
    refine (Gl.fr_lat i v hv x).trans ?_
    refine Iff.trans ?_ (hfr' _).symm
    rw [hDint]
    rw [hκ]
    simp only [Units.val_mul, mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine ⟨κ.1, hlev, fun y hy => ?_⟩
  have hyκ : κ.1⁻¹ * y * κ.1 ∈ levelVL cm.sig J v S.Lb := mul_mem (mul_mem (inv_mem hlev) hy) hlev
  have hg : (Gl.fr i v hv)⁻¹ * bc (G.phi i v hv) (κ.1⁻¹ * y * κ.1) * Gl.fr i v hv
      = D⁻¹ * (fr'⁻¹ * bc (G.phi i v hv) y * fr') * D := by
    rw [map_mul, map_mul, map_inv, hphi]; group
  have hred : redM F v (G.mat i v hv (Gl.fr i v hv) (κ.1⁻¹ * y * κ.1)) =
      diagonal (fun j => ((d j)⁻¹ : (kv F v)ˣ).1) * redM F v (G.mat i v hv fr' y) * diagonal (fun j => ((d j : (kv F v)ˣ) : kv F v)) := by
    rw [← hDred]
    unfold GLoc.mat
    rw [hg, Units.val_mul, Units.val_mul]
  obtain ⟨hK1, hK2⟩ := hK y hy
  refine ⟨?_, fun hy' => ?_⟩
  · rw [hK1, (hd _).1, ← hred, Gl.mem i v hv _ hyκ]
  · rw [hK2 hy', (hd _).2, hred]

end GlobalTheory.St.G
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem lint_Afun_compact_le : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u ∈ DD σ w, AEStronglyMeasurable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) (μG.restrict K) ∧ ∫⁻ x in K, (‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide v hv ξ K hK
  classical
  have hStd' := hStd
  have hSide' := hSide
  obtain ⟨-, hrep, -, -, hHaar, hSchur, -, hDecay, -⟩ := hStd'
  obtain ⟨hz, hT, hπ, hμS, -⟩ := hSide'
  obtain ⟨hclG, -, -, hclS, -⟩ := GlobalTheory.SgInf.closedSub_groups k r z hz hT
  have hUni : IsUnimod (Sset k r z) μS := ((GlobalTheory.SgInf.unimodular_S_N_UW k r z hz hT μS).1) hμS
  obtain ⟨ν, hν⟩ := exists_isQuotMeas_Sset k r z μG μS hz hT hHaar hμS
  obtain ⟨C₀, hC₀, hC⟩ := GlobalTheory.T.lintegral_compact_le_quotientMeasure_bessel k r (Sset k r z) μG μS ν K hclS hHaar hμS hUni hν hK
  have hstab : ∀ g ∈ GG k r, ∀ x ∈ DD σ w, σ g x ∈ DD σ w :=
    (GlobalTheory.SgInfDD.DD_stable_dense k r σ w hrep).1
  have hD1 := fun u (hu : u ∈ DD σ w) => GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide
    (DD σ w : Set H) (fun g hg x hx => hstab g hg x hx) hDecay u hu v hv
  have hPi := (GlobalTheory.SgInf.PiUnitary.piS_unitary k r z c π hz hT hπ).2.1
  have hD3 := fun u (hu : u ∈ DD σ w) =>
    GlobalTheory.T.norm_identity_besselCoefficient_quotient k r σ w a μG d z c π μS hStd hSide ν hν u hu u hu v hv ξ
  set ψ := psiGen k r z c with hψ
  set bc : ℂ := ⟪ξ, be ψ π μS σ v v ξ⟫_ℂ with hbc
  refine ⟨C₀.toReal * bc.re / d, fun u hu => ?_⟩
  set A : Mt k r → Wp := fun x => Afun ψ π μS σ u v ξ (Matrix.of x) with hA
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  set GM : Set (Mt k r) := {x | Matrix.of x ∈ GG k r} with hGM
  have hGMc : IsClosed GM := hclG.2.1.preimage hof
  have hAc : ContinuousOn A GM := by
    have h1 : ContinuousOn (fun x : Mat k r => Afun ψ π μS σ u v ξ x) (GG k r) :=
      (hD1 u hu).2.2.2.clm_apply continuousOn_const
    exact h1.comp hof.continuousOn (fun x hx => hx)
  have hae : ∀ᵐ x ∂μG, x ∈ GM := by
    rw [ae_iff]; exact hHaar.2.2.1
  refine ⟨?_, ?_⟩
  · have h1 : AEStronglyMeasurable A (μG.restrict GM) :=
      hAc.aestronglyMeasurable hGMc.measurableSet
    rw [Measure.restrict_eq_self_of_ae_mem hae] at h1
    exact h1.restrict
  set F : Mt k r → ENNReal := GM.indicator (fun x => (‖A x‖₊ : ENNReal) ^ 2) with hF
  have hFm : Measurable F := by
    have h1 : ContinuousOn (fun x => (‖A x‖₊ : ENNReal) ^ 2) GM := by
      have h0 : ContinuousOn (fun x => (‖A x‖₊ : ENNReal)) GM :=
        (ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn hAc
      exact (ENNReal.continuous_pow 2).comp_continuousOn h0
    have h2 := ContinuousOn.measurable_piecewise h1
      (continuousOn_const (c := (0 : ENNReal)) (s := GMᶜ)) hGMc.measurableSet
    have h3 : F = GM.piecewise (fun x => (‖A x‖₊ : ENNReal) ^ 2) (fun _ => 0) := by
      funext x
      by_cases hx : x ∈ GM <;> simp [hF, hx]
    rw [h3]; exact h2
  have hFinv : ∀ s ∈ Sset k r z, ∀ x, F (lmulM s x) = F x := by
    intro s hs x
    have hsG : s ∈ GG k r := hclS.1 hs
    have hmem : lmulM s x ∈ GM ↔ x ∈ GM := by
      constructor
      · intro h
        have h1 : s⁻¹ * (s * (Matrix.of x : Mat k r)) ∈ GG k r :=
          hclG.2.2.2.1 _ (hclG.2.2.2.2 _ hsG) _ h
        have h2 : s⁻¹ * (s * (Matrix.of x : Mat k r)) = Matrix.of x := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_GG hsG), Matrix.one_mul]
        rw [h2] at h1; exact h1
      · intro h; exact hclG.2.2.2.1 _ hsG _ h
    by_cases hx : x ∈ GM
    · have hx' := hmem.2 hx
      rw [hF, Set.indicator_of_mem hx', Set.indicator_of_mem hx]
      have hAeq : A (lmulM s x) = PiS ψ π s (A x) := by
        show be ψ π μS σ (σ (s * Matrix.of x) u) v ξ =
          PiS ψ π s (be ψ π μS σ (σ (Matrix.of x) u) v ξ)
        have hm : σ (s * Matrix.of x) = (σ s).comp (σ (Matrix.of x)) := hrep.1.2 s hsG _ hx
        have hxu : σ (Matrix.of x) u ∈ DD σ w := hstab _ hx u hu
        have he := ((hD1 _ hxu).2.1 s hs).1
        rw [hm]
        show be ψ π μS σ (σ s (σ (Matrix.of x) u)) v ξ = _
        rw [he]; rfl
      have hn : ‖PiS ψ π s (A x)‖₊ = ‖A x‖₊ := Subtype.ext (hPi.2.1 s hs _)
      rw [hAeq, hn]
    · have hx' : lmulM s x ∉ GM := fun h => hx (hmem.1 h)
      rw [hF, Set.indicator_of_notMem hx', Set.indicator_of_notMem hx]
  obtain ⟨-, -, hL2, hnorm, hb0, hbim⟩ := hD3 u hu
  have hint : Integrable (fun x => ‖A x‖ ^ 2) ν := hL2.integrable_norm_pow (by norm_num)
  have hval : ∫ x, ‖A x‖ ^ 2 ∂ν = ‖u‖ ^ 2 * bc.re / d := by
    have h1 : ∫ x, ⟪A x, A x⟫_ℂ ∂ν = ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h2 : bc = (bc.re : ℂ) := by
      apply Complex.ext <;> simp [hbim]
    have h3 : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have h4 : ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) = ((‖u‖ ^ 2 * bc.re / d : ℝ) : ℂ) := by
      rw [← h1]
      refine hnorm.trans ?_
      rw [h3]
      push_cast
      rw [← h2]
    exact_mod_cast h4
  have hlin : ∫⁻ x, (‖A x‖₊ : ENNReal) ^ 2 ∂ν = ENNReal.ofReal (‖u‖ ^ 2 * bc.re / d) := by
    rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ← enorm_eq_nnnorm, ofReal_norm_eq_enorm]
  calc ∫⁻ x in K, (‖A x‖₊ : ENNReal) ^ 2 ∂μG = ∫⁻ x in K, F x ∂μG := by
        refine lintegral_congr_ae (ae_restrict_of_ae ?_)
        filter_upwards [hae] with x hx
        rw [hF, Set.indicator_of_mem hx]
    _ ≤ C₀ * ∫⁻ x, F x ∂ν := hC F hFm hFinv
    _ ≤ C₀ * ∫⁻ x, (‖A x‖₊ : ENNReal) ^ 2 ∂ν := by
        refine mul_le_mul_right ?_ _
        exact lintegral_mono fun x => Set.indicator_le_self _ _ x
    _ = ENNReal.ofReal (C₀.toReal * bc.re / d * ‖u‖ ^ 2) := by
        rw [hlin]
        have hC₁ : C₀ = ENNReal.ofReal C₀.toReal := (ENNReal.ofReal_toReal hC₀.ne).symm
        conv_lhs => rw [hC₁]
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        congr 1; ring

end GlobalTheory.SgInf
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.ProjLine

theorem mul_mem_GG_iff {k r : ℕ} {s x : Mat k r} (hs : s ∈ GG k r) : s * x ∈ GG k r ↔ x ∈ GG k r := by
  simp only [GG, UH, Set.mem_setOf_eq] at hs ⊢
  have e : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * (sᴴ * Hpk k r * s) * x := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hs]

theorem Sset_subset_GG {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) : Sset k r z ⊆ GG k r := by
  rintro s ⟨h, hh, m, hm, rfl⟩
  exact (mul_mem_GG_iff hh.1).2 hm.1

theorem isClosed_GG (k r : ℕ) : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} := by
  have hc : Continuous fun x : Mat k r => xᴴ * Hpk k r * x :=
    ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq (X := Mt k r) hc continuous_const

theorem rankOneInnerOperator_self_apply {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (x y : Wp) :
    rk1 y x x = ((‖x‖ ^ 2 : ℝ) : ℂ) • y := by
  rw [rankOneInnerOperator_apply, inner_self_eq_norm_sq_to_K]; push_cast; rfl

theorem inner_rankOneInnerOperator_self {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (x : Wp) :
    ⟪x, rk1 x x x⟫_ℂ = (((‖x‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [rankOneInnerOperator_self_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]
  have e : ((‖x‖ : ℝ) : ℂ) = (RCLike.ofReal ‖x‖ : ℂ) := rfl
  push_cast
  rw [← e]; ring

theorem ae_mem_GG {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {μG μS ν : Measure (Mt k r)}
    (hG : IsHaarOn (GG k r) μG) (hS : IsHaarOn (Sset k r z) μS) (hq : IsQuotMeas μG μS ν) :
    ∀ᵐ x ∂ν, (Matrix.of x : Mat k r) ∈ GG k r := by
  set B : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∉ GG k r} with hBdef
  have hB : MeasurableSet B := (isClosed_GG k r).measurableSet.compl
  have h0 := hq (B.indicator 1) (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hG.2.2.1] at h0
  have hc : μS Set.univ ≠ 0 := by
    intro h; exact hS.2.1 (Measure.measure_univ_eq_zero.1 h)
  have hle : ∀ x, B.indicator (fun _ => μS Set.univ) x ≤
      ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x : Mat k r) i j) ∂μS := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      calc μS Set.univ = ∫⁻ _, 1 ∂μS := (lintegral_one).symm
        _ ≤ _ := by
          apply lintegral_mono_ae
          have hnull : ∀ᵐ s ∂μS, (Matrix.of s : Mat k r) ∈ Sset k r z := by
            rw [ae_iff]; simpa using hS.2.2.1
          filter_upwards [hnull] with s hs
          have hmem : (fun i j => (Matrix.of s * Matrix.of x : Mat k r) i j) ∈ B := by
            show ¬ ((Matrix.of s * Matrix.of x : Mat k r) ∈ GG k r)
            intro h; exact hx ((mul_mem_GG_iff (Sset_subset_GG z hs)).1 h)
          rw [Set.indicator_of_mem hmem]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  have hmul : μS Set.univ * ν B = 0 := by
    rw [← lintegral_indicator_const hB]
    exact le_antisymm ((lintegral_mono hle).trans h0.symm.le) (zero_le)
  have hνB : ν B = 0 := (mul_eq_zero.1 hmul).resolve_left hc
  rw [ae_iff]; simpa [hBdef] using hνB

theorem projector_line : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ w) l → (∀ u ∈ DD σ w, l2SG ν (fun x => l (σ x u)) = ENNReal.ofReal (‖u‖ ^ 2 / d)) ∧ (∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ x ∈ GG k r, Afun (psiGen k r z c) π μS σ w v ξ x = ⟪l v, ξ⟫_ℂ • l (σ x w)) ∧ ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, rconv μG (eFun μG σ w) W y = ((d : ℂ) * ∫ g, ⟪l (σ (Matrix.of g) w), W (Matrix.of g)⟫_ℂ ∂ν) • l (σ y w) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hq l hl
  have hG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hU : IsURepOn (GG k r) σ := hStd.2.1
  have hd : 0 < d := hStd.2.2.2.2.2.1.1
  have hS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  have hae := ae_mem_GG hG hS hq
  have hstab := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hU).1
  obtain ⟨_, ⟨v0, hv0, hlv0⟩, hbe⟩ := hl
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨_, _, hmem, heq, _, _⟩ :=
      GlobalTheory.T.norm_identity_besselCoefficient_quotient k r σ w a μG d z c π μS hStd hSide ν hq u hu u hu v0 hv0 (l v0)
    set A : Mt k r → Wp := fun x => Afun (psiGen k r z c) π μS σ u v0 (l v0) (Matrix.of x) with hAdef
    set L : Mt k r → Wp := fun x => l (σ (Matrix.of x) u) with hLdef
    set N : ℝ := ‖l v0‖ ^ 2 with hNdef
    have hN : 0 < N := by positivity
    have hAL : ∀ᵐ x ∂ν, A x = (N : ℂ) • L x := by
      filter_upwards [hae] with x hx
      simp only [hAdef, hLdef, Afun]
      rw [hbe _ (hstab _ hx _ hu) _ hv0, rankOneInnerOperator_apply, inner_self_eq_norm_sq_to_K]
      simp [hNdef]
    have hnA : ∀ᵐ x ∂ν, ‖A x‖ ^ 2 = N ^ 2 * ‖L x‖ ^ 2 := by
      filter_upwards [hAL] with x hx
      rw [hx, norm_smul, Complex.norm_real, Real.norm_of_nonneg hN.le, mul_pow]
    have hIA : Integrable (fun x => ‖A x‖ ^ 2) ν := hmem.integrable_norm_pow two_ne_zero
    have hIL : Integrable (fun x => ‖L x‖ ^ 2) ν := by
      have : (fun x => ‖L x‖ ^ 2) =ᵐ[ν] fun x => (N ^ 2)⁻¹ * ‖A x‖ ^ 2 := by
        filter_upwards [hnA] with x hx
        rw [hx, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
      exact (hIA.const_mul _).congr this.symm
    have hbevv : ⟪l v0, be (psiGen k r z c) π μS σ v0 v0 (l v0)⟫_ℂ = ((N ^ 2 : ℝ) : ℂ) := by
      rw [hbe _ hv0 _ hv0, inner_rankOneInnerOperator_self]
    have hintA : ∫ x, ‖A x‖ ^ 2 ∂ν = N ^ 2 * (‖u‖ ^ 2 / d) := by
      have h1 : ∫ x, ⟪A x, A x⟫_ℂ ∂ν = ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [inner_self_eq_norm_sq_to_K]; push_cast; rfl
      have h2 := heq
      rw [hbevv, inner_self_eq_norm_sq_to_K u] at h2
      have h3 : ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) = ((N ^ 2 * (‖u‖ ^ 2 / d) : ℝ) : ℂ) := by
        rw [← h1]; refine h2.trans ?_
        have e : ((‖u‖ : ℝ) : ℂ) = (RCLike.ofReal ‖u‖ : ℂ) := rfl
        push_cast
        rw [← e]; ring
      exact_mod_cast h3
    have hintL : ∫ x, ‖L x‖ ^ 2 ∂ν = ‖u‖ ^ 2 / d := by
      have : ∫ x, ‖A x‖ ^ 2 ∂ν = N ^ 2 * ∫ x, ‖L x‖ ^ 2 ∂ν := by
        rw [← integral_const_mul]; exact integral_congr_ae hnA
      rw [this] at hintA
      exact mul_left_cancel₀ (by positivity) hintA
    unfold l2SG
    rw [← hintL, ofReal_integral_eq_lintegral_ofReal hIL (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  · intro v hv ξ x hx
    simp only [Afun]
    rw [hbe _ (mem_DD σ w hx) _ hv, rankOneInnerOperator_apply]
  · intro W hW1 hW2 hEq hL2 y hy
    obtain ⟨_, hconv⟩ := GlobalTheory.T.bessel_functional_standard_side k r σ w a μG d z c π μS hStd hSide ν hq W hW1 hW2 hEq hL2 y hy
    rw [hconv]
    have h : ∀ᵐ g ∂ν, be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g)) =
        ⟪l (σ (Matrix.of g) w), W (Matrix.of g)⟫_ℂ • l (σ y w) := by
      filter_upwards [hae] with g hg
      rw [hbe _ (mem_DD σ w hy) _ (mem_DD σ w hg), rankOneInnerOperator_apply]
    rw [integral_congr_ae h, integral_smul_const, smul_smul]

end GlobalTheory.SgInf.ProjLine
end
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.lowestKType_compressionFormula_of_strictLowestKType : FormulaGap := by
  first | exact @GlobalTheory.Jet.FormGapFree.formulaGap | exact GlobalTheory.Jet.FormGapFree.formulaGap | (intros; apply GlobalTheory.Jet.FormGapFree.formulaGap <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem mu0Tie_of_colsTiedSym : ∀ (D : D7), Formalism.L2.Forms.ColsTiedSym D → ∀ u : D.what₂.Word, StandardLattice.Mu0Tie D u :=
  fun _ C u => Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u

end GlobalTheory
end

section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx NumberField

namespace GlobalTheory

theorem prim_rows_surjective : ∀ (D : D7) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → ∀ (Zs : DefSub A3.fam3.amb3) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs)), (R.toCx3 F).zs = Zs → HEq ((R.toCx3 F).data F.cr true) S1 → Function.Surjective ((A3.side3 F.P1 F.ψ1 Zs).Pq A3.A.μ0).mulVec ∧ Function.Surjective (S1.ι A3.A.μ0).mulVec := by
  intro D _ G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hsep hW hP Zs S1 hz hS
  subst hz
  have hS' := eq_of_heq hS
  subst hS'
  have hR := complex_data_conditions_base_level_of_primitive_links hok hsep hW hP
  exact ⟨(hR.wf true).Pq_surj _, (CxData.rowMat_bij _ _ true (hR.what₂ true).1 (hR.ratMu true) _).2⟩

end GlobalTheory
end
