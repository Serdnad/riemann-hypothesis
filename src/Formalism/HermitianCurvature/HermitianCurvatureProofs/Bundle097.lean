module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.StatementD
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle081
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting

@[expose] public section

section

namespace Formalism.FourierDecayAlt.P.PBJ

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

section rw

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rw_vanish_GV {O : Set (Mat k r)} (hO : IsOpen O) {f : Mat k r → E}
    (h : ∀ g ∈ O, g ∈ GV k r → f g = 0) :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ g ∈ O, g ∈ GV k r → Rw w f g = 0
  | [], _ => h
  | X :: w, hw => by
    intro g hg hgG
    have ih := rw_vanish_GV hO h w (fun Y hY => hw Y (List.mem_cons_of_mem _ hY))
    have hX : inLie k r X := hw X List.mem_cons_self
    show RdV X (Rw w f) g = 0
    unfold RdV
    have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
      (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
    have h0 : (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) 0 ∈ O := by
      simp only; rw [Formalism.FourierDecayAlt.P.B5.curve_zero]; exact hg
    have hev : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ O :=
      hc.continuousAt.preimage_mem_nhds (hO.mem_nhds h0)
    have e : (fun t : ℝ => Rw w f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => 0 := by
      filter_upwards [hev] with t ht
      exact ih _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)
    rw [e.deriv_eq]; simp

end rw

section op

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem opApply_eq_zero (Θ : DiffOp k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r)
    (h : ∀ T ∈ Θ, Rw T.word F g = 0) : opApply Θ F g = 0 := by
  unfold opApply
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hx
  rw [h T hT, map_zero]

theorem ckOn_opApply_list (UU : Set (Mat k r)) (F : Mat k r → (Wq →L[ℂ] Wp))
    (hF : CkOn ⊤ (GV k r) F) (hs : closure {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ UU) :
    ∀ Θ : DiffOp k r Wp Wq, (∀ T ∈ Θ, CkOn ⊤ UU T.coef) →
      (∀ T ∈ Θ, closure {g | g ∈ GV k r ∧ Rw T.word F g ≠ 0} ⊆ UU) → CkOn ⊤ (GV k r) (opApply Θ F)
  | [], _, _ => by
    have e : opApply ([] : DiffOp k r Wp Wq) F = fun _ => 0 := by funext g; simp [opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, hc, hsu => by
    have e : opApply (T :: Θ) F = fun g => T.coef g (Rw T.word F g) + opApply Θ F g := by
      funext g; simp [opApply]
    rw [e]
    refine Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add ?_ (ckOn_opApply_list UU F hF hs Θ (fun T' hT' => hc T' (List.mem_cons_of_mem _ hT'))
      (fun T' hT' => hsu T' (List.mem_cons_of_mem _ hT')))
    exact Formalism.FourierDecayAlt.P.B5.ckOn_coef (hc T List.mem_cons_self)
      (Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top hF T.word_lie) (hsu T List.mem_cons_self)

end op

end Formalism.FourierDecayAlt.P.PBJ

namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem theta_compact_support : Formalism.FourierDecayAlt.KB.ThetaCpt := by
  intro Wp Wq _ _ _ _ _ _ P p F w e Cb hDD hF hw
  obtain ⟨nf, fib, o, κ, Dop, _, hIn, _, _, hΘeq⟩ := hDD w hw e
  obtain ⟨hFs, ⟨R, hR⟩, ε, hε, hεF⟩ := hF
  have hGc : Continuous (Gf P.k P.r p.T.base.z p.T.base.z') := Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _

  have hv1 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat P.k P.r | Gf P.k P.r p.T.base.z p.T.base.z' g < ε}, g ∈ GV P.k P.r →
      Rw T.word F g = 0 := fun T _ =>
    PBJ.rw_vanish_GV (isOpen_lt hGc continuous_const)
      (fun g hg hgG => by by_contra hne; exact absurd (hεF g hgG hne) (not_le.2 hg)) T.word T.word_lie
  have hv2 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat P.k P.r | R < gN g}, g ∈ GV P.k P.r → Rw T.word F g = 0 := fun T _ =>
    PBJ.rw_vanish_GV (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous)
      (fun g hg hgG => by by_contra hne; exact absurd (hR g hgG hne) (not_le.2 hg)) T.word T.word_lie
  have hcl : IsClosed {g : Mat P.k P.r | g ∈ GV P.k P.r ∧ ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g} :=
    Formalism.FourierDecayAlt.P.B5.GV_closed.inter (isClosed_le continuous_const hGc)
  have hsub : {g : Mat P.k P.r | g ∈ GV P.k P.r ∧ ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g} ⊆
      C6.domL p.T.base ∅ := fun g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2, by simp⟩
  have hsF : closure {g | g ∈ GV P.k P.r ∧ F g ≠ 0} ⊆ C6.domL p.T.base ∅ := by
    refine subset_trans (closure_minimal ?_ hcl) hsub
    intro g hg; exact ⟨hg.1, hεF g hg.1 hg.2⟩
  have hsT : ∀ T ∈ Dop, closure {g | g ∈ GV P.k P.r ∧ Rw T.word F g ≠ 0} ⊆ C6.domL p.T.base ∅ := by
    intro T hT
    refine subset_trans (closure_minimal ?_ hcl) hsub
    intro g hg
    refine ⟨hg.1, ?_⟩
    by_contra hlt
    exact hg.2 (hv1 T hT g (not_le.1 hlt) hg.1)
  refine ⟨opApply Dop F, ⟨?_, ⟨R, ?_⟩, ε, hε, ?_⟩, fun g hg => hΘeq F g hg, ?_⟩
  · exact PBJ.ckOn_opApply_list _ F hFs hsF Dop (fun T hT => (hIn.1 T hT).1) hsT
  · intro g hgG hne
    by_contra hlt
    exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv2 T hT g (not_le.1 hlt) hgG)
  · intro g hgG hne
    by_contra hlt
    exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g (not_le.1 hlt) hgG)
  · intro a
    show D.vecV p.T.base p.ν' p.m₀ _ a = D.vecV p.T.base p.ν' p.m₀ _ a
    unfold D.vecV
    split_ifs with h1 h2
    · have hγ := h2.choose_spec
      have hG : 0 < Gf P.k P.r p.T.base.z p.T.base.z' h2.choose := by
        rw [← Formalism.FourierDecayAlt.P.ptG_spec _ _ _ _ a _ h1.1 hγ.2.1]; exact h1.2
      rw [Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae p.T.base h2.choose _ (p.Θ.Θ w e F) (opApply Dop F) 1 ?_, one_smul]
      filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS p.T.base] with q hq
      rw [one_smul]
      simp only [D.orbIntegrand, rho]
      rw [hΘeq F _ ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem p.T.base hq hγ.1,
        by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs p.T.base hq]; exact hG, by simp⟩]
    · rfl
    · rfl

end Formalism.FourierDecayAlt.P
end

section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

open Formalism.FourierDecayAlt.P.PBJ

section lev0

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem ptG_one (TT : ℝ) (ζ : ℂ) : D.ptG TT 0 [(1, ζ)] = Complex.normSq ζ - TT := by
  simp [D.ptG, D.ptMatN, D.ptEntry, Matrix.det_fin_one]

theorem isLocPt_one {ζ : ℂ} (hζ : ζ ≠ 0) : D.IsLocPt [(1, ζ)] (0 + 1) := by
  refine ⟨?_, ?_⟩
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact ⟨le_refl _, hζ⟩
  · simp [D.ptSize]

theorem orbJ_one_eq (S : B.RealPlaceData k ρ Wp Wq) {γ : B.Mat k ρ} (hγ : γ ∈ B.GV k ρ)
    (hpos : 0 < Gf k ρ S.z S.z' γ) {d : Fin (ρ + 1) → ℂ} (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k ρ S.z S.z' γ = C2.monoP 1 d) (F : B.Mat k ρ → (Wq →L[ℂ] Wp)) :
    D.orbJ S γ (D.muR S γ 1) F = B.JF S F γ := by
  have : IsEmpty (C2.Lstidx (1 : Equiv.Perm (Fin (ρ + 1)))) := ⟨fun q => by
    obtain ⟨⟨a, b⟩, h1, h2⟩ := q
    simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, id] at h2
    exact absurd h1 (not_lt.2 h2.le)⟩
  have hone : D.rhoOfU S γ 1 = 1 := by
    unfold D.rhoOfU
    split_ifs with hex
    · have h1mem : (1 : B.Mat k ρ) ∈ C6.Rset γ := by
        refine ⟨WeylGroupFacts.mem_n_one, ?_⟩
        rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ)]
        exact WeylGroupFacts.mem_n_one
      exact Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj S hγ hpos hd hZ hex.choose_spec.1 h1mem
        (hex.choose_spec.2.trans (Formalism.FourierDecayAlt.P.Dx2.Rad.uMap_one S.z ⟨S.z_mem, S.T_pos⟩).symm)
    · rfl
  have hlow : C2.lowOf (fun q : C2.Lstidx (1 : Equiv.Perm (Fin (ρ + 1))) => q.1) isEmptyElim = 1 := by
    unfold C2.lowOf
    ext i j
    simp
  have hR : D.muR S γ 1 = Measure.dirac (Matrix.of.symm (1 : B.Mat k ρ)) := by
    unfold D.muR
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty _ isEmptyElim, Measure.map_dirac' Subsingleton.measurable,
      hlow, Matrix.conjTranspose_one, hone]
  have hact : ∀ p, C6.actR γ 1 p = p := by
    intro p
    unfold C6.actR
    rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_G hγ), Matrix.one_mul,
      Matrix.one_mul]
    rfl
  have hθ : ∀ θ, D.IsNormCut S γ (D.muR S γ 1) θ → ∀ p, S.inSS p → θ p = 1 := by
    intro θ hθ p hp
    have h := hθ.2.2 p hp
    rw [hR, integral_dirac] at h
    change θ (C6.actR γ (1 : B.Mat k ρ) p) = 1 at h
    rw [hact p] at h
    exact h
  unfold D.orbJ
  split_ifs with hex
  · have h1 := hθ _ hex.choose_spec.1
    calc ∫ p, hex.choose p • D.orbIntegrand S γ F p ∂S.μSS = ∫ p, D.orbIntegrand S γ F p ∂S.μSS := by
          refine integral_congr_ae ?_
          filter_upwards [Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_inSS S] with p hp
          rw [h1 p hp, one_smul]
      _ = B.Jtau S (1, 1) F γ := rfl
      _ = B.JF S F γ := Formalism.FourierDecayAlt.P.bessel_function_trivial_index k ρ Wp Wq S F γ
  · have hni : ¬ Integrable (fun p => D.orbIntegrand S γ F p) S.μSS := by
      intro hI
      apply hex
      refine ⟨fun _ => 1, ⟨measurable_const, fun _ => zero_le_one, fun p _ => ?_⟩, by simpa using hI⟩
      rw [hR, integral_dirac]
    rw [← Formalism.FourierDecayAlt.P.bessel_function_trivial_index k ρ Wp Wq S F γ]
    exact (integral_undef hni).symm

theorem vector_level_zero_eq_jacquet (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (ν : Fin (2 * ρ + k + 1) → ℂ) (m : B.Mat k ρ)
    (hb : D.IsBaseFrame B0 ν m) (Φ : B.Mat k ρ → (Wq →L[ℂ] Wp)) (ζ : ℂ)
    (hζ : Tz k ρ B0.z * Tz k ρ B0.z' < Complex.normSq ζ) (γ0 : B.Mat k ρ) (hγ0 : γ0 ∈ B.GV k ρ)
    (hZ : Zhat k ρ B0.z B0.z' γ0 = D.ptMatN [(1, ζ)] (ρ + 1)) (hD : D.IsDFrame B0 ν m γ0) :
    D.vecV B0 ν m Φ [(1, ζ)] = B.JF B0 Φ γ0 := by
  subst hρ
  have hTT : 0 < Tz k 0 B0.z * Tz k 0 B0.z' := mul_pos B0.T_pos B0.T'_pos
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, Complex.normSq_zero] at hζ; linarith
  have hloc := isLocPt_one hζ0
  have hG : 0 < D.ptG (Tz k 0 B0.z * Tz k 0 B0.z') 0 [(1, ζ)] := by rw [ptG_one]; linarith
  rw [Formalism.FourierDecayAlt.P.isotropic_vectors_linear_indep k 0 Wp Wq B0 ν m Φ [(1, ζ)] hloc γ0 hb hG hγ0 hZ hD]
  have hw : (hloc.2 ▸ D.ptPerm [(1, ζ)] : Equiv.Perm (Fin (0 + 1))) = 1 := by
    refine Equiv.ext fun a => Fin.ext ?_
    have h1 := a.isLt
    have h2 := ((hloc.2 ▸ D.ptPerm [(1, ζ)] : Equiv.Perm (Fin (0 + 1))) a).isLt
    simp only [Equiv.Perm.coe_one, id]
    omega
  obtain ⟨hmono, hnz⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' [(1, ζ)] (0 + 1) hloc.2 hloc.1
  rw [hw] at hmono
  have hpos : 0 < Gf k 0 B0.z B0.z' γ0 := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec k 0 _ _ [(1, ζ)] γ0 hloc hZ]; exact hG
  rw [hw]
  exact orbJ_one_eq B0 hγ0 hpos hnz (hZ.trans hmono) Φ

theorem vector_level_zero_degenerate (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (ν : Fin (2 * ρ + k + 1) → ℂ) (m : B.Mat k ρ)
    (Φ : B.Mat k ρ → (Wq →L[ℂ] Wp)) (ζ : ℂ) (hζ : Complex.normSq ζ ≤ Tz k ρ B0.z * Tz k ρ B0.z') :
    D.vecV B0 ν m Φ [(1, ζ)] = 0 := by
  subst hρ
  unfold D.vecV
  rw [dite_eq_right]
  rintro ⟨_, h⟩
  rw [ptG_one] at h
  linarith

theorem exists_frame_level_zero (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (ν : Fin (2 * ρ + k + 1) → ℂ) (m : B.Mat k ρ)
    (hb : D.IsBaseFrame B0 ν m) (ζ : ℂ) (hζ : Tz k ρ B0.z * Tz k ρ B0.z' < Complex.normSq ζ) :
    ∃ γ0 ∈ B.GV k ρ, Zhat k ρ B0.z B0.z' γ0 = D.ptMatN [(1, ζ)] (ρ + 1) ∧ D.IsDFrame B0 ν m γ0 := by
  subst hρ
  have hTT : 0 < Tz k 0 B0.z * Tz k 0 B0.z' := mul_pos B0.T_pos B0.T'_pos
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, Complex.normSq_zero] at hζ; linarith
  have hG : 0 < D.ptG (Tz k 0 B0.z * Tz k 0 B0.z') 0 [(1, ζ)] := by rw [ptG_one]; linarith
  exact Formalism.FourierDecayAlt.P.exists_isotropic_frame k 0 Wp Wq B0 ν m [(1, ζ)] hb (isLocPt_one hζ0) hG

theorem jacquet_integral_level_zero (hρ : ρ = 0) (B0 : B.RealPlaceData k ρ Wp Wq) (hN : B0.μN = D.muN k ρ)
    (Φ : B.Mat k ρ → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ) :
    B.JF B0 Φ γ = ∫ p : Mt k ρ × Mt k ρ, (B0.π (Matrix.of p.1)).comp
      ((Φ ((Matrix.of p.1)⁻¹ * γ * Matrix.of p.2)).comp (B0.π' (Matrix.of p.2)⁻¹)) ∂(B0.μW.prod B0.μW') := by
  subst hρ
  have : SigmaFinite B0.μW := Formalism.FourierDecayAlt.P.Dx2.MN.sigma_of_haar B0.haarW
  have : SigmaFinite B0.μW' := Formalism.FourierDecayAlt.P.Dx2.MN.sigma_of_haar B0.haarW'
  have hN0 : B0.μN = Measure.dirac (Matrix.of.symm (1 : B.Mat k 0)) := hN
  have hmeas : (B0.μW.prod B0.μN).prod (B0.μW'.prod B0.μN) = (B0.μW.prod B0.μW').map
      (fun p : Mt k 0 × Mt k 0 => ((p.1, Matrix.of.symm (1 : B.Mat k 0)), (p.2, Matrix.of.symm (1 : B.Mat k 0)))) := by
    rw [hN0, Measure.prod_dirac, Measure.prod_dirac,
      Measure.map_prod_map (f := fun x : Mt k 0 => (x, Matrix.of.symm (1 : B.Mat k 0)))
        (g := fun x : Mt k 0 => (x, Matrix.of.symm (1 : B.Mat k 0))) _ _ (by fun_prop) (by fun_prop)]
    rfl
  have hemb : MeasurableEmbedding (fun p : Mt k 0 × Mt k 0 =>
      ((p.1, Matrix.of.symm (1 : B.Mat k 0)), (p.2, Matrix.of.symm (1 : B.Mat k 0)))) :=
    (MeasurableEmbedding.id.prodMk_right _).prodMap (MeasurableEmbedding.id.prodMk_right _)
  have hpsi : ∀ (z : Fin (2 * 0 + k + 1) → ℂ) (g : B.Mat k 0), Formalism.QuantumDeterminants.psi k 0 z cStd g = 1 := by
    intro z g; simp [Formalism.QuantumDeterminants.psi, Formalism.QuantumDeterminants.ell]
  unfold B.JF besselJ
  rw [hmeas, hemb.integral_map]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [hpsi, star_one, mul_one, one_smul, Equiv.apply_symm_apply, inv_one]

end lev0

end Formalism.FourierDecayAlt.P.PBM
end
end

section

noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx2.DF
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

section commute

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem inWb_of_zero (hr : r = 0) (v : Fin (2 * r + k + 1) → ℂ) : inWb k r v := by
  subst hr; intro i hi; exfalso; have := i.isLt; omega

theorem prW_perp0 (hr : r = 0) (z v : Fin (2 * r + k + 1) → ℂ) (hvz : herm (Hpk k r) v z = 0) :
    D.prW k r z v = v := by
  rw [prW_eq, Wb_of_inWb (inWb_of_zero hr v), hvz, zero_div, zero_smul, sub_zero]

theorem herm_unit {g : B.Mat k r} (hg : g ∈ UH (Hpk k r)) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g *ᵥ v) w = herm (Hpk k r) v (g⁻¹ *ᵥ w) := by
  have hu := WeylGroupFacts.isUnit_of_uh hg
  conv_lhs => rw [show w = g *ᵥ (g⁻¹ *ᵥ w) by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec]]
  exact herm_m0_mulVec_invariant g hg v _

theorem dframe_commute (S : B.RealPlaceData k r Wp Wq) (hr : r = 0) {ν' : Fin (2 * r + k + 1) → ℂ} {m₀ : B.Mat k r}
    (hbase : D.IsBaseFrame S ν' m₀) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) (hD : D.IsDFrame S ν' m₀ γ)
    (hdet : (Zhat k r S.z S.z' γ).det ≠ 0) {hB : B.Mat k r} (hhB : hB ∈ UWset k r S.z') (hBν : hB *ᵥ ν' = ν') :
    (m₀ * hB * m₀⁻¹) * γ * hB⁻¹ = γ := by
  obtain ⟨hν, hνz, hνν, ⟨hmU, hmfix⟩, hmz⟩ := hbase
  obtain ⟨⟨a1, ha1, h1⟩, ⟨a2, ha2, h2⟩, h3⟩ := hD
  have hz := S.z_mem
  have hz' := S.z'_mem
  have um := WeylGroupFacts.isUnit_of_uh hmU
  have uγ := WeylGroupFacts.isUnit_of_uh hγ
  have uB := WeylGroupFacts.isUnit_of_uh hhB.1
  set ζ := (Zhat k r S.z S.z' γ).det with hζdef
  have hzν : herm (Hpk k r) S.z' ν' = 0 := herm_zν hνz
  have hzz0 : herm (Hpk k r) S.z' S.z' ≠ 0 := by
    rw [herm_self_alt]; have := S.T'_pos; intro h; simp at h; linarith
  have hzz0' : herm (Hpk k r) S.z S.z ≠ 0 := by
    rw [herm_self_alt]; have := S.T_pos; intro h; simp at h; linarith

  have hlast : ∀ b : Fin (r + 1), b = Fin.last r := fun b => Fin.ext (by have := b.isLt; simp only [Fin.val_last]; omega)
  have hfz : ∀ (x : Fin (2 * r + k + 1) → ℂ) (b : Fin (r + 1)), fvec k r x b = x := by
    intro x b; rw [hlast b]; exact fvec_lastI x
  have hadj : ∀ a b : Fin (r + 1), (Zhat k r S.z S.z' γ).adjugate a b = 1 := by
    subst hr; intro a b
    rw [Matrix.adjugate_fin_one]; fin_cases a; fin_cases b; rfl
  have hcofR : D.cofR S γ = γ *ᵥ S.z' := by
    unfold D.cofR; subst hr; simp [hadj, hfz]
  have hcofL : D.cofL S γ = S.z := by
    unfold D.cofL; subst hr; simp [hadj, hfz]
  rw [hcofR, prW_eq, Wb_of_inWb (inWb_of_zero hr _)] at h1
  rw [hcofL, prW_eq, Wb_of_inWb (inWb_of_zero hr _)] at h2

  set c1 := herm (Hpk k r) (γ *ᵥ S.z') S.z / herm (Hpk k r) S.z S.z with hc1
  set c2 := herm (Hpk k r) (γ⁻¹ *ᵥ S.z) S.z' / herm (Hpk k r) S.z' S.z' with hc2
  have hγz' : γ *ᵥ S.z' = c1 • S.z + ((a1 : ℂ) * ζ) • (m₀ *ᵥ ν') := by rw [← h1]; abel
  have hγiz : γ⁻¹ *ᵥ S.z = c2 • S.z' + ((a2 : ℂ) * conj ζ) • ν' := by rw [← h2]; abel
  set μ := Real.sqrt (Tz k r S.z' / Tz k r S.z) with hμdef
  have hμ : 0 < μ := Real.sqrt_pos.2 (div_pos S.T'_pos S.T_pos)
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hmiz : m₀⁻¹ *ᵥ S.z = (μ : ℂ)⁻¹ • S.z' := by
    have : S.z = (μ : ℂ)⁻¹ • (m₀ *ᵥ S.z') := by rw [hmz, smul_smul, inv_mul_cancel₀ hμ', one_smul]
    rw [this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec]
  set σ := m₀⁻¹ * γ with hσdef

  have hσz' : σ *ᵥ S.z' = (c1 * (μ : ℂ)⁻¹) • S.z' + ((a1 : ℂ) * ζ) • ν' := by
    rw [hσdef, ← Matrix.mulVec_mulVec, hγz', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hmiz,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec, smul_smul]
  have ha2ζ : (a2 : ℂ) * conj ζ ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast ha2.ne') ?_
    simpa using hdet
  have hγν : γ *ᵥ ν' = ((a2 : ℂ) * conj ζ)⁻¹ • (S.z - c2 • (γ *ᵥ S.z')) := by
    have e : γ *ᵥ (γ⁻¹ *ᵥ S.z) = S.z := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ uγ, Matrix.one_mulVec]
    rw [hγiz, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at e
    rw [← e]
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ha2ζ, one_smul]
  have hσν : σ *ᵥ ν' = (((a2 : ℂ) * conj ζ)⁻¹ * (μ : ℂ)⁻¹) • S.z' -
      (((a2 : ℂ) * conj ζ)⁻¹ * c2) • (σ *ᵥ S.z') := by
    simp only [hσdef, ← Matrix.mulVec_mulVec]
    rw [hγν, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, hmiz, smul_sub, smul_smul, smul_smul]

  have hfix : ∀ u, herm (Hpk k r) u S.z' = 0 → herm (Hpk k r) u ν' = 0 → σ *ᵥ u = u := by
    intro u hu1 hu2
    have e1 : herm (Hpk k r) (γ *ᵥ u) S.z = 0 := by
      rw [herm_unit hγ, hγiz, B2x4.herm_add_right, B2x4.herm_smul_right, B2x4.herm_smul_right, hu1, hu2]
      simp
    have e2 : herm (Hpk k r) (γ *ᵥ u) (γ *ᵥ S.z') = 0 := by rw [herm_m0_mulVec_invariant γ hγ, hu1]
    have key := h3 (γ *ᵥ u) (fun a => ⟨by rw [hfz]; exact e1, by rw [hfz]; exact e2⟩)
    rw [prW_perp0 hr S.z _ e1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ uγ, Matrix.one_mulVec,
      prW_perp0 hr S.z' u hu1] at key
    rw [hσdef, ← Matrix.mulVec_mulVec, key, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ um, Matrix.one_mulVec]

  have hBz' : hB *ᵥ S.z' = S.z' := hhB.2.2
  have hBperp : ∀ u, herm (Hpk k r) u S.z' = 0 → herm (Hpk k r) u ν' = 0 →
      herm (Hpk k r) (hB *ᵥ u) S.z' = 0 ∧ herm (Hpk k r) (hB *ᵥ u) ν' = 0 := by
    intro u h1u h2u
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← hBz']
      rw [herm_m0_mulVec_invariant hB hhB.1, h1u]
    · conv_lhs => rw [← hBν]
      rw [herm_m0_mulVec_invariant hB hhB.1, h2u]

  have hcomm : σ * hB = hB * σ := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    set α := herm (Hpk k r) v S.z' / herm (Hpk k r) S.z' S.z' with hα
    set β := herm (Hpk k r) v ν' with hβ
    set v0 := v - α • S.z' - β • ν' with hv0
    have hv0z : herm (Hpk k r) v0 S.z' = 0 := by
      rw [hv0, B2x4.herm_sub_left, B2x4.herm_sub_left, B2x4.herm_smul_left, B2x4.herm_smul_left, hνz, hα]
      field_simp; ring
    have hv0ν : herm (Hpk k r) v0 ν' = 0 := by
      rw [hv0, B2x4.herm_sub_left, B2x4.herm_sub_left, B2x4.herm_smul_left, B2x4.herm_smul_left, hzν, hνν, hβ]
      ring
    have hv : v = v0 + α • S.z' + β • ν' := by rw [hv0]; abel
    obtain ⟨hb1, hb2⟩ := hBperp v0 hv0z hv0ν
    rw [← Matrix.mulVec_mulVec v σ hB, ← Matrix.mulVec_mulVec v hB σ, hv]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hBz', hBν, hfix v0 hv0z hv0ν,
      hfix (hB *ᵥ v0) hb1 hb2]
    rw [hσν, hσz']
    simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_smul, hBz', hBν]

  have hγσ : γ = m₀ * σ := by rw [hσdef, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ um, Matrix.one_mul]
  rw [hγσ]
  calc m₀ * hB * m₀⁻¹ * (m₀ * σ) * hB⁻¹ = m₀ * hB * (m₀⁻¹ * m₀) * σ * hB⁻¹ := by simp only [Matrix.mul_assoc]
    _ = m₀ * (σ * hB) * hB⁻¹ := by rw [Matrix.nonsing_inv_mul _ um, hcomm]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = m₀ * σ := by rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ uB, Matrix.mul_one]

end commute

end Formalism.FourierDecayAlt.P.PBI
end
end
