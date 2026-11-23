module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle662
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle539
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle580
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle621
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle682
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle686
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyCompletedLocalizationPrism
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle684
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.KappaFrob

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (g : ↥(GK K)) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → s.κ g * s.F.map (bk.iS.comp C) = s.F.map (bk.iS.comp C) * (s.κ g).map Φ := by
  intro l hl K bk τ hτ d ρ _ s g G Φ hG hΦ
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have h0 : 0 < bk.ρ₀ := NNReal.rpow_pos (zero_lt_one.trans hl1)
  have h1 : bk.ρ₀ < 1 := NNReal.rpow_lt_one_of_one_lt_of_neg hl1
    (neg_lt_zero.2 (one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)))
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  have hi : Function.Injective bk.iA := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk _ bk.ev ι TB bk.ρ₀ h0 h1).1
  obtain ⟨j, hj⟩ := exists_discMap_of_pow_dvd l _ _ bk.ev (X : bk.S) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0
    (by rw [pow_one]) (by rw [pow_one])
  have hu : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (isUnit_toDisc_frobS_E l K bk).map j
    rwa [hj.ext] at h

  have hfτ : WittVector.frobenius τ ≠ 0 := by
    obtain ⟨-, ε, η, ⟨-, hδ1⟩, h⟩ := hτ
    rw [h]
    intro h'
    rw [Units.mul_right_eq_zero, sub_eq_zero] at h'
    have h1' : ε = 1 := by simpa using congrArg (fun w : Ainf l => w.coeff 0) h'
    exact hδ1 (by rw [h1', map_one, map_one])
  have hEτ : bk.ev bk.E * τ ≠ 0 := hτ.1 ▸ hfτ
  have hτ0 : τ ≠ 0 := right_ne_zero_of_mul hEτ
  have hE0 : bk.ev bk.E ≠ 0 := left_ne_zero_of_mul hEτ
  have hσinj : Function.Injective (Per.σA (g : GQ l)) := fun x y hxy => by
    have := congrArg (Per.σA ((g : GQ l)⁻¹)) hxy
    rwa [← GlobalTheory.RingBasics.σA_mul, ← GlobalTheory.RingBasics.σA_mul, inv_mul_cancel, GlobalTheory.RingBasics.σA_one, GlobalTheory.RingBasics.σA_one] at this
  have ha : bk.iA (bk.ev bk.E * τ) ≠ 0 := fun h => hEτ (hi (h.trans (map_zero _).symm))
  have hb : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) ≠ 0 := fun h =>
    hEτ (hσinj ((hi (h.trans (map_zero _).symm)).trans (map_zero _).symm))

  have hcomm : Φ.comp G = G.comp Φ := by
    have e : (WittVector.frobenius : Ainf l →+* Ainf l).comp (Per.σA (g : GQ l)) =
        (Per.σA (g : GQ l)).comp WittVector.frobenius :=
      RingHom.ext fun x => (GlobalTheory.GalPhi.σA_frobenius _ x).symm
    have k1 : IsDiscMap (l := _) (u := _) (ρ := _) ((WittVector.frobenius : Ainf l →+* Ainf l).comp (Per.σA (g : GQ l))) (Φ.comp G) :=
      ⟨fun x => by rw [RingHom.comp_apply, hG.ext, hΦ.ext, RingHom.comp_apply],
        fun x => (hΦ.norm_le _).trans (hG.norm_le _)⟩
    have k2 : IsDiscMap (l := _) (u := _) (ρ := _) ((Per.σA (g : GQ l)).comp WittVector.frobenius) (G.comp Φ) :=
      ⟨fun x => by rw [RingHom.comp_apply, hΦ.ext, hG.ext, RingHom.comp_apply],
        fun x => (hG.norm_le _).trans (hΦ.norm_le _)⟩
    rw [e] at k1
    exact k1.unique k2
  have hΦa : Φ (bk.iA (bk.ev bk.E * τ)) = bk.iS (frobS l bk.a bk.E) * bk.iA (bk.ev bk.E * τ) := by
    rw [hΦ.ext, map_mul, hτ.1, ← bk.ev_frob, map_mul]; rfl
  have hΦb : Φ (bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ))) =
      G (bk.iS (frobS l bk.a bk.E)) * bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) := by
    rw [hΦ.ext, ← GlobalTheory.GalPhi.σA_frobenius, map_mul, hτ.1, ← bk.ev_frob, map_mul, map_mul]
    rw [show bk.iS (frobS l bk.a bk.E) = bk.iA (bk.ev (frobS l bk.a bk.E)) from rfl, hG.ext]

  have hφ : ((l : bk.DA bk.ρ₀) ^ s.c₁) • (s.W * s.X'.map bk.iS).map Φ =
      bk.iS (frobS l bk.a bk.E) ^ s.N • (s.W * s.X'.map bk.iS * s.F.map (bk.iS.comp C)) := s.φ Φ hΦ
  have hgal := s.gal g G hG
  set P := s.W * s.X'.map bk.iS with hP
  set FD := s.F.map (bk.iS.comp C) with hFD'
  set R := (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) with hR'
  set κ := s.κ g with hκ
  set a := bk.iA (bk.ev bk.E * τ) with ha'
  set b := bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) with hb'
  set u := bk.iS (frobS l bk.a bk.E) with hu'
  set L := (l : bk.DA bk.ρ₀) ^ s.c₁ with hL'
  have hMG : ∀ (H : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (c : bk.DA bk.ρ₀) (M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)),
      (c • M).map H = H c • M.map H := fun H c M => Matrix.map_smul' _ _ _ (map_mul H)
  have hR : R.map Φ = R := Matrix.ext fun i j => by
    simp only [hR', Matrix.map_apply, RingHom.comp_apply]
    rw [hΦ.ext, GlobalTheory.GalPhi.frobenius_algebraMap]
  have hFD : FD.map G = FD := Matrix.ext fun i j => by
    simp only [hFD', Matrix.map_apply, RingHom.comp_apply]
    change G (bk.iA (bk.ev (C (s.F i j)))) = bk.iA (bk.ev (C (s.F i j)))
    rw [hG.ext, bk.ev_C, bk.gal_w]
  have hPG : (P.map G).map Φ = (P.map Φ).map G := Matrix.ext fun i j => by
    simp only [Matrix.map_apply]; exact RingHom.congr_fun hcomm _
  have hgalΦ : Φ a ^ s.N • (R * (P.map Φ).map G) = Φ b ^ s.N • (P.map Φ * κ.map Φ) := by
    have h := congrArg (fun M => M.map Φ) hgal
    have e1 : (R * P.map G).map Φ = R.map Φ * (P.map G).map Φ := Matrix.map_mul
    have e2 : (P * κ).map Φ = P.map Φ * κ.map Φ := Matrix.map_mul
    rwa [hMG, hMG, e1, e2, hR, hPG, map_pow, map_pow] at h
  have hL : G L = L := by simp [hL']
  have hA : L • (R * (P.map Φ).map G) = G (u ^ s.N) • (R * P.map G * FD) := by
    rw [← Matrix.mul_smul, ← hL, ← hMG, hφ, hMG, Matrix.map_mul, hFD, Matrix.mul_smul, Matrix.mul_assoc]
  have hB : L • (P.map Φ * κ.map Φ) = u ^ s.N • (P * FD * κ.map Φ) := by
    rw [← Matrix.smul_mul, hφ, Matrix.smul_mul]
  have step1 : (Φ a ^ s.N * G (u ^ s.N)) • (R * P.map G * FD) = (Φ b ^ s.N * u ^ s.N) • (P * FD * κ.map Φ) := by
    calc (Φ a ^ s.N * G (u ^ s.N)) • (R * P.map G * FD) = Φ a ^ s.N • (L • (R * (P.map Φ).map G)) := by
          rw [hA, smul_smul]
      _ = L • (Φ a ^ s.N • (R * (P.map Φ).map G)) := smul_comm _ _ _
      _ = L • (Φ b ^ s.N • (P.map Φ * κ.map Φ)) := by rw [hgalΦ]
      _ = Φ b ^ s.N • (L • (P.map Φ * κ.map Φ)) := smul_comm _ _ _
      _ = _ := by rw [hB, smul_smul]
  have hΦa' : Φ a ^ s.N = u ^ s.N * a ^ s.N := by rw [hΦa, mul_pow]
  have hΦb' : Φ b ^ s.N = G (u ^ s.N) * b ^ s.N := by rw [hΦb, mul_pow, map_pow]
  have key : (u ^ s.N * G (u ^ s.N) * a ^ s.N * b ^ s.N) • (P * κ * FD) =
      (u ^ s.N * G (u ^ s.N) * a ^ s.N * b ^ s.N) • (P * FD * κ.map Φ) := by
    calc (u ^ s.N * G (u ^ s.N) * a ^ s.N * b ^ s.N) • (P * κ * FD)
        = (Φ a ^ s.N * G (u ^ s.N)) • ((b ^ s.N • (P * κ)) * FD) := by
          rw [Matrix.smul_mul, smul_smul, hΦa']; congr 1; ring
      _ = (Φ a ^ s.N * G (u ^ s.N)) • ((a ^ s.N • (R * P.map G)) * FD) := by rw [hgal]
      _ = a ^ s.N • ((Φ a ^ s.N * G (u ^ s.N)) • (R * P.map G * FD)) := by
          rw [Matrix.smul_mul, smul_comm]
      _ = a ^ s.N • ((Φ b ^ s.N * u ^ s.N) • (P * FD * κ.map Φ)) := by rw [step1]
      _ = _ := by rw [smul_smul, hΦb']; congr 1; ring
  have hc : u ^ s.N * G (u ^ s.N) * a ^ s.N * b ^ s.N ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (hu.pow _).ne_zero ((hu.pow _).map G).ne_zero) (pow_ne_zero _ ha))
      (pow_ne_zero _ hb)
  have h3 : P * κ * FD = P * FD * κ.map Φ := Matrix.ext fun i j => by
    have := congrFun (congrFun key i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this

  have hτi : bk.iA τ ≠ 0 := fun h => hτ0 (hi (h.trans (map_zero _).symm))
  have hdW : s.W.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det s.W_mul
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, h, zero_mul] at this
    exact pow_ne_zero _ (pow_ne_zero _ hτi) this.symm
  have hEi : bk.iS bk.E ≠ 0 := fun h => hE0 (hi (h.trans (map_zero _).symm))
  have hl0 : (l : bk.DA bk.ρ₀) ≠ 0 := (isUnit_l_disc l _ _).ne_zero
  have hdX : (s.X'.map bk.iS).det ≠ 0 := by
    intro h
    have := congrArg (fun M => (M.map bk.iS).det) s.X_mul
    rw [Matrix.map_mul, Matrix.det_mul, h, mul_zero, Matrix.map_smul' _ _ _ (map_mul bk.iS), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.det_smul, Matrix.det_one, mul_one, map_mul, map_pow, map_pow, map_natCast] at this
    exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ hEi)) this.symm
  have hdP : P.det ≠ 0 := by rw [hP, Matrix.det_mul]; exact mul_ne_zero hdW hdX
  have h4 : P.det • (κ * FD) = P.det • (FD * κ.map Φ) := by
    have e : ∀ M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), P.det • M = P.adjugate * (P * M) := fun M => by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [e, e, ← Matrix.mul_assoc P, ← Matrix.mul_assoc P, h3]
  exact Matrix.ext fun i j => by
    have := congrFun (congrFun h4 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hdP this

end GlobalTheory.BKLim.KappaFrob
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.SiteCoord

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

theorem comp_assoc {R : Type} [CommRing R] {P₁ P₂ P₃ P₄ : Obj l R} (a : Hom P₃ P₄) (b : Hom P₂ P₃)
    (c : Hom P₁ P₂) : (a.comp b).comp c = a.comp (b.comp c) := Hom.ext' rfl

theorem map_mulVec (S : Strat bk d) {Y Y' : Obj l ↥(OL K)} (k : Hom Y Y') (g₁ g₂ : Hom bk.prism Y)
    (w : Fin d → Y.A) :
    (fun i => k.f ((S.ε g₁ g₂).mulVec w i)) = (S.ε (k.comp g₁) (k.comp g₂)).mulVec fun i => k.f (w i) := by
  funext i
  rw [RingHom.map_mulVec, S.ε_nat]
  rfl

theorem mulVec_map_add {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (M : Matrix (Fin d) (Fin d) A')
    (w w' : Fin d → A) :
    M.mulVec (fun i => φ ((w + w') i)) = M.mulVec (fun i => φ (w i)) + M.mulVec (fun i => φ (w' i)) := by
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp

theorem mulVec_map_smul {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (M : Matrix (Fin d) (Fin d) A')
    (c : A) (w : Fin d → A) : M.mulVec (fun i => φ ((c • w) i)) = φ c • M.mulVec (fun i => φ (w i)) := by
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem coords_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∀ (P : Type) [AddCommGroup P] [Module B.A P] (u : P →ₛₗ[h.f] (Fin d → C.A)), (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i)) → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ v : P →ₛₗ[a.f] (Fin d → Q.A), ∀ (Q' : Obj l ↥(OL K)) (h' : Hom Q Q') (a' : Hom C Q'), a'.comp h = h'.comp a → ∀ x, (fun i => h'.f (v x i)) = (S.ε (h'.comp g) (a'.comp f)).mulVec fun i => a'.f (u x i) := by
  intro l _ K bk d S B C h f hC P _ _ u hu Q a g
  obtain ⟨Q₀, a₀, h₀, hpo⟩ := hC.stable.po Q a
  have hc₀ : Cover h₀ := (GlobalTheory.T.stable_and_cover_prismHom_of_pushout l _ B C Q Q₀ h a a₀ h₀ hpo).2 hC
  obtain ⟨hinj, hsh⟩ := GlobalTheory.T.prism_cover_injective_and_descent l _ Q Q₀ h₀ hc₀
  obtain ⟨D, p, q, hpq⟩ := hc₀.stable.po Q₀ h₀
  have hcf : ∀ b, a₀.f (h.f b) = h₀.f (a.f b) := fun b => congrArg (fun k : Hom B Q₀ => k.f b) hpo.comm
  obtain ⟨z, hzdef⟩ : ∃ z : P → Fin d → Q₀.A,
      z = fun x => (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (u x i) := ⟨_, rfl⟩
  have hpa : (p.comp a₀).comp h = (q.comp a₀).comp h := by
    rw [comp_assoc p a₀ h, comp_assoc q a₀ h, hpo.comm, ← comp_assoc p h₀ a, ← comp_assoc q h₀ a, hpq.comm]
  have hg : p.comp (h₀.comp g) = q.comp (h₀.comp g) := by rw [← comp_assoc p h₀ g, hpq.comm, comp_assoc q h₀ g]
  have key : ∀ x, (fun i => p.f (z x i)) = fun i => q.f (z x i) := by
    intro x
    have e1 := hu D (p.comp a₀) (q.comp a₀) hpa x
    simp only [comp_assoc] at e1
    have e1' : (fun i => p.f (a₀.f (u x i))) = (S.ε (p.comp (a₀.comp f)) (q.comp (a₀.comp f))).mulVec
        fun i => q.f (a₀.f (u x i)) := e1
    have e2 := map_mulVec S p (h₀.comp g) (a₀.comp f) (fun i => a₀.f (u x i))
    have e3 := map_mulVec S q (h₀.comp g) (a₀.comp f) (fun i => a₀.f (u x i))
    have hzx : z x = (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (u x i) := by rw [hzdef]
    calc (fun i => p.f (z x i))
        = fun i => p.f ((S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) i) :=
          congrArg (fun w : Fin d → Q₀.A => fun i => p.f (w i)) hzx
      _ = (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f))).mulVec fun i => p.f (a₀.f (u x i)) := e2
      _ = (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f))).mulVec
            ((S.ε (p.comp (a₀.comp f)) (q.comp (a₀.comp f))).mulVec fun i => q.f (a₀.f (u x i))) :=
          congrArg (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f))).mulVec e1'
      _ = (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f)) * S.ε (p.comp (a₀.comp f)) (q.comp (a₀.comp f))).mulVec
            fun i => q.f (a₀.f (u x i)) := Matrix.mulVec_mulVec _ _ _
      _ = (S.ε (p.comp (h₀.comp g)) (q.comp (a₀.comp f))).mulVec fun i => q.f (a₀.f (u x i)) :=
          congrArg (fun M => Matrix.mulVec M fun i => q.f (a₀.f (u x i))) (S.ε_trans _ _ _)
      _ = (S.ε (q.comp (h₀.comp g)) (q.comp (a₀.comp f))).mulVec fun i => q.f (a₀.f (u x i)) :=
          congrArg (fun k => Matrix.mulVec (S.ε k (q.comp (a₀.comp f))) fun i => q.f (a₀.f (u x i))) hg
      _ = fun i => q.f ((S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) i) := e3.symm
      _ = fun i => q.f (z x i) := (congrArg (fun w : Fin d → Q₀.A => fun i => q.f (w i)) hzx).symm
  have hz : ∀ x i, ∃ y, h₀.f y = z x i := fun x i => by
    obtain ⟨y, hy⟩ := hsh D p q hpq (z x i) (congrFun (key x) i)
    exact ⟨y, hy⟩
  choose y hy using hz
  have hzx : ∀ x, z x = (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (u x i) := fun x => congrFun hzdef x
  have z_add : ∀ x x', z (x + x') = z x + z x' := fun x x' =>
    calc z (x + x') = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u (x + x') i)) := hzx _
      _ = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f ((u x + u x') i)) :=
          congrArg (fun w : Fin d → C.A => (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (w i)) (map_add u x x')
      _ = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) +
            (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x' i)) := mulVec_map_add a₀.f _ _ _
      _ = z x + z x' := congrArg₂ (· + ·) (hzx x).symm (hzx x').symm
  have z_smul : ∀ (b : B.A) x, z (b • x) = h₀.f (a.f b) • z x := fun b x =>
    calc z (b • x) = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u (b • x) i)) := hzx _
      _ = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f ((h.f b • u x) i)) :=
          congrArg (fun w : Fin d → C.A => (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (w i))
            (LinearMap.map_smulₛₗ u b x)
      _ = a₀.f (h.f b) • (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) := mulVec_map_smul a₀.f _ _ _
      _ = h₀.f (a.f b) • z x := congrArg₂ (· • ·) (hcf b) (hzx x).symm
  let v : P →ₛₗ[a.f] (Fin d → Q.A) :=
    { toFun := y
      map_add' := fun x x' => by
        funext i
        apply hinj
        exact calc h₀.f (y (x + x') i) = z (x + x') i := hy _ i
          _ = z x i + z x' i := congrFun (z_add x x') i
          _ = h₀.f (y x i) + h₀.f (y x' i) := congrArg₂ (· + ·) (hy x i).symm (hy x' i).symm
          _ = h₀.f (y x i + y x' i) := (map_add h₀.f _ _).symm
      map_smul' := fun b x => by
        funext i
        apply hinj
        exact calc h₀.f (y (b • x) i) = z (b • x) i := hy _ i
          _ = h₀.f (a.f b) * z x i := congrFun (z_smul b x) i
          _ = h₀.f (a.f b) * h₀.f (y x i) := congrArg (h₀.f (a.f b) * ·) (hy x i).symm
          _ = h₀.f (a.f b * y x i) := (map_mul h₀.f _ _).symm }
  refine ⟨v, ?_⟩
  intro Q' h' a' hcomm x
  have hU := GlobalTheory.T.prismPushoutModAdicPow_universal l _ B C Q Q₀ h a a₀ h₀ hpo Q' a' h' hcomm
  obtain ⟨c, hc, -⟩ := hU
  have e : (fun i => h'.f (v x i)) = fun i => (c.comp h₀).f (y x i) :=
    congrArg (fun k : Hom Q Q' => fun i => k.f (y x i)) hc.2.symm
  have e' : (fun i => (c.comp h₀).f (y x i)) = fun i => c.f (z x i) := by
    funext i
    exact congrArg c.f (hy x i)
  exact calc (fun i => h'.f (v x i)) = fun i => c.f (z x i) := e.trans e'
    _ = fun i => c.f ((S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) i) :=
        congrArg (fun w : Fin d → Q₀.A => fun i => c.f (w i)) (hzx x)
    _ = (S.ε (c.comp (h₀.comp g)) (c.comp (a₀.comp f))).mulVec fun i => c.f (a₀.f (u x i)) :=
        map_mulVec S c _ _ _
    _ = (S.ε ((c.comp h₀).comp g) ((c.comp a₀).comp f)).mulVec fun i => (c.comp a₀).f (u x i) :=
        congrArg₂ (fun k k' => (S.ε k k').mulVec fun i => c.f (a₀.f (u x i)))
          (comp_assoc c h₀ g).symm (comp_assoc c a₀ f).symm
    _ = (S.ε (h'.comp g) (a'.comp f)).mulVec fun i => a'.f (u x i) :=
        congrArg₂ (fun (k : Hom Q Q') (k' : Hom C Q') => (S.ε (k.comp g) (k'.comp f)).mulVec fun i => k'.f (u x i))
          hc.2 hc.1

end GlobalTheory.BSP.SiteCoord
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

theorem mem_nonZeroDivisors_of_associated' {R : Type} [CommRing R] {a b : R} (h : Associated a b)
    (ha : a ∈ nonZeroDivisors R) : b ∈ nonZeroDivisors R := by
  obtain ⟨v, rfl⟩ := h
  exact mul_mem_nonZeroDivisors.mpr ⟨ha, v.isUnit.mem_nonZeroDivisors⟩

theorem mul_cancel_of_rel {R : Type} [CommRing R] {n : Type} [Fintype n] {N : ℕ} {ef eg eh : R}
    (hg : eg ∈ nonZeroDivisors R) (hh : eh ∈ nonZeroDivisors R) {Pf Pg Ph ε₁ ε₂ ε₃ : Matrix n n R}
    (r1 : eg ^ N • (Pf * ε₁) = ef ^ N • Pg) (r2 : eh ^ N • (Pg * ε₂) = eg ^ N • Ph)
    (r3 : eh ^ N • (Pf * ε₃) = ef ^ N • Ph) : Pf * (ε₁ * ε₂) = Pf * ε₃ := by
  have key : (eg ^ N * eh ^ N) • (Pf * (ε₁ * ε₂)) = (eg ^ N * eh ^ N) • (Pf * ε₃) := by
    calc (eg ^ N * eh ^ N) • (Pf * (ε₁ * ε₂))
        = eh ^ N • ((eg ^ N • (Pf * ε₁)) * ε₂) := by
          rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = eh ^ N • ((ef ^ N • Pg) * ε₂) := by rw [r1]
      _ = ef ^ N • (eh ^ N • (Pg * ε₂)) := by
          rw [Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
      _ = ef ^ N • (eg ^ N • Ph) := by rw [r2]
      _ = eg ^ N • (ef ^ N • Ph) := by rw [smul_smul, smul_smul, mul_comm]
      _ = eg ^ N • (eh ^ N • (Pf * ε₃)) := by rw [r3]
      _ = (eg ^ N * eh ^ N) • (Pf * ε₃) := by rw [smul_smul]
  have hc : eg ^ N * eh ^ N ∈ nonZeroDivisors R :=
    mul_mem_nonZeroDivisors.mpr ⟨pow_mem hg _, pow_mem hh _⟩
  ext i j
  have e := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at e
  exact (mul_cancel_left_mem_nonZeroDivisors hc).mp e

theorem rel_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g h : Hom bk.prism B) (ε₁ ε₂ ε₃ : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε₁ → ht.Rel (BK.hf f₀ X) g h ε₂ → ht.Rel (BK.hf f₀ X) f h ε₃ → ε₁ * ε₂ = ε₃ := by
  intro l _ K bk d ρ τ s ht B f₀ h0 f g h ε₁ ε₂ ε₃ h1 h2 h3
  have hn : ∀ k : Hom bk.prism B, ‖toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf k X)‖ ≤ bk.ρ₀ := fun k =>
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ k).1
  have hE : ∀ k : Hom bk.prism B,
      toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf k bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := fun k =>
    mem_nonZeroDivisors_of_associated' ((GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f₀ k).2.1.map (toDisc l (BK.hf f₀ X) bk.ρ₀)) h0
  have mf := isDiscMap_map (BK.hf f) (hn f)
  have mg := isDiscMap_map (BK.hf g) (hn g)
  have mh := isDiscMap_map (BK.hf h) (hn h)
  have hF : Disc.map (BK.hf f) (hn f) (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈
      nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := by
    rw [mf.ext]; exact hE f
  exact GlobalTheory.T.basis_matrix_map_cancel_left l K bk d ρ τ s ht (Disc l (BK.hf f₀ X) bk.ρ₀) _ hF _ _
    (mul_cancel_of_rel (hE g) (hE h) (h1 _ _ mf mg) (h2 _ _ mg mh) (h3 _ _ mf mh))

end GlobalTheory.BSP.Height
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.Height

theorem isDiscMap_comp' {l : ℕ} {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A'']
    {u : A} {u' : A'} {u'' : A''} {ρ ρ' ρ'' : ℝ≥0} {f : A →+* A'} {g : A' →+* A''}
    {F : Disc l u ρ →+* Disc l u' ρ'} {G : Disc l u' ρ' →+* Disc l u'' ρ''}
    (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) (hG : IsDiscMap (l := _) (u := _) (ρ := _) g G) : IsDiscMap (l := _) (u := _) (ρ := _) (g.comp f) (G.comp F) :=
  ⟨fun a => by simp [hF.ext, hG.ext], fun x => (hG.norm_le _).trans (hF.norm_le x)⟩

theorem rel_map : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B B' : Obj l ↥(OL K)) (f₀ f g : Hom bk.prism B) (f₀' : Hom bk.prism B') (k : Hom B B') (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → (∃ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) k.f Fk) ∧ ∀ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) k.f Fk → ht.Rel (BK.hf f₀' X) (k.comp f) (k.comp g) (ε.map Fk) := by
  intro l _ K bk d ρ τ s ht B B' f₀ f g f₀' k ε hrel
  have hk : ‖toDisc l (BK.hf f₀' X) bk.ρ₀ (k.f (BK.hf f₀ X))‖ ≤ bk.ρ₀ :=
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B' f₀' (k.comp f₀)).1
  refine ⟨⟨Disc.map k.f hk, isDiscMap_map k.f hk⟩, ?_⟩
  intro Fk hFk Ff' Fg' hf' hg'
  have hff := (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ f).1
  have hgg := (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀ g).1
  have h := congrArg (fun M => Matrix.map M Fk)
    (hrel _ _ (isDiscMap_map (BK.hf f) hff) (isDiscMap_map (BK.hf g) hgg))
  have e1 : Fk.comp (Disc.map (BK.hf f) hff) = Ff' :=
    (isDiscMap_comp' (isDiscMap_map (BK.hf f) hff) hFk).unique hf'
  have e2 : Fk.comp (Disc.map (BK.hf g) hgg) = Fg' :=
    (isDiscMap_comp' (isDiscMap_map (BK.hf g) hgg) hFk).unique hg'
  subst e1 e2
  ext i j
  have h2 := congrFun (congrFun h i) j

  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, map_mul, map_pow, map_sum, smul_eq_mul,
  hFk.ext, RingHom.comp_apply] at h2 ⊢
  exact h2

end GlobalTheory.BSP.Height
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace GlobalTheory.RecT

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GoodCusp.tw {y : IrrGL (k := k)} (hy : GoodCusp y) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    GoodCusp (y.tw χ hχ) := by
  rcases hy with h1 | ⟨hf, y₀, χ₀, hχ₀, hfix, rfl⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hf, y₀, χ₀ * χ, hχ₀.mul hχ, hfix, IrrGL.tw_tw _ _ _ _ _⟩

theorem Good.tw {x : IrrGL (k := k)} (hx : Good x) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (x.tw χ hχ) := by
  obtain ⟨s, hs, hg⟩ := hx
  refine ⟨s.map (·.tw χ hχ), (hs.tw χ hχ).of_equiv (x.twEquiv χ hχ), ?_⟩
  intro y hy
  obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
  exact (hg y' hy').tw χ hχ

theorem good_tw_iff (x : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Good (x.tw χ hχ) ↔ Good x :=
  ⟨fun h => by simpa only [IrrGL.tw_tw_inv] using h.tw χ⁻¹ hχ.inv, fun h => h.tw χ hχ⟩

theorem good_nu_iff (x : IrrGL (k := k)) (s : ℂ) : Good (x.nu s) ↔ Good x := good_tw_iff x _ _

end GlobalTheory.RecT

end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.nonempty_envRing : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A) (d p : A), J.FG → (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → IsAdicComplete J A → Nonempty (EnvRing D J d p) := by
  first | exact @GlobalTheory.BSP.envRing_exists | exact GlobalTheory.BSP.envRing_exists | (intros; apply GlobalTheory.BSP.envRing_exists <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.nonempty_completedLocalizationPrism : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A), GenAway B f d → Nonempty (LocP B f d) := by
  first | exact @GlobalTheory.BSP.GenAway₂ | exact GlobalTheory.BSP.GenAway₂ | (intros; apply GlobalTheory.BSP.GenAway₂ <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ g : GQ l, ∃ h ∈ GK (ϖ.field a), ∃ k ∈ ϖ.GKinf, g = h * k := by
  first | exact @GlobalTheory.NgalDecomp.galQ_eq_GK_mul_GKinf | exact GlobalTheory.NgalDecomp.galQ_eq_GK_mul_GKinf | (intros; apply GlobalTheory.NgalDecomp.galQ_eq_GK_mul_GKinf <;> assumption)
end
