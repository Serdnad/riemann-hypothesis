module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle310
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle311
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle312
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle313
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle314
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle011
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle014
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizedLatticeEqOfAdelicMatricesAgreeAtPlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointDecorationAgreeBelow
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicDatum_rational_translates_vs_classes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ i (hi : i + 1 ≤ D.R.m) c c' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)), ∀ γ' ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (i + 1) hi), ∀ (κ : ((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.U) (κ' : ((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.U), x.1 = ratA D.host.F γ * ((St i (Nat.le_of_succ_le hi)).y c).1 * κ.1 → x'.1 = ratA D.host.F γ' * ((St (i + 1) hi).y c').1 * κ'.1 → (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap) = 1 → ∀ z, muT (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K ((St i (Nat.le_of_succ_le hi)).chOf c)).lev.chi κ : ℂˣ) : ℂ) * Xi i hi ((St i (Nat.le_of_succ_le hi)).chOf c) ((St (i + 1) hi).chOf c') x x' z = muT (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K ((St (i + 1) hi).chOf c')).lev.chi κ' : ℂˣ) : ℂ) * (t.rd u μ).Xi i c c' (seamHom t.seam (Matrix.toLin' (star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) γ')).toLinearMap)) ∘ₗ z ∘ₗ Matrix.toLin' (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi))).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) γ)).toLinearMap)))) := by
  first | exact @GlobalTheory.TwV.adelicDatum_at_translates | exact GlobalTheory.TwV.adelicDatum_at_translates | (intros; apply GlobalTheory.TwV.adelicDatum_at_translates <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ Xi muT, AdLawAt A dtU a Xi muT → ∀ k < D.R.m, ∀ i (hi : i ≤ D.R.m) c (x : UA D i hi), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), ∀ (κ : ((St i hi).K ((St i hi).chOf c)).lev.U), x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 → muT (k + 1) (Matrix.GeneralLinearGroup.det x.1) = muT (k + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) * (((t.O u μ).mt (k + 1) ((t.O u μ).dt i c) : ℂˣ) : ℂ) * muT (k + 1) (Matrix.GeneralLinearGroup.det κ.1) ∧ muT (k + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) ≠ 0 ∧ muT (k + 1) (Matrix.GeneralLinearGroup.det κ.1) ≠ 0) := by
  first | exact @GlobalTheory.TwV.mu_det_rat_y_lev | exact GlobalTheory.TwV.mu_det_rat_y_lev | (intros; apply GlobalTheory.TwV.mu_det_rat_y_lev <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.intAt_qOf_pow_mul_y0_of_adTie : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ} (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdTie A dtU a → ∀ (β : (St (t.m2 + 1) (cpl_lt t μ).le).Ch) (x : UA D (t.m2 + 1) (cpl_lt t μ).le) (Q : SB t μ) (l : Fin (D.R.N (t.m2 + 1))), IntAt Q.1 ((qOf Q.1 : t.X.E) ^ (if Q.1 ∈ t.Pr.vGs then 1 else (t.cst μ).M) * A.y0 β Q l) := by
  first | exact @GlobalTheory.TwU.baseCosetRepresentative_bounded_at_bad_primes | exact GlobalTheory.TwU.baseCosetRepresentative_bounded_at_bad_primes | (intros; apply GlobalTheory.TwU.baseCosetRepresentative_bounded_at_bad_primes <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.chartFrames_congruent_one_of_same_badPlace_components : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : SB t μ, (frsF t.sel (t.tup μ) p₁ P).trans (frsF t.sel (t.tup μ) p P).symm ∈ GLint t.X.E (D.R.N j) P.1 ∧
    ∀ w ∈ stdAt t.X.E (D.R.N j) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ •
      ((frsF t.sel (t.tup μ) p P).symm (frsF t.sel (t.tup μ) p₁ P w) - w) ∈ stdAt t.X.E (D.R.N j) P.1) := by
  first | exact @GlobalTheory.FrameAgree.frame_away | exact GlobalTheory.FrameAgree.frame_away | (intros; apply GlobalTheory.FrameAgree.frame_away <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.matrixStepDatum_equivariant_rational_unitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i + 1 ≤ D.R.m), i < t.m2 → ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) p p',
      IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      ∀ (g : UF t.X.E (D.R.N i)) (g' : UF t.X.E (D.R.N (i + 1))) (w : HomE t.X.E (D.R.N i) (D.R.N (i + 1))),
      xiPt A i hi β β' (((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)
        (((g', 1, 1) : UF t.X.E (D.R.N (i + 1)) × GLG (E := t.X.E) (n := D.R.N (i + 1)) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N (i + 1)) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p')
        (g'.1.toLinearMap ∘ₗ w ∘ₗ g.1.symm.toLinearMap) = xiPt A i hi β β' p p' w) := by
  first | exact @GlobalTheory.RatEntry.xiPt_rat | exact GlobalTheory.RatEntry.xiPt_rat | (intros; apply GlobalTheory.RatEntry.xiPt_rat <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.adelicFiniteDatum_integralOffBadPrimes : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → ∀ i hi β β' x x' z, IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z)) := by
  first | exact @GlobalTheory.TwV.xiAd_intOff | exact GlobalTheory.TwV.xiAd_intOff | (intros; apply GlobalTheory.TwV.xiAd_intOff <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.kernelChainCharacters_algebraic_unitaryPoints : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), (((t.O u μ).mt (i + 1) (dtU y) : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar) := by
  first | exact @GlobalTheory.TieAlgValues.mt_mem_Qbar | exact GlobalTheory.TieAlgValues.mt_mem_Qbar | (intros; apply GlobalTheory.TieAlgValues.mt_mem_Qbar <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem funMoved_ptAd_rat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ i (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (γ : GL (Fin (D.R.N i)) D.host.E),
      γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi) → x₁.1 = ratA D.host.F γ * x.1 →
      ∀ g : UF t.X.E (D.R.N i), seamGL t.seam g.1 = A.crd i hi * γ * (A.crd i hi)⁻¹ →
      ∀ p, IsPtAd A a i hi β x p → ∀ (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal),
        IsOver v (seamP t.seam P.1) →
        FunMoved t.seam ((St i hi).K β).lev P v h (iotaOf A i hi β P v h) (ratA D.host.F (A.crd i hi) * x₁.1) ((((g, 1, 1) : UF t.X.E (D.R.N i) × GLG (E := t.X.E) (n := D.R.N i) (SG := t.Pr.vGs) × GLQ t.X.E (D.R.N i) (QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K))) • p)).deco.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β x x₁ γ hγ hx g hg p hp P v h hv
  have H := funMoved_ratA_act t.seam _ P v h _ _ _ g.1 1 (hp.fnl P v h hv)
  have e : ratA D.host.F (A.crd i hi) * x₁.1 = ratA D.host.F (seamGL t.seam g.1) * (ratA D.host.F (A.crd i hi) * x.1) := by
    rw [hx, hg, map_mul, map_mul, map_inv]; group
  rw [e]
  exact H

end GlobalTheory.TwV
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjCarry

theorem mem_hatL_latAd_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E))
    (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (u : Fin N → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    u ∈ Formalism.L2.Herm.hatL (F := F) (latAd x Lb) ↔
      ((x⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _) *ᵥ u ∈ Formalism.L2.Herm.hatL (F := F) Lb := by
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds F E (Fin N) Lb hfin hspan x u
  have hlat : latAd x Lb = Formalism.UG.CS.globLat x Lb := Submodule.span_eq (Formalism.UG.CS.globLat x Lb)
  rw [hlat]
  exact hrec

theorem carries_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}
    (C y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (M : Submodule (𝓞 E) (Fin N → E))
    (hfin : Module.Finite (𝓞 E) M) (hspan : Submodule.span E (M : Set (Fin N → E)) = ⊤) :
    Formalism.L2.Herm.Carries (F := F) (C * y * C⁻¹) (latAd C M) (latAd (C * y) M) := by
  intro x
  rw [mem_hatL_latAd_iff (C * y) M hfin hspan, mem_hatL_latAd_iff C M hfin hspan, Matrix.mulVec_mulVec, ← Units.val_mul]
  have e : C⁻¹ * (C * y * C⁻¹)⁻¹ = (C * y)⁻¹ := by group
  rw [e]

theorem cT_map_incl {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {N : ℕ}
    (σ : E →ₐ[F] E) (M : Matrix (Fin N) (Fin N) E) :
    cT (sigR σ R) (M.map (inclE (F := F) R)) = (cT (σ : E →+* E) M).map (inclE (F := F) R) := by
  ext a b
  simp [cT, sigR, inclE]

end GlobalTheory.ConjCarry

namespace GlobalTheory.ConjCarry

theorem conj_mem_std {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E)
    (hco : cT (σ : E →+* E) co.1 * co.1 = J) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ratA F co * y * (ratA F co)⁻¹ ∈ UPts σ (1 : Matrix (Fin N) (Fin N) E) (FiniteAdeleRing (𝓞 F) F) := by
  set R := FiniteAdeleRing (𝓞 F) F
  set s := sigR σ R
  set Cm : Matrix (Fin N) (Fin N) (E ⊗[F] R) := ((ratA F co : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) with hCm
  set Ci : Matrix (Fin N) (Fin N) (E ⊗[F] R) := (((ratA F co)⁻¹ : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) with hCi
  set Y : Matrix (Fin N) (Fin N) (E ⊗[F] R) := (y : Matrix (Fin N) (Fin N) (E ⊗[F] R)) with hY
  have hCm' : Cm = co.1.map (inclE (F := F) R) := rfl
  have hJ : cT s Cm * Cm = J.map (inclE (F := F) R) := by
    rw [hCm', cT_map_incl, ← Matrix.map_mul, hco]
  have hy' : cT s Y * J.map (inclE (F := F) R) * Y = J.map (inclE (F := F) R) := hy
  have hCC : Cm * Ci = 1 := by
    rw [hCm, hCi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  show cT s ((ratA F co * y * (ratA F co)⁻¹ : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) *
      (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) R) * ((ratA F co * y * (ratA F co)⁻¹ : GL (Fin N) (E ⊗[F] R)) : Matrix (Fin N) (Fin N) (E ⊗[F] R)) =
      (1 : Matrix (Fin N) (Fin N) E).map (inclE (F := F) R)
  rw [h1, Units.val_mul, Units.val_mul, ← hCm, ← hCi, ← hY, Matrix.mul_one, cT_mul, cT_mul]
  calc cT s Ci * (cT s Y * cT s Cm) * (Cm * Y * Ci)
      = cT s Ci * (cT s Y * (cT s Cm * Cm) * Y) * Ci := by simp only [Matrix.mul_assoc]
    _ = cT s Ci * (cT s Cm * Cm) * Ci := by rw [hJ, hy']
    _ = cT s (Cm * Ci) * (Cm * Ci) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hCC, cT_one, Matrix.one_mul]

end GlobalTheory.ConjCarry

namespace GlobalTheory.ConjCarry

theorem exists_stdUnitaryPoint_det_eq_unitaryPoint_det {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (co : GL (Fin N) E)
    (hco : cT (σ : E →+* E) co.1 * co.1 = J) (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    ∃ d : GL (Fin 1) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), d ∈ UPts σ (1 : Matrix (Fin 1) (Fin 1) E) (FiniteAdeleRing (𝓞 F) F) ∧
      Matrix.GeneralLinearGroup.det d = Matrix.GeneralLinearGroup.det y := by
  set R := FiniteAdeleRing (𝓞 F) F
  set s := sigR σ R
  set u := Matrix.GeneralLinearGroup.det y with hu
  refine ⟨Units.map (Matrix.scalar (Fin 1) : E ⊗[F] R →+* Matrix (Fin 1) (Fin 1) (E ⊗[F] R)).toMonoidHom u, ?_, ?_⟩
  ·
    have hy' : cT s (y : Matrix (Fin N) (Fin N) (E ⊗[F] R)) * J.map (inclE (F := F) R) * (y : Matrix (Fin N) (Fin N) (E ⊗[F] R)) =
        J.map (inclE (F := F) R) := hy
    have hdet := congrArg Matrix.det hy'
    rw [Matrix.det_mul, Matrix.det_mul] at hdet
    have hcT : ∀ M : Matrix (Fin N) (Fin N) (E ⊗[F] R), (cT s M).det = s M.det := by
      intro M
      unfold cT
      rw [Matrix.det_transpose, RingHom.map_det]
      rfl
    have hJu : IsUnit (J.map (inclE (F := F) R)).det := by
      show IsUnit ((inclE (F := F) R).mapMatrix J).det
      rw [← RingHom.map_det]
      refine IsUnit.map _ ?_
      have hco' : IsUnit (co : Matrix (Fin N) (Fin N) E).det := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
      rw [← hco, Matrix.det_mul]
      refine IsUnit.mul ?_ hco'
      unfold cT
      rw [Matrix.det_transpose]
      show IsUnit (((σ : E →+* E)).mapMatrix (co : Matrix (Fin N) (Fin N) E)).det
      rw [← RingHom.map_det]
      exact hco'.map _
    rw [hcT] at hdet
    have hn : s (u : E ⊗[F] R) * (u : E ⊗[F] R) = 1 := by
      have h2 : (s (u : E ⊗[F] R) * (u : E ⊗[F] R)) * (J.map (inclE (F := F) R)).det = 1 * (J.map (inclE (F := F) R)).det := by
        calc (s (u : E ⊗[F] R) * (u : E ⊗[F] R)) * (J.map (inclE (F := F) R)).det
            = s (u : E ⊗[F] R) * (J.map (inclE (F := F) R)).det * (u : E ⊗[F] R) := by ring
          _ = (J.map (inclE (F := F) R)).det := by rw [hu, Matrix.GeneralLinearGroup.val_det_apply]; exact hdet
          _ = 1 * (J.map (inclE (F := F) R)).det := (one_mul _).symm
      exact hJu.mul_right_cancel h2
    have h1 : (1 : Matrix (Fin 1) (Fin 1) E).map (inclE (F := F) R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    show cT s _ * (1 : Matrix (Fin 1) (Fin 1) E).map (inclE (F := F) R) * _ = (1 : Matrix (Fin 1) (Fin 1) E).map (inclE (F := F) R)
    rw [h1, Matrix.mul_one]
    ext a b
    fin_cases a; fin_cases b
    simp [cT, Matrix.mul_apply, hn]
  · ext
    simp [Matrix.GeneralLinearGroup.det, Matrix.det_fin_one]

theorem det_conj {R : Type} [CommRing R] {N : ℕ} (C y : GL (Fin N) R) :
    Matrix.GeneralLinearGroup.det (C * y * C⁻¹) = Matrix.GeneralLinearGroup.det y := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

end GlobalTheory.ConjCarry

namespace GlobalTheory.TwV


open GlobalTheory.ConjCarry in
theorem conj_crd_unitary_carries : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) β (y : UA D i hi), ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹ ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N i) ∧ Formalism.L2.Herm.Carries (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹) (latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb) (latCo D.sp (gramN D i hi) (A.crd i hi) a y.1 ((St i hi).K β).lev.Lb) ∧ ∃ d : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det d.1 = Matrix.GeneralLinearGroup.det y.1 ∧ Formalism.L2.Herm.IsDetOf D.sp.cm d (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β y
  have hco := hPins.crd_orth i hi
  have hLbf := ((St i hi).K β).lev.Lb_fin
  have hLbs := ((St i hi).K β).lev.Lb_span
  obtain ⟨e1, hCf, hCs⟩ := GlobalTheory.T.companion_lattice_eq_point_lattice_over_companion D i hi (A.crd i hi) hco a 1 _ hLbf hLbs
  have e2 := (GlobalTheory.T.companion_lattice_eq_point_lattice_over_companion D i hi (A.crd i hi) hco a y _ hLbf hLbs).1
  have e1' : latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb =
      latAd (ratA D.host.F (A.crd i hi)) (compan (sp := D.sp) (gramN D i hi) a ((St i hi).K β).lev.Lb) := by
    have := e1
    simp only [OneMemClass.coe_one, mul_one] at this
    exact this
  refine ⟨conj_mem_std (sigD D) (gramN D i hi) (A.crd i hi) hco y.1 y.2, ?_, ?_⟩
  · rw [e1', e2]
    exact carries_conj _ _ _ hCf hCs
  · obtain ⟨d, hd, hdd⟩ := exists_stdUnitaryPoint_det_eq_unitaryPoint_det (sigD D) (gramN D i hi) (A.crd i hi) hco y.1 y.2
    refine ⟨⟨d, hd⟩, hdd, ?_⟩
    exact hdd.trans (GlobalTheory.ConjCarry.det_conj (ratA D.host.F (A.crd i hi)) y.1).symm

end GlobalTheory.TwV
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)

theorem _root_.GlobalTheory.T.localizedLattice_eq_of_adelic_matrices_agree_at_place : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    p₁.deco.1.at P.1 = p.deco.1.at P.1 := by
  first | exact @GlobalTheory.LatAway.decoAt_eq | exact GlobalTheory.LatAway.decoAt_eq | (intros; apply GlobalTheory.LatAway.decoAt_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

theorem _root_.GlobalTheory.T.muCharacter_det_level_eq_local_tame_product : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    MuLaw t u μ dtU → ∀ i, i < D.R.m → ∀ j (hj : j ≤ D.R.m) (β : (St j hj).Ch) (κ : ((St j hj).K β).lev.U) (e : SB t μ → t.X.E),
      (∀ P : SB t μ, IntAtA (F := D.host.F) (seamP t.seam P.1)
        (iA D.host.F D.host.E ((qOf (seamP t.seam P.1) : D.host.E))⁻¹ *
          ((((Matrix.GeneralLinearGroup.det κ.1)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
            iA D.host.F D.host.E (t.seam.iE (e P)) - 1))) →
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) i P (e P)) = 1 ∧
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) = t.seam.σ₀ (∏ P, rhoT t.Ch t.sel (t.tup μ) i P (e P))) := by
  first | exact @GlobalTheory.LevMuDet.muOf_det_lev | exact GlobalTheory.LevMuDet.muOf_det_lev | (intros; apply GlobalTheory.LevMuDet.muOf_det_lev <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.point_decoration_agree_below : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := by
  first | exact @GlobalTheory.TwV.AwayLat.lat_eq | exact GlobalTheory.TwV.AwayLat.lat_eq | (intros; apply GlobalTheory.TwV.AwayLat.lat_eq <;> assumption)
end
