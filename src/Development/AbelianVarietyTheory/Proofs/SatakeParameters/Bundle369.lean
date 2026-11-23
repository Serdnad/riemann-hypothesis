module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle321
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle349
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle363
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle320
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle354
public import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle356
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle365
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle342
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle327
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle329
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle165
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle299
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle171
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle350
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle341
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle351
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle364
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle007
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section
namespace GlobalTheory.TwV.AwayCpl
theorem frames_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : SB t μ, ∃ k : GLint t.X.E (D.R.N j) P.1, frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k.1 ∧
      ∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ ((t.cst μ).D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp t.X.E (D.R.N j)) l))) := GlobalTheory.T.chartPoints_frames_congr_away_from_badPrimes

theorem levAt_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.Ok → Pr.Ok → ChIdx.Ok Ch sel mu cst L G m2 → ∀ j (b : L.β j) (P : rowSG Pr sel mu) (k : GLint X.E (R.N j) P.1), j ≤ m2 + 1 →
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N j)) l))) →
    GlobalTheory.TopLaw.LevAt (L.levG j b) (L.levQ j b) P k 1 := GlobalTheory.T.congruent_one_mem_step_levels_character_one

theorem rhoS_det_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (i n : ℕ) (P : rowSG Pr sel mu) (k : GLint X.E n P.1),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E n) l))) →
    rhoS Ch sel mu i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 := GlobalTheory.T.tameLocalCharacter_det_congruent_one_eq_one

theorem exists_approx : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (SB : Finset (HeightOneSpectrum (𝓞 E))) (f : SB → (Sp E n ≃ₗ[E] Sp E n)) (y0 : SB → Sp E n) (e : SB → ℕ),
    ∃ y : Sp E n, ∀ P l, IntAt P.1 ((((qOf P.1 : ℕ) : E) ^ (e P))⁻¹ * ((f P).symm y - y0 P) l) := GlobalTheory.T.exists_vector_prescribed_residues_in_frames

theorem psiAt_coset : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    ChIdx.Ok Ch sel mu cst L G m2 → ∀ (al : L.β m2) (P : rowSG Pr sel mu) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (k : GLint X.E (R.N (m2 + 1)) P.1)
    (w w₁ : Sp X.E (R.N (m2 + 1))),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E (R.N (m2 + 1))) l))) →
    SameCoset sel mu cst P (k.1.symm w₁) w →
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w₁ = PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ w := GlobalTheory.T.coupledStep_localDatum_invariant_coset_move

theorem lat_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1) := GlobalTheory.T.adelicPoints_same_badComponents_same_localization

theorem fnl_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 → ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := GlobalTheory.T.chartFunctional_eq_of_agree_badPlaces_allSteps

theorem intAt_sub {E : Type} [Field E] {P : HeightOneSpectrum (𝓞 E)} {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by
  obtain ⟨r₁, s₁, hs₁, e₁⟩ := ha
  obtain ⟨r₂, s₂, hs₂, e₂⟩ := hb
  refine ⟨s₂ * r₁ - s₁ * r₂, s₁ * s₂, fun hm => (P.isPrime.mem_or_mem hm).elim hs₁ hs₂, ?_⟩
  rw [map_sub, map_mul, map_mul, map_mul, ← e₁, ← e₂]
  ring

theorem phiT_data_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 ∧ ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTi j hj β x x₁ p p₁ h h₁ hag P
  have e := lat_away A dtU a hP hTi j hj β x x₁ p p₁ h h₁ hag P
  exact ⟨e, fnl_away A dtU a hP hTi j hj β x x₁ p p₁ h h₁ hag P e⟩


open Classical in
theorem ptAway_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i = t.m2 → PtAway A a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTi i hi hi2
  subst hi2
  intro β β' x x' x₁ x₁' p p' p₁ p₁' h h' h₁ h₁' hag
  have hX := hP.fields.ok
  have hPr := t.pr_ok
  have hL := t.idx_ok μ
  funext z
  unfold xiPt
  simp only [dif_neg (lt_irrefl _), if_pos rfl]
  unfold XiCpl1
  refine congrArg₂ (· * ·) ?_ (Finset.prod_congr rfl fun P _ => ?_)

  · have H := phiT_data_away A dtU a hP hTi t.m2 _ β x x₁ p p₁ h h₁ (fun v hv => (hag v hv).1)
    have H' := phiT_data_away A dtU a hP hTi (t.m2 + 1) hi β' x' x₁' p' p₁' h' h₁' (fun v hv => (hag v hv).2)
    have e : ∀ P : t.Pr.vT (t.word u), (∀ y ∈ (p₁.deco.1).at P.1, z y ∈ (p₁'.deco.1).at P.1 ∧ p₁'.deco.1.f P (z y) = p₁.deco.1.f P y) ↔
        (∀ y ∈ (p.deco.1).at P.1, z y ∈ (p'.deco.1).at P.1 ∧ p'.deco.1.f P (z y) = p.deco.1.f P y) := by
      intro P
      rw [(H P).1, (H' P).1]
      refine forall₂_congr fun y hy => and_congr_right fun hz => ?_
      rw [(H P).2 y hy, (H' P).2 _ hz]
    unfold phiT
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ((forall_congr' e).1 h1) h2
    · exact absurd ((forall_congr' e).2 h2) h1
    · rfl

  · obtain ⟨k, hk, hkc⟩ := frames_away A dtU a hP hTi t.m2 _ β x x₁ p p₁ h h₁ (fun v hv => (hag v hv).1) P
    obtain ⟨k', hk', hkc'⟩ := frames_away A dtU a hP hTi (t.m2 + 1) hi β' x' x₁' p' p₁' h' h₁' (fun v hv => (hag v hv).2) P
    have hne : ∀ q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
        repY (cosetOf A (t.m2 + 1) hi β' q) ∈ cosetOf A (t.m2 + 1) hi β' q := by
      intro q
      obtain ⟨y, hy⟩ := exists_approx t.X.E (D.R.N (t.m2 + 1)) (SB t μ) (frsF t.sel (t.tup μ) q) (y0At A (t.m2 + 1) hi β')
        (fun P => if P.1 ∈ t.Pr.vGs then 0 else (t.cst μ).M)
      exact Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β' q) ⟨y, fun P l => hy P l⟩
    obtain ⟨bL, -⟩ := hL.last_uniq
    have hc1 := hne p₁' P
    have hc0 := hne p' P
    rw [hk'] at hc1
    rw [hk, hk']
    generalize repY (cosetOf A (t.m2 + 1) hi β' p₁') = Y₁ at hc1 ⊢
    generalize repY (cosetOf A (t.m2 + 1) hi β' p') = Y₀ at hc0 ⊢
    generalize frsF t.sel (t.tup μ) p P = f at ⊢
    generalize frsF t.sel (t.tup μ) p' P = f' at hc0 hc1 ⊢
    rw [show (f' * k'.1).symm Y₁ = k'.1.symm (f'.symm Y₁) from rfl] at hc1
    have lawS := GlobalTheory.CoupledLaw.psiAt_source hX hPr hL (al := A.ib t.m2 hi β) (P := P) (κ := k) (a := 1)
      (levAt_one _ _ _ _ _ _ _ _ _ _ _ hX hPr hL t.m2 (A.ib t.m2 hi β) P k (Nat.le_succ _) hkc) (inFr f f' z) (f'.symm Y₁)
    have lawT := GlobalTheory.CoupledLaw.psiAt_target hX hPr hL (b := bL) (P := P) (κ := k') (a := 1)
      (levAt_one _ _ _ _ _ _ _ _ _ _ _ hX hPr hL (t.m2 + 1) bL P k' le_rfl hkc') ((t.idx μ).h t.m2 (A.ib t.m2 hi β) P)
      (k'.1.symm.toLinearMap ∘ₗ (inFr f f' z ∘ₗ k.1.toLinearMap)) (k'.1.symm (f'.symm Y₁))
    have hrS := rhoS_det_one t.X t.Pr D.R t.Ch t.sel t.S (t.tup μ) (t.cst μ) hL.cst_ok t.m2 _ P k hkc
    have hrT := rhoS_det_one t.X t.Pr D.R t.Ch t.sel t.S (t.tup μ) (t.cst μ) hL.cst_ok t.m2 _ P k' hkc'
    have hsc : SameCoset t.sel (t.tup μ) (t.cst μ) P (k'.1.symm (f'.symm Y₁)) (f'.symm Y₀) := fun l => by
      have := intAt_sub (hc1 l) (hc0 l)
      convert this using 1
      simp only [Pi.sub_apply]
      ring
    have hpsi := psiAt_coset _ _ _ _ _ _ _ _ _ _ _ hL (A.ib t.m2 hi β) P (inFr f f' z) k' (f'.symm Y₀) (f'.symm Y₁) hkc' hsc
    have e1 : inFr (f * k.1) (f' * k'.1) z = k'.1.symm.toLinearMap ∘ₗ (inFr f f' z ∘ₗ k.1.toLinearMap) := LinearMap.ext fun v => rfl
    have e2 : (f' * k'.1).symm Y₁ = k'.1.symm (f'.symm Y₁) := rfl
    have e3 : k'.1.toLinearMap ∘ₗ (k'.1.symm.toLinearMap ∘ₗ (inFr f f' z ∘ₗ k.1.toLinearMap)) = inFr f f' z ∘ₗ k.1.toLinearMap :=
      LinearMap.ext fun v => LinearEquiv.apply_symm_apply _ _
    have e4 : k'.1 (k'.1.symm (f'.symm Y₁)) = f'.symm Y₁ := LinearEquiv.apply_symm_apply _ _
    rw [e3, e4, hrT, mul_one, Units.val_one, one_mul] at lawT
    rw [hrS, mul_one, Units.val_one, one_mul] at lawS
    rw [e1, e2, ← lawT, lawS, hpsi]

end GlobalTheory.TwV.AwayCpl
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.latticeTuple_joint_dictionary : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std := by
  first | exact @GlobalTheory.TwV.joint_dict | exact GlobalTheory.TwV.joint_dict | (intros; apply GlobalTheory.TwV.joint_dict <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV.Xc.MoveScal

theorem embLL_mem' (D : D7) (z : D.what₂.LL) : D.what₂.embLL z ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral z).map D.what₂.embLL.toRatAlgHom

theorem embT_mem' (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral x).map (TaylorLogMetric.embT D τ).toRatAlgHom

theorem lamC_mul' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  rw [Formalism.L2.Ker.lamC_of_mem lam (mul_mem hx hy), Formalism.L2.Ker.lamC_of_mem lam hx, Formalism.L2.Ker.lamC_of_mem lam hy, ← map_mul]
  rfl

theorem lamC_ne' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (h0 : x ≠ 0) :
    TaylorLogMetric.lamC lam x ≠ 0 := by
  rw [Formalism.L2.Ker.lamC_of_mem lam hx]
  exact (map_ne_zero lam).2 fun h => h0 (congrArg Subtype.val h)

theorem scal_core {Mp Mg ML Mk χk P x y : ℂ} (e1 e1' e2 n2 : ℤ) (hMg : Mg ≠ 0) (hMk : Mk ≠ 0) (hχ : χk ≠ 0)
    (hP : P ≠ 0) :
    Mp * (Mg * ML * Mk)⁻¹ * (P⁻¹ * x) ^ (-e1) * y ^ e1' * ((P⁻¹ * x) ^ e2 * y ^ (-n2))⁻¹ * (Mk * χk⁻¹) *
        (χk * Mg * P ^ (-(e1 + e2))) =
      Mp * ML⁻¹ * x ^ (-e1) * y ^ e1' * (x ^ e2 * y ^ (-n2))⁻¹ := by
  rw [mul_zpow, mul_zpow, inv_zpow', inv_zpow', neg_neg, zpow_neg P (e1 + e2), zpow_add₀ hP, zpow_neg P e2]
  have hA : P ^ e1 ≠ 0 := zpow_ne_zero _ hP
  have hB : P ^ e2 ≠ 0 := zpow_ne_zero _ hP
  generalize P ^ e1 = A at hA ⊢
  generalize P ^ e2 = B at hB ⊢
  generalize x ^ (-e1) = X1
  generalize x ^ e2 = X2
  generalize y ^ e1' = Y1
  generalize y ^ (-n2) = Y2
  field_simp

end GlobalTheory.TwV.Xc.MoveScal


open GlobalTheory.TwV.Xc.MoveScal in

theorem GlobalTheory.TwV.Xc.moveBy_scal : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; GlobalTheory.TwU.pPow (sysS H X std) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹)) = (kapG (sysS H X std) ℂ_[D.what₂.places.resChar w] j c γ)⁻¹ * (GlobalTheory.TwU.pPow (sysS H X std) j (c, La) La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hSp hPos hPair j hj c La γ g κ hr hLa hMove La' hLa'
  have hγL : ((sysS H X std).Pj j).IsLatTup (((sysS H X std).Lv.lev j c).smul γ La) :=
    (Formalism.MainNotions.FormalGroupSystem.Pf.latTup_smul _ _ γ La).2 hLa
  have hjm : j < (sysS H X std).mm := by rw [(GlobalTheory.TwV.DelB.sysS_ranks S).1]; exact hj
  obtain ⟨hA1, -, -, -, hs1, hf1, -, -⟩ := hPair j hjm (c, La) La' hLa hLa'
  have hker := GlobalTheory.T.kernelLattice_movedLatticeTuple S hD hSp j hj c La γ g κ hr hLa hMove
  obtain ⟨hMgA, hkap⟩ := GlobalTheory.T.eigenvalue_arithmeticElement_at_site S hD hSp hPos j hj c La γ g κ hr hLa hMove (GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hSp j hj La'.1)
  obtain ⟨hgU, hpt, -, r, hr_eq, -⟩ := hMove
  have hE := (GlobalTheory.TwV.Xc.eMat_unitary_det D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) (fun x => rfl) _ _ hr
    (gramN D j hj.le) (J.A.crd j hj.le) (J.pins.crd_orth j hj.le)).2 g hgU
  have hchi := GlobalTheory.ChiMove.chi_detId_smulLat D t.χ t.χ_ok ⟨_, hA1.2.2.1⟩ _ hE.1
  rw [hE.2] at hchi
  have hD1 := (hD j hj.le (c, La) hLa).2.2.2
  have hD2 := (hD j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La) hγL).2.2.2
  have hUL : (J.fd std).dt j (c, La) ∈ U1 (sigD D) := hD1 ▸ det_unitary_adelic_point_gram_step_norm_one D j hj.le _
  have hUk : Matrix.GeneralLinearGroup.det κ.1 ∈ U1 (sigD D) :=
    det_unitary_adelic_point_gram_step_norm_one D j hj.le ⟨κ.1, ((((J.St j hj.le).K _).lev.U_eq κ.1).1 κ.2).1⟩
  have hUγ : (J.fd std).dt j (c, ((sysS H X std).Lv.lev j c).smul γ La) ∈ U1 (sigD D) :=
    hD2 ▸ det_unitary_adelic_point_gram_step_norm_one D j hj.le _
  have hUg : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g) ∈ U1 (sigD D) := by
    have e : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g) =
        (J.fd std).dt j (c, ((sysS H X std).Lv.lev j c).smul γ La) * (Matrix.GeneralLinearGroup.det κ.1)⁻¹ *
          ((J.fd std).dt j (c, La))⁻¹ := by
      rw [hD2, hD1, hpt, map_mul, map_mul, mul_inv_cancel_right, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (mul_mem hUγ (inv_mem hUk)) (inv_mem hUL)

  have hmm := S.law.mu_mul j hj
  have hMdt : S.muT (j + 1) ((J.fd std).dt j (c, (((sysS H X std).Lv.lev j c).smul γ La))) = S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) *
      S.muT (j + 1) ((J.fd std).dt j (c, La)) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) := by
    rw [hD2, hpt, map_mul, map_mul, ← hD1, hmm.2 _ (mul_mem hUg hUL) _ hUk, hmm.2 _ hUg _ hUL]
  have hMg := S.law.mu_ne hj hUg
  have hMk := S.law.mu_ne hj hUk
  have hχ : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hP : (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ≠ 0 := Finset.prod_ne_zero_iff.2 fun τ _ => (map_ne_zero _).2 (Units.ne_zero (Matrix.GeneralLinearGroup.det g))
  have hcore : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) =
      GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹ := by
    simp only [GlobalTheory.TwU.scal0, Base.chiFac]
    rw [hker, hchi, hMdt]
    exact scal_core _ _ _ _ hMg hMk hχ hP
  have hbQ : (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) ∈ TaylorLogMetric.Qbar :=
    mul_mem (mul_mem (hr_eq ▸ embLL_mem' D r) hMgA) (zpow_mem (prod_mem fun τ _ => embT_mem' D τ _) _)
  have hb0 : (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) * S.muT (j + 1) (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F g)) * (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ g.1.det) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) + (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)))) ≠ 0 := mul_ne_zero (mul_ne_zero hχ hMg) (zpow_ne_zero _ hP)
  have hALQ : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, La) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, La)) ((J.fd std).kerN (j + 1) La'))⁻¹ ∈ TaylorLogMetric.Qbar := mul_mem hs1 (inv_mem hf1)
  have hAγQ : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) ∈ TaylorLogMetric.Qbar := by
    rw [← mul_inv_cancel_right₀ hb0 (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * (Base.chiFac t.χ _ _ ((J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La))) ((J.fd std).kerN (j + 1) La'))⁻¹ * (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹)), hcore]
    exact mul_mem hALQ (inv_mem hbQ)
  have hp0 : ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hpp : GlobalTheory.TwU.pPow (sysS H X std) j (c, La) La' = GlobalTheory.TwU.pPow (sysS H X std) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' * ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La)) := by
    unfold GlobalTheory.TwU.pPow
    rw [← zpow_add₀ hp0, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    dsimp only
    ring
  have hq0 : ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (∑ v : (sysS H X std).Pl, (sysS H X std).vm v (j + 1) * (len (sysS H X std) v j (((sysS H X std).Lv.lev j c).smul γ La) - len (sysS H X std) v j La)) ≠ 0 := zpow_ne_zero _ hp0
  have hl0 := lamC_ne' S.lam hbQ hb0
  rw [hkap, hpp, ← hcore, lamC_mul' S.lam hAγQ hbQ]
  field_simp

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwV.Xc.dt_sameAway_step : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v π, IsUnifAt J v π → ∀ j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → ∃ k ∈ U1 (sigD D), k ∈ intU D.host.F D.host.E ∧ OneOff ((A0 J).pl v).1 k ∧ (J.fd std).dt j La = (J.fd std).dt j Lb * π ^ (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2) * k) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS v π hπ j hj La Lb hab
  have hA := hD j hj La hab.1
  have hB := hD j hj Lb hab.2.1
  have pa := GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hS j hj La hab.1
  have pb := GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hS j hj Lb hab.2.1
  have sa := GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hS v j hj La Lb hab
  have hone := J.one
  obtain ⟨hadd, hint, -, -⟩ := GlobalTheory.TwV.Xc.OrdA.ordA_props _ _ _ _ _ (A0 J) hone.int hS.1 v
  set n : ℤ := len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2 with hn
  set k := ((J.fd std).dt j Lb * π ^ n)⁻¹ * (J.fd std).dt j La with hk

  let oh : (AfE D.host.F D.host.E)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (ordA (A0 J) v x)) (fun x y => by simp [hadd x y, ofAdd_add])
  have hoh : ∀ x, ordA (A0 J) v x = Multiplicative.toAdd (oh x) := fun x => rfl
  have hkU : k ∈ U1 (sigD D) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ pb.1 (Subgroup.zpow_mem _ hπ.1 n))) pa.1
  have hkOff : OneOff ((A0 J).pl v).1 k := by
    intro w' hw'
    let f : (AfE D.host.F D.host.E)ˣ →* _ := Units.map (prV (E := D.host.E) w').toMonoidHom
    have hfπ : f π = 1 := Units.ext (hπ.2.1 w' hw')
    have hdet : ∀ x : GL (Fin (D.R.N j)) (AfE D.host.F D.host.E),
        f (Matrix.GeneralLinearGroup.det x) = Matrix.GeneralLinearGroup.det (Formalism.UG.bc (prV (E := D.host.E) w') x) := by
      intro x
      apply Units.ext
      simp [f, Formalism.UG.bc, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    have hfab : f ((J.fd std).dt j La) = f ((J.fd std).dt j Lb) := by
      rw [hA.2.2.2, hB.2.2.2, hdet, hdet, sa.1 w' hw']
    have : f k = 1 := by
      simp only [hk, map_mul, map_inv, map_zpow, hfπ, one_zpow, mul_one, hfab, inv_mul_cancel]
    exact congrArg Units.val this
  have hkOrd : ordA (A0 J) v k = 0 := by
    have hz : ordA (A0 J) v (π ^ n) = n * ordA (A0 J) v π := by
      rw [hoh, hoh, map_zpow, toAdd_zpow, smul_eq_mul]
    have hi : ∀ x, ordA (A0 J) v x⁻¹ = -ordA (A0 J) v x := by
      intro x; rw [hoh, hoh, map_inv, toAdd_inv]
    rw [hk, hadd, hi, hadd, hz, pa.2 v, pb.2 v, hπ.2.2, hn]
    ring
  refine ⟨k, hkU, ?_, hkOff, ?_⟩
  · exact GlobalTheory.TwV.Xc.mem_intU_of_oneOff_ordA _ _ (sigD D) _ _ _ (A0 J) _ hone.good hone.int hS.1 v k hkU hkOff hkOrd
  · rw [hk, mul_inv_cancel_left]
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem tieChiH_of_parts : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]), ∀ j < D.R.m, ∀ (cB : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (cK : ℂ_[D.what₂.places.resChar w]), (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * cB j La * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → TieChiH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι sc (d.sH S ι) cB j cK) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d ι j hj cB sc cK hsc La hLa c' L' hL'
  have hLat := S.Y.Rep_lat j La hLa
  have hsC := GlobalTheory.T.latticeTuplePairScalar_eq_characterProduct S hD d j hj La (c', L') hLat hL'
  have he := GlobalTheory.T.frameFactors_cancel_p_power_of_pair_series _ (sysS H X std) S.E S.hfin S.hst S.g S.hLT D.what₂.Tau (hT.gat_pos u w hg)
    (FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (ltC S.g S.hLT)) j La (c', L')
  have h2 := hsc La (c', L') hLat hL'
  show cK * S.E.iK (S.Y.eS j La * (S.Y.eT j (c', L'))⁻¹) * cB j La * (pPow (sysS H X std) j La (c', L') * ι (d.sC S j La (c', L'))) = _
  rw [hsC]
  have hι : ∀ x y : ℂ, ι (x * y) = ι x * ι y := map_mul ι
  simp only [hι]
  linear_combination (cK * cB j La * ι (d.uS S j La) * ι (d.uT S j (c', L')) *
      ι ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) *
      ι ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) c' L')) : ℂˣ) : ℂ)) * he +
    ι ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) *
      ι ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) c' L')) : ℂˣ) : ℂ) * h2

end GlobalTheory.TwV.DelB
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.TwV.DelA.cmp_valsAt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat (j + 1)).V, ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp (j + 1) x La.1 La.2) = MvPolynomial.map ι V ∧ RealAt d (j + 1) hj h La ((ex.tw.fm u μ).emb (j + 1) x) V) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPos ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  intro d j hj h La hLa x
  have hr := (GlobalTheory.TwV.DelA.posTie_at S hPos ι hι).2
  obtain ⟨c, κ, _, hκ, hy, hiff⟩ := GlobalTheory.T.realAt_succ_iff_decomposition_values S d j hj h La hLa
  obtain ⟨g, hgb, hpt⟩ := GlobalTheory.T.latticeTupleSuccLevel_point_isComponentPointInChart S hDict j hj La hLa
  have hH := ((H.core j hj) ((I.at' j hj).st.eC.symm La.1).1).toHyp Formalism.L2.G.RelativeIndexFlags.blockRationality_holds
  have hv := valC_spec hH.ex ((I.at' j hj).eps.symm x) ((I.at' j hj).st.eC.symm La.1).2 La.2 hLa
  refine ⟨MvPolynomial.map D.what₂.embLL (valC ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev (embT D) D.what₂.embLL
    ((I.at' j hj).st.charts.gat ((I.at' j hj).st.eC.symm La.1).1) ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1)
    (I.at' j hj).st.pos ((I.at' j hj).st.embN ((I.at' j hj).st.eC.symm La.1).1) ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y
    ((I.at' j hj).eps.symm x) ((I.at' j hj).st.eC.symm La.1).2 La.2), ?_, ?_⟩
  · rw [kaAt_cmp X H hT j hj x]
    show MvPolynomial.map _ (cmpC _ _ _ _ _ _ _ _ _ _ _ _) = _
    simp only [cmpC, hLa, if_true]
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    refine congrArg (fun f => MvPolynomial.map f _) ?_
    exact RingHom.ext fun r => (hr r).symm
  · rw [hiff]
    intro z z' hz
    have h2 : trC (X.onCh j hj) (j + 1) ((ex.tw.fm u μ).emb (j + 1) x) =
        (I.at' j hj).M.emb (j + 1) ((I.at' j hj).eps.symm x) := by
      apply trC_heq
      have := (I.at' j hj).eps_emb ((I.at' j hj).eps.symm x)
      rwa [LinearEquiv.apply_symm_apply] at this
    have hp1 := hpt
    rw [d.eq (j + 1) hj La hLa, hy] at hp1
    have hk := congrArg (fun k => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 g
      (GlobalTheory.TwU.ratA D.host.F (d.gam (j + 1) hj La) * (((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y c).1 * k)) hκ
    have hp2 := hk.mpr hp1
    have hv2 := hv.2 g hgb c (d.gam (j + 1) hj La) (d.mem (j + 1) hj La) κ hp2 z z' hz
    rw [h2, ← embN_eq_nrmR]
    exact hv2
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem castSt_lb {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    (S : GlobalTheory.TwU.StepCharts C i hi) (β : S.Ch) (T : GlobalTheory.TwU.StepCharts C' i hi) (hT : T = castSt h S) :
    ∃ β' : T.Ch, (T.K β').lev.Lb = (S.K β).lev.Lb := by
  subst hT
  subst h
  exact ⟨β, rfl⟩

theorem uB_det_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j) τ, ‖ι (embT D τ (uB J j hj a).1.det)‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj a τ
  have hU := GlobalTheory.T.local_space_gram_transform S hPos ι hι j hj
  have hO := (bAt_orth_lev S j hj a).1
  have e : (uB J j hj a).1.det = (J.A.crd j hj).1.det * (bAt J j hj a).1.det := by
    simp [uB, Matrix.det_mul]
  rw [e]
  cases j with
  | zero =>
    obtain ⟨c⟩ := Formalism.MainNotions.G.KAat.cl_nonempty J.one a
    refine hU ((J.St 0 hj).chOf (J.e0 c)) (bAt J 0 hj a) hO (fun v => ?_) τ
    rw [(J.lev0 _).1]
    exact J.lb0 v
  | succ j =>
    obtain ⟨β, hβ⟩ := castSt_lb (X.onCh j hj) (GlobalTheory.TwU.StepCharts.ofStepIn (I.at' j hj).st) ((I.at' j hj).st.eC.symm a).1 _ (J.st j hj)
    refine hU β (bAt J (j + 1) hj a) hO (fun v => ?_) τ
    rw [hβ]
    have h1 := J.lbB j hj ((I.at' j hj).st.eC.symm a).1 v
    rw [J.iw j hj _ v] at h1
    exact h1

end GlobalTheory.TwV.DelA
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.trueColumns_goodCharts_middleSteps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∀ (i : ℕ) (hi : i ≤ B.R.m), 1 ≤ i → i < B.R.m → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (Kc : Fam I l Z u a i hi (badQ (I.rec7 l Z) Q) chOf), ReadsOne I l Z u a i hi chOf Kc ∧ ∀ β, FunKilled (Kc β).lev (X.piT u) ∧ ∃ n : ℕ, 0 < n ∧ ∀ κ, (Kc β).lev.chi κ ^ n = 1 := by
  first | exact @GlobalTheory.TwU.AtTrue.goodCharts_mid | exact GlobalTheory.TwU.AtTrue.goodCharts_mid | (intros; apply GlobalTheory.TwU.AtTrue.goodCharts_mid <;> assumption)
end
