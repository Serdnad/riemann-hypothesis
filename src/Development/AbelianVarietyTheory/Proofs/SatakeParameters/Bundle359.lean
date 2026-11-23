module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle025
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle332
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle348
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle247
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle120
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle324
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle026
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle354
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle351
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle349
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle350
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle352
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
import Formalism.LocalToGlobal.InertKernelTheory.DelPolOfTies
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)

noncomputable section

namespace GlobalTheory.AwayMat
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levOne_of_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := GlobalTheory.T.congruentOne_mem_stepLevel_levelChar_eq_one

theorem muAt_det_of_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ) (P : rowSG Pr sel mu) (n : ℕ) (k : Sp X.E n ≃ₗ[X.E] Sp X.E n),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E n) l))) →
    muAt Ch sel mu cst i P ((LinearEquiv.det k : X.Eˣ) : X.E) = 1 := GlobalTheory.T.localChar_det_eq_one_of_congr_one_mod_pow

theorem xiAt_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ), i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N i) ≃ₗ[X.E] Sp X.E (R.N i)) (k' : Sp X.E (R.N (i + 1)) ≃ₗ[X.E] Sp X.E (R.N (i + 1))),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N i)) l))) →
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k' (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N (i + 1))) l))) →
    ∀ x, XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (inFr k k' x) = XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hCh hsel hL i hi al be P k k' hk hk' x
  obtain ⟨r, hr, hrk, hc⟩ := levOne_of_cong Ch sel mu cst L G m2 hX hPr hCh hsel hL i hi.le al P k hk
  obtain ⟨r', hr', hrk', hc'⟩ := levOne_of_cong Ch sel mu cst L G m2 hX hPr hCh hsel hL (i + 1) hi be P k' hk'
  have h := GlobalTheory.UnfoldTwoSided.xiAt_two_sided Ch sel mu cst L G m2 hX hPr hCh hsel hL i hi al be P r r' k k' hr hr' hrk hrk' x
  rw [hc, hc', muAt_det_of_cong Ch sel mu cst L G m2 hX hPr hsel hL i P _ k hk, muAt_det_of_cong Ch sel mu cst L G m2 hX hPr hsel hL i P _ k' hk'] at h
  simpa only [one_mul] using h

theorem decoAtT_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    p₁.deco.1.at P.1 = p.deco.1.at P.1 ∧ ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y := fun A dtU a H T i hi β x x₁ p p₁ h1 h2 P hv => ⟨GlobalTheory.T.localizedLattice_eq_of_adelic_matrices_agree_at_place A dtU a H T i hi β x x₁ p p₁ h1 h2 P hv, GlobalTheory.T.chartFunctional_eq_of_agree_under_levelPrime A dtU a H T i hi β x x₁ p p₁ h1 h2 P hv⟩

theorem frames_cong : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : SB t μ,
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∃ k : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i), frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k ∧
      ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) l)) := GlobalTheory.T.chainChart_frames_badPrime_congruent_one_of_adelic_agree

theorem inFr_mul {E : Type} [Field E] {n n' : ℕ} (f k : Sp E n ≃ₗ[E] Sp E n) (f' k' : Sp E n' ≃ₗ[E] Sp E n') (z : HomE E n n') :
    inFr (f * k) (f' * k') z = inFr k k' (inFr f f' z) := LinearMap.ext fun _ => rfl

theorem ptAway_mat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i < t.m2 → PtAway A a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi him
  intro β β' x x' x₁ x₁' p p' p₁ p₁' h1 h2 h3 h4 hag
  classical
  have hSS : (t.rd u μ).SS = Sall t.sel (t.tup μ) (t.word u) := ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 T.isChainTop).1
  have hv : ∀ Q, Q ∈ Sall t.sel (t.tup μ) (t.word u) → ∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam Q) →
      bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 ∧ bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1 :=
    fun Q hQ v hvQ => hag v ⟨seamP t.seam Q, (mem_ssRec t u μ Q).2 (hSS ▸ hQ), hvQ⟩
  have hX : t.X.AbelianUnramifiedExtensionConditions := H.fields
  have hCh : t.Ch.Ok := H.ch.ch_ok
  have hL := t.idx_ok μ
  funext z
  unfold xiPt
  rw [dite_eq_left him, dite_eq_left him]
  unfold XiEntry
  refine congrArg₂ (· * ·) ?_ ?_
  · have eA := fun P : t.Pr.vT (t.word u) => decoAtT_eq A dtU a H T i _ β x x₁ p p₁ h1 h3 P
      (fun v hv' => (hv P.1 (Finset.mem_union_left _ P.2) v hv').1)
    have eA' := fun P : t.Pr.vT (t.word u) => decoAtT_eq A dtU a H T (i + 1) hi β' x' x₁' p' p₁' h2 h4 P
      (fun v hv' => (hv P.1 (Finset.mem_union_left _ P.2) v hv').2)
    have key : (∀ P : t.Pr.vT (t.word u), ∀ y ∈ p₁.deco.1.at P.1, z y ∈ p₁'.deco.1.at P.1 ∧ p₁'.deco.1.f P (z y) = p₁.deco.1.f P y) ↔
        (∀ P : t.Pr.vT (t.word u), ∀ y ∈ p.deco.1.at P.1, z y ∈ p'.deco.1.at P.1 ∧ p'.deco.1.f P (z y) = p.deco.1.f P y) := by
      refine forall_congr' fun P => ?_
      obtain ⟨a1, f1⟩ := eA P
      obtain ⟨a2, f2⟩ := eA' P
      rw [a1, a2]
      refine forall₂_congr fun y hy => and_congr_right fun hzy => ?_
      rw [f1 y hy, f2 _ hzy]
    unfold phiT
    by_cases hc : ∀ P : t.Pr.vT (t.word u), ∀ y ∈ p.deco.1.at P.1, z y ∈ p'.deco.1.at P.1 ∧ p'.deco.1.f P (z y) = p.deco.1.f P y
    · rw [if_pos hc, if_pos (key.2 hc)]
    · rw [if_neg hc, if_neg (fun h => hc (key.1 h))]
  · refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨k, hk, hkc⟩ := frames_cong A dtU a H T i _ β x x₁ p p₁ h1 h3 P
      (fun v hv' => (hv P.1 (Finset.mem_union_right _ P.2) v hv').1)
    obtain ⟨k', hk', hkc'⟩ := frames_cong A dtU a H T (i + 1) hi β' x' x₁' p' p₁' h2 h4 P
      (fun v hv' => (hv P.1 (Finset.mem_union_right _ P.2) v hv').2)
    rw [hk, hk', inFr_mul]
    exact xiAt_cong t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hX t.pr_ok hCh H.sel hL i him _ _ P k k' hkc hkc' _

end GlobalTheory.AwayMat
end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frame_localLattice_span_kernelLattice_succ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j + 1 ≤ D.R.m → ∀ La : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN (j + 1) La) = ((sysS H X std).latAt v (j + 1) La.2).map ((((J.fd std).frM (j + 1) La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  first | exact @GlobalTheory.TwV.Joint.locSp_kerN_succ | exact GlobalTheory.TwV.Joint.locSp_kerN_succ | (intros; apply GlobalTheory.TwV.Joint.locSp_kerN_succ <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.frame_localLattice_span_kernelLattice_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ La : (sysS H X std).Lt 0, ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN 0 La) = ((sysS H X std).latAt v 0 La.2).map ((((J.fd std).frM 0 La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  first | exact @GlobalTheory.TwV.Joint.locSp_kerN_zero | exact GlobalTheory.TwV.Joint.locSp_kerN_zero | (intros; apply GlobalTheory.TwV.Joint.locSp_kerN_zero <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stepZero_kernelLattice_eq_pointKernelLattice : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), HEq ((J.fd std).kerN 0 La) (latK D.sp (gramN D 0 (Nat.zero_le _)) J.a (J.pt std 0 (Nat.zero_le _) La).1 ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.Lb) := by
  first | exact @GlobalTheory.kerN_zero_eq_latK_pt | exact GlobalTheory.kerN_zero_eq_latK_pt | (intros; apply GlobalTheory.kerN_zero_eq_latK_pt <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.succStep_kernelLattice_eq_pointKernelLattice : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → HEq ((J.fd std).kerN (j + 1) La) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La).1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb) := by
  first | exact @GlobalTheory.TwV.Joint.kerN_succ_heq | exact GlobalTheory.TwV.Joint.kerN_succ_heq | (intros; apply GlobalTheory.TwV.Joint.kerN_succ_heq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.tuplesLocalModels_of_otherDivisionLatticesHeights : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), ModelsAt D O → ModelsAt (setDiv D N h) (O.tr N h) := by
  first | exact @GlobalTheory.Svd.modelsAt_tr | exact GlobalTheory.Svd.modelsAt_tr | (intros; apply GlobalTheory.Svd.modelsAt_tr <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

namespace GlobalTheory.TwV.DelB.UnitB

theorem det_map_transpose {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (M : Matrix (Fin N) (Fin N) E) :
    ((M.map σ)ᵀ).det = σ M.det := by
  rw [Matrix.det_transpose, RingHom.map_det]
  rfl

theorem det_unitary_prod {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (J c B : Matrix (Fin N) (Fin N) E)
    (hc : (c.map σ)ᵀ * c = J) (hB : (B.map σ)ᵀ * J * B = 1) :
    σ (c.det * B.det) * (c.det * B.det) = 1 := by
  have h : ((c * B).map σ)ᵀ * (c * B) = 1 := by
    rw [Matrix.map_mul, Matrix.transpose_mul]
    calc (B.map σ)ᵀ * (c.map σ)ᵀ * (c * B) = (B.map σ)ᵀ * ((c.map σ)ᵀ * c) * B := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hc, hB]
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, det_map_transpose, Matrix.det_one, Matrix.det_mul] at hd
  exact hd

end GlobalTheory.TwV.DelB.UnitB


open GlobalTheory.TwV.DelB.UnitB in
theorem GlobalTheory.TwV.DelB.detCrdB_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) B.1 * gramN D j hj * B.1 = 1 → (∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v))) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ ((J.A.crd j hj).1.det * B.1.det))‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj β B hB hL τ
  refine GlobalTheory.T.norm_cmEmbedding_normOne_localUnit_eq_one S hPos ι hι _ ?_ (fun v => GlobalTheory.T.det_orthonormalCoords_mul_basis_localUnit S j hj β B v (hL v)) τ
  have hc := J.pins.crd_orth j hj
  have h1 := det_unitary_prod (sigD D : D.host.E →+* D.host.E) (gramN D j hj) (J.A.crd j hj).1 B.1 hc hB
  have hconj : ∀ y : D.host.E, D.host.conj y = (sigD D : D.host.E →+* D.host.E) y := fun y => (bridge_star_holds D.R D.host y).symm
  rw [hconj, mul_comm]
  exact h1
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.muT_det_ratA : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩) ∧ ∀ k (hk : k ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk), S.muT (j + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) = ∏ τ, TaylorLogMetric.embT D τ γ.1.det ^ e τ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj
  obtain ⟨e, he, hz⟩ := S.law.mu_rat j hj
  refine ⟨e, he, fun k hk γ hγ => ?_⟩
  have hu := ((GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S) k hk).2 γ hγ
  have key : Matrix.GeneralLinearGroup.det (ratA D.host.F γ) =
      Formalism.L2.DIV.ratId D.host.F D.host.E (Matrix.GeneralLinearGroup.det γ) := by
    ext
    simp [ratA, Formalism.UG.bc, Formalism.L2.DIV.ratId, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [key]
  have h2 := hz (Matrix.GeneralLinearGroup.det γ) (by simpa using hu.2)
  simpa using h2
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem castSt_ofStepIn_read {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (St : GlobalTheory.TwU.StepCharts C' i hi) (hSt : St = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn S))
    (β : S.Ch) (c : {c // S.chOf c = β}) (c' : C'.cls i) (hc' : c' = castCls h i c.1) :
    (St.y c').1 = ((S.K β).y c).1 ∧
    (∀ κ' : (St.K (St.chOf c')).lev.U, ∃ κ : (S.K β).lev.U, κ.1 = κ'.1 ∧
      (((S.K β).lev.chi κ : ℂˣ) : ℂ) = (((St.K (St.chOf c')).lev.chi κ' : ℂˣ) : ℂ)) ∧
    ∀ (φ : C'.cls i → C'.Y i → ℂ) (z : Fr D i hi), φ c' (St.eY.symm z) = trC h i φ c.1 (S.eY.symm z) := by
  subst hSt hc' h
  obtain ⟨c, rfl⟩ := c
  exact ⟨rfl, fun κ' => ⟨κ', rfl, rfl⟩, fun φ z => rfl⟩

theorem nrmR_apply_eq {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (β : S.Ch) (φ : C.cls i → C.Y i → ℂ) (c : {c // S.chOf c = β}) (z : Fr D i hi) :
    nrmR S β φ c z = S.kTw β * (((S.tw β).ch ((S.K β).y c) : ℂ) * detF (cTw D i) z * φ c.1 (S.eY.symm z)) := rfl

end GlobalTheory.TwV.DelA



theorem GlobalTheory.TwV.DelA.realAt_succ_decomp : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ (c : {c // (I.at' j hj).st.chOf c = ((I.at' j hj).st.eC.symm La.1).1}) (κ : ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U), castCls (X.onCh j hj) (j + 1) c.1 = clsAt X H (j + 1) La.1 La.2 ∧ κ.1 = (d.kap (j + 1) hj La).1 ∧ ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 = (((I.at' j hj).st.K _).y c).1 ∧ ∀ φ V, RealAt d (j + 1) hj h La φ V ↔ ∀ z z' : Fr D (j + 1) hj, IsTr (atInf (embT D) (d.gam (j + 1) hj La).1) z' z → evC (gatJ Lv (j + 1)).P ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk (I.at' j hj).st.pos (gramC (gramN D (j + 1) hj) (embT D)) (crdB (embT D) ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).B) V z = ((((I.at' j hj).st.K _).lev.chi κ : ℂˣ) : ℂ) * nrmR (I.at' j hj).st _ (trC (X.onCh j hj) (j + 1) φ) c z') := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj h La hLa
  have hc := clsOf_chart (S := (I.at' j hj).st) (H.core j hj) La.1 La.2 hLa
  have hcls : clsAt X H (j + 1) La.1 La.2 = castCls (X.onCh j hj) (j + 1) (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) :=
    clsAt_succ X H j hj La.1 La.2
  obtain ⟨hy, hk, hφ⟩ := GlobalTheory.TwV.DelA.castSt_ofStepIn_read (X.onCh j hj) (I.at' j hj).st (J.St (j + 1) hj) (J.st j hj) _
    ⟨_, hc⟩ _ hcls
  obtain ⟨κ, hκ1, hκχ⟩ := hk (d.kap (j + 1) hj La)
  refine ⟨⟨_, hc⟩, κ, hcls.symm, hκ1, hy, fun φ V => ?_⟩
  have htw := GlobalTheory.T.stepTwist_at_classRep_eq_charPow_det S j hj _ ⟨_, hc⟩
  unfold RealAt
  refine forall_congr' fun z => forall_congr' fun z' => imp_congr_right fun _ => ?_
  have hR : d.chi (j + 1) hj La * ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D (j + 1) *
        dPow (bAt J (j + 1) hj La.1).1 (fun _ => -(cTw D (j + 1))) * detF (cTw D (j + 1)) z' *
        φ (clsAt X H (j + 1) La.1 La.2) ((J.St (j + 1) hj).eY.symm z') =
      ((((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.chi κ : ℂˣ) : ℂ) *
        nrmR (I.at' j hj).st _ (trC (X.onCh j hj) (j + 1) φ) ⟨_, hc⟩ z' := by
    have a1 : d.chi (j + 1) hj La = ((((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.chi κ : ℂˣ) : ℂ) := hκχ.symm
    have a2 : ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D (j + 1) =
        (((I.at' j hj).st.tw ((I.at' j hj).st.eC.symm La.1).1).ch (((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩) : ℂ) := by
      rw [htw, Units.val_zpow_eq_zpow_val, hcls]
    have a3 : dPow (bAt J (j + 1) hj La.1).1 (fun _ => -(cTw D (j + 1))) = (I.at' j hj).st.kTw ((I.at' j hj).st.eC.symm La.1).1 := rfl
    rw [a1, a2, a3, hφ φ z', GlobalTheory.TwV.DelA.nrmR_apply_eq]
    ring
  simp only [J.pos j hj]
  refine Iff.trans (Eq.congr_right hR) ?_
  exact Iff.rfl
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelSite_chartBasis_orthonormal_levelIndependent : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j), cT (sigD D : D.host.E →+* D.host.E) (bAt J j hj a).1 * gramN D j hj * (bAt J j hj a).1 = 1 ∧ ∀ a', bAt J j hj a' = bAt J j hj a) := by
  first | exact @GlobalTheory.TwV.DelA.bAt_orth_lev | exact GlobalTheory.TwV.DelA.bAt_orth_lev | (intros; apply GlobalTheory.TwV.DelA.bAt_orth_lev <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.comparedForm_levelZero_realises_complexPoly : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) (h : ((sysS H X std).Pj 0).m + 1 = D.R.N 0) (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat 0).V, ∃ V : XR ((sysS H X std).Pj 0) ℂ, MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp 0 x La.1 La.2) = MvPolynomial.map ι V ∧ RealAt d 0 (Nat.zero_le _) h La ((ex.tw.fm u μ).emb 0 x) V) := by
  first | exact @GlobalTheory.TwV.DelA.cmp_realAt_zero | exact GlobalTheory.TwV.DelA.cmp_realAt_zero | (intros; apply GlobalTheory.TwV.DelA.cmp_realAt_zero <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kernelSite_valuesAtPoint_iff_realisesInStdCoords : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) (e : D.what₂.Tau → ℤ) (φ : (D.chTw u μ).cls j → (D.chTw u μ).Y j → ℂ) (P : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), (∀ y, φ (clsAt X H j La.1 La.2) y = (∏ τ, (D.chTw u μ).de j y τ ^ e τ)⁻¹ * frPoly (t.O u μ) j P y) → ∀ V, RealAt d j hj h La φ V ↔ Realises (sysS H X std) D (hT.gat_pos u w hg) j h (fun τ => e τ - cTw D j) (sPt d j hj La • P) (actC (sysS H X std) D (hT.gat_pos u w hg) j h (mM d j hj La) V)) := by
  first | exact @GlobalTheory.TwV.DelA.realAt_iff_realises | exact GlobalTheory.TwV.DelA.realAt_iff_realises | (intros; apply GlobalTheory.TwV.DelA.realAt_iff_realises <;> assumption)
end
