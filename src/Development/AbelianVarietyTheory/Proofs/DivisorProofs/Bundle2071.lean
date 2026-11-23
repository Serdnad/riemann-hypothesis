module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle385
public import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBound
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.CosetFix

variable {D : D7}

theorem zeroAt_zero (q : ℕ) : ZeroAt D q 0 :=
  fun _ => ⟨1, one_pos, Nat.coprime_one_left _, 0, zero_mem _, by simp⟩

theorem trivAt_one {N : ℕ} (q : ℕ) : TrivAt D q ((1 : GA D N) : GL (Fin N) (AE D)) := fun i j => by
  simpa using zeroAt_zero (D := D) q



theorem fix_of_prop {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (hT : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d) {g' : GA D P.d}
    {H : VC D P.a P.d → ℂ} {c : ℂ} (hc' : P.W.Om 1 g' P.e0 = c • H) :
    H ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧ ∀ k : GA D P.a, P.W.Om k 1 P.e0 = P.e0 → P.W.Om k 1 H = H := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply P.W.nz
    have h0 : P.W.Om 1 g' P.e0 = 0 := by rw [hc', zero_smul]
    have e := P.W.mul 1 1 g'⁻¹ g' P.e0 hT
    have e1 : (1 : GA D P.a) * 1 = 1 := mul_one 1
    have e2 : g'⁻¹ * g' = 1 := inv_mul_cancel g'
    rw [e1, e2, P.W.one _ hT, h0] at e
    have z := P.W.smul 1 g'⁻¹ (0 : ℂ) (0 : VC D P.a P.d → ℂ) (NormUniq.tt_zero _)
    have z0 : (0 : ℂ) • (0 : VC D P.a P.d → ℂ) = 0 := zero_smul ℂ _
    rw [z0] at z
    rw [e, z]
    exact zero_smul ℂ _
  have hHT : H ∈ TT D (tor0 D ⊤ δ) P.a P.d := by
    have e : H = c⁻¹ • P.W.Om 1 g' P.e0 := by rw [hc', smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hm : P.W.Om 1 g' P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d := P.W.maps 1 g' P.e0 hT
    rw [e]
    exact NormUniq.tt_smul hm c⁻¹
  refine ⟨hHT, fun k he => ?_⟩
  have e1 := P.W.mul k 1 1 g' P.e0 hT
  have e2 := P.W.mul 1 k g' 1 P.e0 hT
  have f1 : k * (1 : GA D P.a) = k := mul_one k
  have f2 : (1 : GA D P.d) * g' = g' := one_mul g'
  have f3 : (1 : GA D P.a) * k = k := one_mul k
  have f4 : g' * (1 : GA D P.d) = g' := mul_one g'
  rw [f1, f2] at e1
  rw [f3, f4] at e2
  have e3 : P.W.Om k 1 (P.W.Om 1 g' P.e0) = P.W.Om 1 g' P.e0 := by rw [← e1, e2, he]
  rw [hc', P.W.smul _ _ _ _ hHT] at e3
  exact smul_right_injective _ hc0 e3

theorem iop_facts (hI : Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) :
    Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 ∈
      TT D (tor0 D ⊤ δ) P.a P.d ∧
    ∀ k : GA D P.a, P.W.Om k 1 P.e0 = P.e0 →
      P.W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d)
        (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0) =
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 := by
  obtain ⟨g', hg'⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D P.d _ (GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d)
  obtain ⟨c, hc⟩ := VacMove.exists_scalar hI P.crv P.vac.1 P.W 1 g' (VacMove.moves_one D P.a) hg'
  exact fix_of_prop P (VacMove.vac_TT hI.g1 P.crv P.vac.1) (c := c) (by rw [hc]; funext z; rfl)

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem vac_fix_split (G : GridData L sc) (i j : Fin D.R.m) {μ₀ : T} (hL : L.Is μ₀) {δ t0 : ℂ} {Q : ℕ}
    {P P' : Pair D ⊤ δ t0 Q} (h : IsBottom G μ₀ i j (condE G.pl) P P') {k : GA D P.a} (hk : k ∈ intG D P.a)
    (hk' : CongOne D (condE G.pl) k) (hs : SuppSplit D (k : GL (Fin P.a) (AE D))) : P.W.Om k 1 P.e0 = P.e0 := by
  obtain ⟨x, hxu, hxi, hx, h1, h2⟩ := GlobalTheory.FunObj.NormUniq.SplitDet.exists_splitComp_det hk hk' hs
  have hm : Moves D (k : GL (Fin P.a) (AE D)) (stdL D P.a) := by
    simpa using VacMove.moves_mul_int hk (VacMove.moves_one D P.a)
  have e := P.W.split k 1 x 1 (stdL D P.a) (stdL D P.d) hs (fun q _ _ => trivAt_one q)
    (fun q hq hi => ⟨hxi q hq hi, by simpa using zeroAt_zero (D := D) q⟩) hx (by simp) hm (VacMove.moves_one D P.d)
  have hc : P.W.chV'.f x ^ P.W.ep' = 1 := by
    rw [h.chars.2 x]
    show ((nuH G μ₀ i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x))⁻¹ = 1
    rw [GlobalTheory.NuTrivSq.nuH_finIdl_eq_one G i j hL x hxu h1 h2, inv_one]
  rw [e, map_one, one_zpow, hc, one_mul,
    show La D (tor0 D ⊤ δ) (stdL D P.a) (stdL D P.d) = La0 D (tor0 D ⊤ δ) P.a P.d from rfl,
    VacMove.iop_self D _ (La0 D (tor0 D ⊤ δ) P.a P.d) P.vac.1]
  funext z
  simp

theorem vac_fix (G : GridData L sc) (i j : Fin D.R.m) (hI : Inp D) {μ₀ : T} (hL : L.Is μ₀) {δ t0 : ℂ} {Q : ℕ}
    {P P' : Pair D ⊤ δ t0 Q} (h : IsBottom G μ₀ i j (condE G.pl) P P') {k : GA D P.a} (hk : k ∈ intG D P.a)
    (hk' : CongOne D (condE G.pl) k) : P.W.Om k 1 P.e0 = P.e0 := by
  obtain ⟨ks, ki, rfl, hs, hi, hs', hss, hii⟩ := GlobalTheory.CongSplitFactor.exists_split_inert_factor hk hk'
  have hT := VacMove.vac_TT hI.g1 P.crv P.vac.1
  have h1 : P.W.Om ki 1 P.e0 = P.e0 :=
    P.W.inert ki 1 ((mem_intG ki).1 hi) ((mem_intG 1).1 (one_mem _)) hii (fun q _ _ => trivAt_one q)
  have e := P.W.mul ks ki 1 1 P.e0 hT
  rw [mul_one] at e
  rw [e, h1, vac_fix_split G i j hL h hs hs' hss]

theorem cosetVec_fix (G : GridData L sc) (i j : Fin D.R.m) (hI : Inp D) {μ₀ : T} (hL : L.Is μ₀) {δ t0 : ℂ} {Q : ℕ}
    {P P' : Pair D ⊤ δ t0 Q} (h : IsBottom G μ₀ i j (condE G.pl) P P') {k : GA D P.a} (hk : k ∈ intG D P.a)
    (hk' : CongOne D (condE G.pl) k) : P.W.Om k 1 (cosetVec P (condE G.pl) 0) = cosetVec P (condE G.pl) 0 := by
  obtain ⟨hHT, hfix⟩ := iop_facts hI P (condE_ne_bot G.pl)
  have hH := hfix k (vac_fix G i j hI hL h hk hk')
  have hW := GlobalTheory.HeisFix.heis_fix hI P (condE_ne_bot G.pl) 0 hk hk' hHT hH
  have hWT := GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT P.crv one_pos (by rw [one_smul]; exact pt_unitBlock_mem δ 0 P.a P.d) hHT
  unfold cosetVec
  rw [P.W.smul _ _ _ _ hWT, hW]

end GlobalTheory.FunObj.CosetFix
end
end

section



open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

noncomputable section

namespace GlobalTheory.FlatTw.Mul

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {G₀ : WTZ E}

theorem mul_idem_cusp {G : WTZ E} {f : Rul Xo c} (hf : f ∈ cuspOn U Z G) : f * idem Z = f := by
  rw [mul_comm]; exact idem_mul_eq (e := exZ Dw G) ⟨cuspW_le_secZ G hf.1, hf.2⟩

def mulEquiv (s : TwSec U x Z G₀) (G : WTZ E) (hG : Even G.2) : cuspOn U Z G ≃ₗ[c.F] cuspOn U Z (G + G₀) where
  toFun f := ⟨(f : Rul Xo c) * s.sig, s.cusp_sig G hG f f.2⟩
  invFun g := ⟨(g : Rul Xo c) * s.inv, s.cusp_inv G hG g g.2⟩
  map_add' f f' := Subtype.ext (add_mul _ _ _)
  map_smul' a f := Subtype.ext (smul_mul_assoc a (f : Rul Xo c) s.sig)
  left_inv f := Subtype.ext (by
    show (f : Rul Xo c) * s.sig * s.inv = f
    rw [mul_assoc, s.mul_inv, mul_idem_cusp f.2])
  right_inv g := Subtype.ext (by
    show (g : Rul Xo c) * s.inv * s.sig = g
    rw [mul_assoc, mul_comm s.inv, s.mul_inv, mul_idem_cusp g.2])

theorem ereal_nonneg {a b : ℝ} {t : EReal} (ht : 0 ≤ t) (hab : 0 ≤ a + b) :
    0 ≤ ((a : ℝ) : EReal) + (t + ((b : ℝ) : EReal)) := by
  rw [add_comm t, ← add_assoc, ← EReal.coe_add]
  exact add_nonneg (EReal.coe_nonneg.2 hab) ht

theorem mem_latOn_of_mul (s : TwSec U x Z G₀) {G G' : WTZ E} (a : c.F) (ha : a ≠ 0)
    (hlo : ∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) (f : cuspOn U Z G) (hf : f ∈ latOn U Z G)
    (g : cuspOn U Z G') (hg : (g : Rul Xo c) = a • ((f : Rul Xo c) * s.sig)) : g ∈ latOn U Z G' := by
  refine (mem_supLat_iff (Z := Z) g.2.2).2 fun w v hv => ?_
  have hfv : 0 ≤ v (f : Rul Xo c) := ((mem_supLat_iff (Z := Z) f.2.2).1 hf) w v hv
  obtain ⟨b, hb, -, hlb, -⟩ := s.exists_val hv
  rw [hg, (isVal_valOn hv).smul _ _ ha, (isVal_valOn hv).mul, hb]
  exact ereal_nonneg hfv (by linarith [hlo w])

theorem mem_latOn_of_mul_inv (s : TwSec U x Z G₀) {G G' : WTZ E} (b : c.F) (hb : b ≠ 0)
    (hhi : ∀ w, s.hi w ≤ (vAdd w b : ℝ)) (g : cuspOn U Z G') (hg : g ∈ latOn U Z G')
    (f : cuspOn U Z G) (hf : (f : Rul Xo c) = b • ((g : Rul Xo c) * s.inv)) : f ∈ latOn U Z G := by
  refine (mem_supLat_iff (Z := Z) f.2.2).2 fun w v hv => ?_
  have hgv : 0 ≤ v (g : Rul Xo c) := ((mem_supLat_iff (Z := Z) g.2.2).1 hg) w v hv
  obtain ⟨β, -, hβ, -, hβh⟩ := s.exists_val hv
  rw [hf, (isVal_valOn hv).smul _ _ hb, (isVal_valOn hv).mul, hβ]
  exact ereal_nonneg hgv (by linarith [hhi w])

theorem twSec_mulEquiv_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∃ φ : cuspOn U Z G ≃ₗ[c.F] cuspOn U Z (G + G₀), (∀ f, (φ f : Rul Xo c) = f * s.sig) ∧ (∀ g, (φ.symm g : Rul Xo c) = g * s.inv) ∧ (∀ a : c.F, a ≠ 0 → (∀ w, 0 ≤ (vAdd w a : ℝ) + s.lo w) → ∀ f ∈ latOn U Z G, ∀ g : cuspOn U Z (G + G₀), (g : Rul Xo c) = a • (φ f : Rul Xo c) → g ∈ latOn U Z (G + G₀)) ∧ (∀ b : c.F, b ≠ 0 → (∀ w, s.hi w ≤ (vAdd w b : ℝ)) → ∀ g ∈ latOn U Z (G + G₀), ∀ f : cuspOn U Z G, (f : Rul Xo c) = b • (φ.symm g : Rul Xo c) → f ∈ latOn U Z G) := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s G hG
  refine ⟨mulEquiv s G hG, fun _ => rfl, fun _ => rfl, fun a ha hlo f hf g hg => ?_, fun b hb hhi g hg f hf => ?_⟩
  · exact mem_latOn_of_mul s a ha hlo f hf g hg
  · exact mem_latOn_of_mul_inv s b hb hhi g hg f hf

end GlobalTheory.FlatTw.Mul
end
end

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum



noncomputable section

namespace GlobalTheory.FlatTw.PetTw

theorem homN_mul_sig_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
    {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) {G : WTZ E} (hG : Even G.2) {f : Rul Xo c} (hf : f ∈ suppOn Z)
    (σ : c.F →+* ℂ) (z : Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) :
    homN (U (goodOf c σ)) x (G + G₀) (f * s.sig) z = s.cInf σ * homN (U (goodOf c σ)) x G f z := by
  by_cases hz : z ∈ framesOn (U (goodOf c σ)) Z
  · rw [s.homN_mul_sig hG f hz, mul_comm]
  · have h1 : rdU (U (goodOf c σ)) (f * s.sig) z.1 z.2 = 0 :=
      rdU_eq_zero _ (mul_mem_suppOn f s.sig_mem_suppOn) hz
    have h2 : rdU (U (goodOf c σ)) f z.1 z.2 = 0 := rdU_eq_zero _ hf hz
    show _ * (‖rdU (U (goodOf c σ)) (f * s.sig) z.1 z.2‖ * _) = s.cInf σ * (_ * (‖rdU (U (goodOf c σ)) f z.1 z.2‖ * _))
    rw [h1, h2, norm_zero, zero_mul, zero_mul, mul_zero, mul_zero, mul_zero]

theorem petAt_mul_sig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∀ f ∈ suppOn Z, ∀ (σ : c.F →+* ℂ) (D : D7) (V : HSp D) (dict : GA D V → Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) (μ : Measure (AutQ V)), petAt (U (goodOf c σ)) x V dict μ (G + G₀) (f * s.sig) = s.cInf σ * petAt (U (goodOf c σ)) x V dict μ G f := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s G hG f hf σ D V dict μ
  rw [petAt_eq, petAt_eq]
  have e : (fun q : AutQ V => homN (U (goodOf c σ)) x (G + G₀) (f * s.sig) (dict q.out)) =
      s.cInf σ • fun q : AutQ V => homN (U (goodOf c σ)) x G f (dict q.out) :=
    funext fun q => homN_mul_sig_eq s hG hf σ (dict q.out)
  rw [e, eLpNorm'_const_smul _ (by norm_num), ENNReal.toReal_mul, Real.eNorm_eq_ofReal (s.cInf_pos σ).le,
    ENNReal.toReal_ofReal (s.cInf_pos σ).le]

end GlobalTheory.FlatTw.PetTw
end
end

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum



noncomputable section

namespace GlobalTheory.FlatTw.TwSec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c}

theorem exists_pow {G₀ : WTZ E} (s : TwSec U x Z G₀) (n : ℕ) :
    ∃ u : TwSec U x Z (n • G₀), u.lo = n • s.lo ∧ u.degLo = n * s.degLo := by
  induction n with
  | zero =>
    obtain ⟨-, -, h2, -, h3⟩ := const_spec (x := x) s.pts (1 : c.F) one_ne_zero
    refine ⟨(const x s.pts 1 one_ne_zero).copy (zero_nsmul G₀).symm, ?_, ?_⟩
    · funext w
      show (const x s.pts 1 one_ne_zero).lo w = _
      rw [h2 w]
      simp [vAdd]
    · show (const x s.pts 1 one_ne_zero).degLo = _
      rw [h3]; simp
  | succ n ih =>
    obtain ⟨u, hl, hd⟩ := ih
    refine ⟨(u.mul s).copy (succ_nsmul G₀ n).symm, ?_, ?_⟩
    · show u.lo + s.lo = _
      rw [hl, succ_nsmul]
    · show (u.mul s).degLo = _
      rw [degLo_mul, hd]; push_cast; ring

end GlobalTheory.FlatTw.TwSec

theorem GlobalTheory.FlatTw.twSec_mul_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c), (∀ (G₀ G₁ : WTZ E) (s : TwSec U x Z G₀) (t : TwSec U x Z G₁), ∃ u : TwSec U x Z (G₀ + G₁), u.sig = s.sig * t.sig ∧ u.cInf = s.cInf * t.cInf ∧ u.lo = s.lo + t.lo ∧ u.degLo = s.degLo + t.degLo) ∧ ∀ (G₀ : WTZ E) (s : TwSec U x Z G₀) (n : ℕ), ∃ u : TwSec U x Z (n • G₀), u.lo = n • s.lo ∧ u.degLo = n * s.degLo := by
  intro E _ _ _ H Dw l Xo c r U x Z
  exact ⟨fun G₀ G₁ s t => ⟨s.mul t, rfl, rfl, rfl, TwSec.degLo_mul s t⟩, fun G₀ s n => s.exists_pow n⟩
end
end

section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum



namespace GlobalTheory.FlatTw

theorem intOff_of_unramPts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (B : Finset ℕ), UnramPts Xo c B → ∀ (Z : Comp Xo c) (la : _root_.GlobalTheory.AllWt.Weight Dw) (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z la δ), IntOff B (δ + s.rho_vw) := by
  intro E _ _ _ H Dw l Xo c r U x B hB Z la δ s w hw
  obtain ⟨v, hv, hint⟩ := hB Z w hw
  have he := s.val_eq hv
  rcases hint s.sig with h | ⟨n, hn⟩
  · rw [he] at h; exact absurd h (EReal.coe_ne_top _)
  · rw [he] at hn
    exact ⟨n, EReal.coe_eq_coe_iff.1 hn⟩

end GlobalTheory.FlatTw
end

section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal

set_option autoImplicit false

namespace GlobalTheory.DegCmp

theorem X_pow_mul_C_mem_coneAlg {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (d : ℕ) (t : Ω) (ht : t ∈ ((LinearMap.range ev) ^ d : Submodule K Ω)) :
    (Polynomial.X ^ d * Polynomial.C t : Polynomial Ω) ∈ coneAlg ev := by
  induction ht using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [pow_zero, one_mul]
    exact (coneAlg ev).algebraMap_mem r
  | add x y i _ _ hx hy =>
    rw [map_add (f := _), mul_add]
    exact add_mem hx hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨v, rfl⟩ := hm
    have h : (Polynomial.X * Polynomial.C (ev v) : Polynomial Ω) ∈ coneAlg ev := Algebra.subset_adjoin ⟨v, rfl⟩
    have e : (Polynomial.X ^ i.succ * Polynomial.C (ev v * x) : Polynomial Ω) =
        (Polynomial.X * Polynomial.C (ev v)) * (Polynomial.X ^ i * Polynomial.C x) := by
      rw [map_mul, pow_succ]; ring
    rw [e]
    exact mul_mem h hx

theorem mem_coneAlg_iff_coeff : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (p : Polynomial Ω), p ∈ coneAlg ev ↔ ∀ d : ℕ, p.coeff d ∈ ((LinearMap.range ev) ^ d : Submodule K Ω) := by
  intro K V Ω _ _ _ _ _ ev p
  constructor
  · intro hp
    unfold coneAlg at hp
    induction hp using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      intro d
      rcases d with _ | d
      · simp
      · simp only [Polynomial.coeff_X_mul, Polynomial.coeff_C]
        split_ifs with h
        · subst h
          simp
        · exact zero_mem _
    | algebraMap r =>
      intro d
      rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
      split_ifs with h
      · subst h
        rw [pow_zero]
        exact Submodule.algebraMap_mem r
      · exact zero_mem _
    | add x y _ _ hx hy =>
      intro d
      rw [Polynomial.coeff_add]
      exact add_mem (hx d) (hy d)
    | mul x y _ _ hx hy =>
      intro d
      rw [Polynomial.coeff_mul]
      refine Submodule.sum_mem _ fun c hc => ?_
      have hc' : c.1 + c.2 = d := by simpa using hc
      rw [← hc', pow_add]
      exact Submodule.mul_mem_mul (hx _) (hy _)
  · intro h
    rw [p.as_sum_support]
    refine Subalgebra.sum_mem _ fun d _ => ?_
    rw [← Polynomial.C_mul_X_pow_eq_monomial, mul_comm]
    exact X_pow_mul_C_mem_coneAlg ev d _ (h d)

end GlobalTheory.DegCmp
end

section

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal

namespace GlobalTheory.DegCmp

theorem rank_map_eq_of_ker_iff {K M A B : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (S : Submodule K M) (f : M →ₗ[K] A) (g : M →ₗ[K] B)
    (h : ∀ x ∈ S, f x = 0 ↔ g x = 0) :
    Module.rank K (S.map f) = Module.rank K (S.map g) := by
  have hk : LinearMap.ker (f.domRestrict S) = LinearMap.ker (g.domRestrict S) := by
    ext x
    simpa using h x x.2
  rw [← LinearMap.range_domRestrict, ← LinearMap.range_domRestrict,
    ← (LinearMap.quotKerEquivRange _).rank_eq, ← (LinearMap.quotKerEquivRange _).rank_eq, hk]

theorem range_pow_eq_map_homogeneous {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {N : ℕ} (b : Module.Basis (Fin N) K V) (τ : ℕ) :
    ((LinearMap.range ev) ^ τ : Submodule K Ω) =
      (homogeneousSubmodule (Fin N) K τ).map (aeval (fun j => ev (b j)) : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
  rw [← homogeneousSubmodule_one_pow, Submodule.map_pow, homogeneousSubmodule_one_eq_span_X, Submodule.map_span,
    LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
  congr 3
  ext j
  simp

theorem hilb_eq_finrank_quotPiece : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (N : ℕ) (b : Module.Basis (Fin N) K V) (τ : ℕ), hilb ev τ = ((Module.finrank K (GlobalTheory.quotPiece (imageIdeal ev b) (τ : ℤ)) : ℕ) : ℕ∞) := by
  intro K V Ω _ _ _ _ _ ev N b τ
  rw [hilb, range_pow_eq_map_homogeneous ev b τ, GlobalTheory.quotPiece_natCast,
    rank_map_eq_of_ker_iff _ _ (Ideal.Quotient.mkₐ K (imageIdeal ev b)).toLinearMap, ← Module.finrank_eq_rank]
  · simp
  · intro x hx
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact (mem_coneIdeal_of_isHomogeneous _ hx).symm

end GlobalTheory.DegCmp
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.principalLevel_arithmeticGroups_contain_congruence : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (U σ)) l.M := by
  first | exact @GlobalTheory.LevGeo.hasPrinc_laws | exact GlobalTheory.LevGeo.hasPrinc_laws | (intros; apply GlobalTheory.LevGeo.hasPrinc_laws <;> assumption)
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.meanLogSupNormLoss_le_linear_in_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q d M : ℕ) (Om s t L : ℝ), 1 ≤ r → 1 ≤ d → 1 ≤ M → 1 ≤ L → 0 ≤ s → 0 ≤ t → Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L → Real.log d ≤ 4 * L → Real.log (s + t + 1) ≤ 2 * L → lamSup E r q d M Om s t ≤ ((1 + |Om|) / 2 + L + (2 * q + 1) * (6 * fdeg E + 48) * L) * (s + t) := by
  first | exact @GlobalTheory.LamSize.lamSup_le | exact GlobalTheory.LamSize.lamSup_le | (intros; apply GlobalTheory.LamSize.lamSup_le <;> assumption)
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.normFactor_and_density_near_one_in_flagChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w → ∀ z : V (nd X), ‖z‖ ≤ chartRad E r w → cpt X x z ∈ X.dom ∧ Real.exp (-(1/20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1/10)) ≤ densF X x z := by
  first | exact @GlobalTheory.ChartNearOne.chart_near_one | exact GlobalTheory.ChartNearOne.chart_near_one | (intros; apply GlobalTheory.ChartNearOne.chart_near_one <;> assumption)
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.supremum_constant_log_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r d M : ℕ) (w L : ℝ), 2 ≤ r → 1 ≤ d → 1 ≤ M → 1 ≤ L → 1 ≤ w → Real.log (fdeg E * r) ≤ L → Real.log M ≤ 30 * L → Real.log (dE E) ≤ 4 * fdeg E * L → Real.log d ≤ 4 * L → Real.log w ≤ 2 * L → 1 ≤ supConst E r d M w ∧ Real.log (supConst E r d M w) ≤ 250 * (fdeg E : ℝ) ^ 2 * (r : ℝ) ^ 2 * L := by
  first | exact @GlobalTheory.SupConstSize.supConst_size | exact GlobalTheory.SupConstSize.supConst_size | (intros; apply GlobalTheory.SupConstSize.supConst_size <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem _root_.GlobalTheory.T.exists_constant_smul_integral_of_fourth_power : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K ρ : Rul Xo c) (a : Comp Xo c → c.F), (∀ Z, a Z ≠ 0) → (∀ Z, GlobalTheory.FlatLine.idem Z * ρ ^ 4 = a Z • (GlobalTheory.FlatLine.idem Z * K)) → (∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v K) → ∃ t : c.F, t ≠ 0 ∧ ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (t • ρ) := by
  first | exact @GlobalTheory.RuleIntegral.exists_smul_nonneg | exact GlobalTheory.RuleIntegral.exists_smul_nonneg | (intros; apply GlobalTheory.RuleIntegral.exists_smul_nonneg <;> assumption)
end
