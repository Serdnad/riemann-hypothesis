module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRMatFrom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle139
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FormSmulL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfCauchySchwarz
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RatioBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelOneSquareIntegrableGeneral
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle208
public import Formalism.HermitianCurvature.StatementHeads
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle197
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle179
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle027
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle204
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RRFin

theorem hasDerivAt_rotExp (m : ℂ) :
    HasDerivAt (fun φ : ℝ => Complex.exp (m * (φ : ℂ) * Complex.I)) (m * Complex.I) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul m).mul_const Complex.I).cexp
  simpa using h

end RRFin

open RRMat RRFin in
theorem rotation_finite_from_matrix : GTRRFinFrom := by
  intro hC hS hW Wp Wq _ _ _ _ _ _ P Bs hpl hk2 hsec e he hc n hn Rt s hRt ρ Φ
  have hB := SSTr.radBase P Bs hpl
  have hTT0 : 0 ≤ P.TT := by
    rw [← SSTr.tz_eq P Bs hpl]; exact mul_nonneg hB.2.2.2.1.le hB.2.2.2.2.1.le
  set E : M.Ty P → (Wq →L[ℂ] Wp) := fun σ => e σ 0 with hEdef
  have heE : ∀ σ ζ, e σ ζ = E σ := fun σ ζ => hc σ ζ 0
  have hid : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => w) (Ann P) := contDiff_id.contDiffOn
  have hstar : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => star w) (Ann P) :=
    by
      have h : (fun w : ℂ => star w) = ⇑Complex.conjCLE := by funext w; simp
      rw [h]; exact Complex.conjCLE.contDiff.contDiffOn
  apply Subtype.ext
  funext q
  simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, SetLike.val_smul, Pi.add_apply,
    Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [dzQ_apply P hTT0, dzbQ_apply P hTT0, fnZ_val P hid, fnZ_val P hstar]
  have hcq : q.1.1 ∈ OmX P.r := q.2.1
  have hζq : P.TT < Complex.normSq q.1.2 := q.2.2

  have hsm : ContDiffOn ℝ MA.sm (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) :=
    (trR P Bs e Φ ρ).2
  have hdiff : DifferentiableAt ℝ (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) q.1 :=
    (hsm.differentiableOn (by simp [MA.sm])).differentiableAt ((MA.Qset_open P.r P.TT).mem_nhds q.2)
  have hWa := hW P.r (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) q.1 hdiff

  have hfibq : ∀ φ : ℝ, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
      (NF.muZ P.k P.r Bs.μsec (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))) ∈
        NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) := by
    intro φ
    have hm := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB Φ.1 Φ.2
    have hx : ((q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
      ⟨hcq, by rw [normSq_rot]; exact ann_tz P Bs hpl hζq⟩
    have h2 := hm.2.1 _ hx
    simp only [NF.radR, Set.indicator_of_mem hx] at h2
    exact h2
  have hGy : ∀ φ : ℝ, inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
        (NF.muZ P.k P.r Bs.μsec q.1.2 * zc P.k P.r φ))) =
      Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) * inner ℂ (B.hsVec (E ρ)) (B.hsVec
        ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))))) := by
    intro φ
    have hζe : P.TT < Complex.normSq (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) := by rw [normSq_rot]; exact hζq
    have hexp := (he.2 _ hζe).2.2 _ (hfibq φ)
    simp only [heE] at hexp
    have hM : ∀ σ, inner ℂ (B.hsVec (E ρ)) (B.hsVec (rotA P Bs φ (E σ))) =
        if ρ = σ then Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) else 0 := fun σ => hn φ ρ σ
    rw [rot_eqv hS P Bs hpl hsec Φ q.1.1 hcq q.1.2 hζq φ]
    conv_lhs => rw [hexp]
    rw [rotA_sum, SSTr.hsVec_sum, inner_sum]
    simp only [VLem.hsV_smul, inner_smul_right, hM, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

  have hD : ((q.1.1, NF.muZ P.k P.r Bs.μsec q.1.2) : (Fin P.r → ℂ) × Q.Mx P.k P.r) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hB.2.1 hB.2.2.1 hB.2.2.2.2.2.1 (q := q.1) ⟨hcq, ann_tz P Bs hpl hζq⟩
  have hG := hasDerivAt_pair hC P Bs Φ _ hD (E ρ) 1
  simp only [one_mul] at hG
  have hE := hasDerivAt_rotExp (-(n ρ : ℂ))
  have hprod := (hE.mul hG).const_mul ((wR P.k P.TT q.1.2 : ℝ) : ℂ)
  have hpt : ∀ φ : ℝ, MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ) (q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) * (Complex.exp (-(n ρ : ℂ) * (φ : ℂ) * Complex.I) *
        inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
          (NF.muZ P.k P.r Bs.μsec q.1.2 * zc P.k P.r φ)))) := by
    intro φ
    have hmem : ((q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E P.r) ∈ MA.Qset P.r P.TT :=
      ⟨hcq, by rw [normSq_rot]; exact hζq⟩
    unfold MA.ext
    rw [dite_eq_left hmem, SSTr.trR_apply P Bs hpl hk2 e he]
    simp only [rawR]
    rw [wR_rot, heE, hGy φ, ← mul_assoc (Complex.exp (-(n ρ : ℂ) * (φ : ℂ) * Complex.I)), ← Complex.exp_add]
    have h0 : -(n ρ : ℂ) * (φ : ℂ) * Complex.I + (n ρ : ℂ) * (φ : ℂ) * Complex.I = 0 := by ring
    rw [h0, Complex.exp_zero, one_mul]
  have hF := hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall hpt)
  have heq := hWa.unique hF

  have hsum := hRt Φ _ hD
  simp only at hsum
  have hG0 := hGy 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul, mul_one] at hG0 heq
  rw [SSTr.trR_apply P Bs hpl hk2 e he, SSTr.trR_apply P Bs hpl hk2 e he]
  simp only [rawR]
  rw [hG0] at heq
  rw [heE, hsum, VLem.hsV_add, inner_add_right, VLem.hsV_smul, inner_smul_right]
  push_cast
  apply mul_left_cancel₀ Complex.I_ne_zero
  linear_combination -heq

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem toStd_append_blk (r : ℕ) (g : ℝ) (s : ℕ) (c : ℂ) : ∀ (h : C.LPt) (b : ℕ),
    D.toStd r g b (h ++ [(s, c)]) = D.toStd r g b h ++
      [(s, (((g / (2 * Real.pi)) ^ S6.nuBlock r ((b + D.ptSize h : ℕ) : ℤ) (s : ℤ) : ℝ) : ℂ) *
        Complex.I ^ (s - 1) * c)] := by
  intro h b
  induction h generalizing b with
  | nil => simp [D.toStd, D.ptSize]
  | cons blk rest ih =>
    obtain ⟨s', t⟩ := blk
    simp only [List.cons_append, D.toStd, ih (b + s'), D.ptSize, List.map_cons,
      List.sum_cons, add_assoc]

theorem slv_congr {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (i : ℕ) (hi : i ≤ r)
    (w : List C.Letter) {P P' : C.LPt} (e : P = P') (hP : D.ptSize P = i) (hP' : D.ptSize P' = i) :
    KB.slv T F i hi w P hP = KB.slv T F i hi w P' hP' := by
  subst e; rfl

theorem psd_shift {Y : Finset C.LPt} {k : C.LPt → C.LPt → ℂ} (blk : ℕ × ℂ)
    (hk : TB.PSDOn (Y.image fun h => h ++ [blk]) k) : TB.PSDOn Y fun p q => k (p ++ [blk]) (q ++ [blk]) := by
  have hinj : Set.InjOn (fun h : C.LPt => h ++ [blk]) Y := fun x _ y _ hxy => List.append_cancel_right hxy
  rw [PBA.psd_iff_qf] at hk ⊢
  obtain ⟨hh, hq⟩ := hk
  refine ⟨fun x hx y hy => hh _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy), fun c => ?_⟩
  have e : PBA.qf Y (fun p q => k (p ++ [blk]) (q ++ [blk])) c =
      PBA.qf (Y.image fun h => h ++ [blk]) k (fun z => c z.dropLast) := by
    unfold PBA.qf
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp
  rw [e]; exact hq _

section lam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def lamB (S : C.HidaSetting E Wp Wq) (b s : ℕ) : ℂ :=
  ((((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r (b : ℤ) (s : ℤ) : ℝ) : ℂ) * Complex.I ^ (s - 1)

theorem stdS_blk (S : C.HidaSetting E Wp Wq) (b s : ℕ) (hb : 1 ≤ b) (H : C.LPt) (hH : D.ptSize H = b - 1) (t : ℂ) :
    stdS S (H ++ [(s, t)]) = stdS S H ++ [(s, lamB S b s * t)] := by
  unfold stdS lamB
  rw [toStd_append_blk, hH, show 1 + (b - 1) = b by omega]

theorem norm_lamB (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s : ℕ) :
    ‖lamB S b s‖ = ((S.g : ℝ) / (2 * Real.pi)) ^ S6.nuBlock S.G.r (b : ℤ) (s : ℤ) := by
  unfold lamB
  rw [norm_mul, norm_pow, Complex.norm_I, one_pow, mul_one, Complex.norm_real, Real.norm_of_nonneg]
  exact zpow_nonneg (by positivity) _

theorem lamB_ne (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s : ℕ) : lamB S b s ≠ 0 := by
  intro h
  have := norm_lamB S hg b s
  rw [h, norm_zero] at this
  exact (zpow_pos (by positivity : (0 : ℝ) < (S.g : ℝ) / (2 * Real.pi)) _).ne this

end lam

section deg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem uB_blk (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (b s : ℕ) (hb : 1 ≤ b) (H : C.LPt) (hH : D.ptSize H = b - 1) (t : ℂ)
    (hP : D.IsLocPt (H ++ [(s, t)]) j) :
    ∃ hX : D.IsLocPt (stdS S H ++ [(s, lamB S b s * t)]) j,
      uB S p F v ε j hj w (H ++ [(s, t)]) = (((√(nnS S (H ++ [(s, t)])) / bS S (H ++ [(s, t)]) : ℝ) : ℂ)) •
        KB.slv (p v).T (F v ε) j hj w (stdS S H ++ [(s, lamB S b s * t)]) hX.2 := by
  have hgpos := g_pos_of_built hB
  have e := stdS_blk S b s hb H hH t
  have hX : D.IsLocPt (stdS S H ++ [(s, lamB S b s * t)]) j := by
    rw [← e]; exact (PBD.isLocPt_toStd_iff _ _ hgpos _ 1 j).2 hP
  refine ⟨hX, ?_⟩
  rw [uB_pos S p F v ε j hj w _ hP]
  congr 1
  exact slv_congr _ _ _ _ _ e _ _

theorem deg_uB_lift (hDL : KB.DegLift) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (b s : ℕ) (hb : 1 ≤ b) (a : List C.Letter) (K : ℕ)
    (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ) (hinj : ∀ c, Function.Injective (grid c))
    (H H' : C.LPt) (hH : D.ptSize H = b - 1) (hH' : D.ptSize H' = b - 1) (t t' : ℂ) :
    ((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
        (p v).form j hj a (uB S p F v ε j hj a (H ++ [(s, t)])) (uB S p F v ε j hj a (H' ++ [(s, t')])) =
      ∑ n : Fin K → Fin (2 * (j - s) + s + 1), ((∏ c, F7.lagCo (grid c) (n c) : ℝ) : ℂ) *
        KB.pairJ ((p v).form j hj a) (List.ofFn fun c => grid c (n c))
          (uB S p F v ε j hj (KB.plusW (List.ofFn fun c => grid c (n c)) a) (H ++ [(s, t)]))
          (uB S p F v ε j hj (KB.minusW (List.ofFn fun c => grid c (n c)) a) (H' ++ [(s, t')])) := by
  by_cases hloc : D.IsLocPt (H ++ [(s, t)]) j ∧ D.IsLocPt (H' ++ [(s, t')]) j
  · obtain ⟨hP, hP'⟩ := hloc
    obtain ⟨hX, eX⟩ := uB_blk hB F v ε j hj a b s hb H hH t hP
    obtain ⟨hX', eX'⟩ := uB_blk hB F v ε j hj a b s hb H' hH' t' hP'
    have hdeg := hDL (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) (F v ε) j s hj a (stdS S H) (stdS S H')
      (lamB S b s * t) (lamB S b s * t') hX hX' K grid (hF v ε hε) hinj
    rw [rr_eq_form (p v) (F v ε) j hj a _ _ hX hX'] at hdeg
    set Dh : ℂ := (((√(nnS S (H ++ [(s, t)])) / bS S (H ++ [(s, t)]) : ℝ) : ℂ)) with hDh
    set Dh' : ℂ := (((√(nnS S (H' ++ [(s, t')])) / bS S (H' ++ [(s, t')]) : ℝ) : ℂ)) with hDh'
    obtain ⟨ε2, hε2, hs, hs'⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj a _ hX)
      (slv_nv (p v) (hF v ε hε) j hj a _ hX')
    rw [eX, eX', form_smul_l (p v) j hj a _ _ _ hs (nv_smul _ hs'), form_smul_r (p v) j hj a _ _ _ hs hs']
    have hL : ((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
        (Dh * (conj Dh' * (p v).form j hj a (KB.slv (p v).T (F v ε) j hj a _ hX.2)
          (KB.slv (p v).T (F v ε) j hj a _ hX'.2))) =
        Dh * conj Dh' * (((-1) ^ (s - 1) * ((lamB S b s * t)⁻¹ - (lamB S b s * t')⁻¹)) ^ K *
          (p v).form j hj a (KB.slv (p v).T (F v ε) j hj a _ hX.2) (KB.slv (p v).T (F v ε) j hj a _ hX'.2)) := by
      ring
    rw [hL, hdeg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    set ys := List.ofFn fun c => grid c (n c) with hys
    obtain ⟨hXp, eXp⟩ := uB_blk hB F v ε j hj (KB.plusW ys a) b s hb H hH t hP
    obtain ⟨hXm, eXm⟩ := uB_blk hB F v ε j hj (KB.minusW ys a) b s hb H' hH' t' hP'
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (slv_nv (p v) (hF v ε hε) j hj (KB.plusW ys a) _ hX)
      (slv_nv (p v) (hF v ε hε) j hj (KB.minusW ys a) _ hX')
    rw [eXp, eXm, pj_smul (p v) j hj a ys _ _ _ _ hp hm]
    ring
  · have h0 : ∀ w : List C.Letter, uB S p F v ε j hj w (H ++ [(s, t)]) = 0 ∨
        uB S p F v ε j hj w (H' ++ [(s, t')]) = 0 := by
      intro w
      by_cases hh : D.IsLocPt (H ++ [(s, t)]) j
      · exact Or.inr (uB_neg S p F v ε j hj w _ fun hh' => hloc ⟨hh, hh'⟩)
      · exact Or.inl (uB_neg S p F v ε j hj w _ hh)
    obtain ⟨ε1, hε1, hx, hx'⟩ := nv_pair (uB_nv hB F hF v ε hε j hj a (H ++ [(s, t)]))
      (uB_nv hB F hF v ε hε j hj a (H' ++ [(s, t')]))
    have lhs0 : (p v).form j hj a (uB S p F v ε j hj a (H ++ [(s, t)])) (uB S p F v ε j hj a (H' ++ [(s, t')])) = 0 := by
      rcases h0 a with h0 | h0
      · rw [h0, form_zero_l (p v) j hj a _ hx']
      · rw [h0, form_zero_r (p v) j hj a _ hx]
    rw [lhs0, mul_zero]
    symm
    refine Finset.sum_eq_zero fun n _ => ?_
    set ys := List.ofFn fun c => grid c (n c) with hys
    obtain ⟨ε3, hε3, hp, hm⟩ := nv_pair (uB_nv hB F hF v ε hε j hj (KB.plusW ys a) (H ++ [(s, t)]))
      (uB_nv hB F hF v ε hε j hj (KB.minusW ys a) (H' ++ [(s, t')]))
    by_cases hh : D.IsLocPt (H ++ [(s, t)]) j
    · rw [uB_neg S p F v ε j hj (KB.minusW ys a) _ fun hh' => hloc ⟨hh, hh'⟩, pj_zero_r (p v) j hj a ys _ hp, mul_zero]
    · rw [uB_neg S p F v ε j hj (KB.plusW ys a) _ hh, pj_zero_l (p v) j hj a ys _ hm, mul_zero]

end deg

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
end

section

open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Tr

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem fs_tr (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (t : ℂ)
    {zi zi' : Fin (2 * (r - l.succ) + k + 1) → ℂ} {πi : Mx k (r - l.succ) → (Wp →L[ℂ] Wp)}
    {πi' : Mx k (r - l.succ) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - l.succ)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - l.succ) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' =
      (κ : ℂ) * pairAt μ Φ Ψ (glue l.succ (Function.update c l t) (Formalism.FourierDecayAlt.P.PTie.shiftCf l.succ c'')))
    (Φ Ψ : RadSp k r z z' π π') :
    fs μ l Φ Ψ c t = (κ : ℂ)⁻¹ * ∫ c'' : Cf (r - l.succ) 0, wtI 0 c'' *
      pairAt μi (T Φ) (T Ψ) (glue 0 (shiftV l.succ (Function.update c l t)) c'') := by
  have hjl : (0 : Fin (r - l.succ + 1)).val + l.succ.val = l.succ.val := by simp
  have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  unfold fs
  rw [← (shEqJ_mp l.succ l.succ 0 hjl).integral_comp', ← integral_const_mul]
  congr 1; funext c''
  rw [wtI_shEqJ, glue_shEqJ l.succ l.succ 0 hjl (Function.update c l t) (Function.update c l t) (fun _ _ => rfl), hT]
  field_simp

theorem level_one_square_integrable_of_transport (μ : Measure (Mt k r)) (l : Fin r) (c : Fin r → ℂ) (t : ℂ)
    {zi zi' : Fin (2 * (r - l.succ) + k + 1) → ℂ} {πi : Mx k (r - l.succ) → (Wp →L[ℂ] Wp)}
    {πi' : Mx k (r - l.succ) → (Wq →L[ℂ] Wq)} (μi : Measure (Mt k (r - l.succ)))
    (T : RadSp k r z z' π π' →ₗ[ℂ] RadSp k (r - l.succ) zi zi' πi πi') (κ : ℝ) (hκ : 0 < κ)
    (hT : ∀ Φ Ψ c'', pairAt μi (T Φ) (T Ψ) c'' =
      (κ : ℂ) * pairAt μ Φ Ψ (glue l.succ (Function.update c l t) (Formalism.FourierDecayAlt.P.PTie.shiftCf l.succ c'')))
    (Φ : RadSp k r z z' π π') (c₀ : Fin (r - l.succ) → ℂ) (h : LevelSquareIntegrable μi 0 (T Φ) c₀) :
    LevelSquareIntegrable μ l.succ Φ (Function.update c l t) :=
  level_square_integrable_of_transport μ l.succ (Function.update c l t) μi T κ hκ hT Φ c₀ h

end Tr

end Formalism.FourierDecayAlt.P5.HerD
end
end

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section read

variable {k : ℕ}

theorem pic_read {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n ρ : ℕ} (hn : 1 + ρ = n)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn (liftVec k 1 ρ zs'))
    (Φ : Fn k n E) (J : Mx k n → E)
    (hΦ : ∀ x ∈ DomR k n z z', Φ x.1 x.2 = resG k n (Fin.last n) J x.1 x.2)
    {t : ℂ} (ht : t ≠ 0) (y : (Fin ρ → ℂ) × Mx k ρ) (hy : y ∈ DomR k ρ zs zs') :
    Φ (fun l => PBH.consC t y.1 (Fin.cast hn.symm l)) (D.castM hn (ιLev k 1 ρ y.2)) =
      ((‖t‖ ^ (2 * n + k) : ℝ) : ℂ) •
        resG k ρ (Fin.last ρ) (fun γ => J (D.castM hn (U.mMap k 1 ρ (Matrix.of fun _ _ => t) γ))) y.1 y.2 := by
  subst hn
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  simp only [Fin.cast_eq_self, Formalism.FourierDecayAlt.P.Dx2.MN.castM_rfl]
  rw [hΦ _ ((PBH.domR_iota ht zs zs' y.1 y.2).2 hy)]
  exact resG_consC ht J y.1 y.2

end read

def HeadPicNil : Prop :=
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j)
    (L : R.LevelData (Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')) (JC.parLev P j).r)
    (Φ : Wd.Ix (Fin ([] : List C.Letter).length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
    KB.CptCoef p.T.base F →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Φ e) (KB.slv p.T F j (by omega) [] h hh.2 e)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin ([] : List C.Letter).length)),
    ∀ y ∈ Q.DomR P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z',
      (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted [])) Φ e :
          Q.Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp))
        (fun l => PBH.consC t y.1 (Fin.cast (by change P.r - j = 1 + (P.r - (j + 1)); omega) l))
          (D.castM (by change 1 + (P.r - (j + 1)) = P.r - j; omega) (ιLev P.k 1 (P.r - (j + 1)) y.2)) =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) •
          Q.resG P.k (P.r - (j + 1)) (Fin.last _)
            (B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj [] (h ++ [(1, t)]) ht.2 e)) y.1 y.2

theorem headPic_nil (hS : KB.SliceStep) : HeadPicNil := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h hh L Φ hF hΦ t ht e y hy
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hn : 1 + (P.r - (j + 1)) = P.r - j := by omega

  have hact : P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted [])) Φ = Φ :=
    Formalism.FourierDecayAlt.P.PBF.polyAction_one₂ Φ
  rw [hact]
  have hread := pic_read (k := P.k) hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj)
    (Subtype.val (Φ e)) (B.JF (p.T.bs j) (KB.slv p.T F j (by omega) [] h hh.2 e))
    (hΦ e) ht0 y hy
  refine hread.trans ?_
  congr 1
  unfold resG
  congr 1
  have hc : ∀ a, y.1 a ≠ 0 := hy.1
  have hγ := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV (i := Fin.last _) hc hy.2.1
  have hΩ := Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus (p.T.bs (j + 1)).z_mem (p.T.bs (j + 1)).z'_mem hy.1 hy.2.1 hy.2.2
  have he : e = fun a => a.elim0 := funext fun a => a.elim0
  subst he
  exact (hS Wp Wq P p F j hj h t hh ht hF _ hγ hΩ).symm

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

theorem head_picture_empty_word : PBP.HeadPicNil := PBP.headPic_nil slice_induction_level

end Formalism.FourierDecayAlt.P
end
end
