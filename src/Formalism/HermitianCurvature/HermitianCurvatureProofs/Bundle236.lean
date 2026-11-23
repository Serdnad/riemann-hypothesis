module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle060
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfChoices
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutIntervalLong
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle232
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGWave
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

def SiteOpsWaveJC : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ (l : Fin P.r), l.val = 0 →
    ∀ (j : Fin 6), (j = 1 ∨ j = 4) →
    ∀ (Φ : RadSp P.k P.r z z' π π'), Φ ∈ waveJ P z z' π π' D l → X.op l j Φ ∈ waveJ P z z' π π' D l

namespace SiteC

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem jf_mul_inv (Bs : B.RealPlaceData k r Wp Wq) (ι : B.Mat k r → ℂ)
    (hι : ∀ p : B.SS k r, Bs.inSS p → ∀ g, ι (B.sgs p g) = ι g) (G : B.Mat k r → (Wq →L[ℂ] Wp))
    (h : B.Mat k r) : B.JF Bs (fun g => ι g • G g) h = ι h • B.JF Bs G h := by
  unfold B.JF besselJ
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [B7.ae_inSS Bs] with p hp
  have hp' := hι p hp h
  simp only [B.sgs] at hp'
  simp only [hp', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm (ι h)]

theorem first_minor_double_coset_invariant (Bs : B.RealPlaceData k r Wp Wq) (p : B.SS k r) (hp : Bs.inSS p) (g : B.Mat k r) :
    Dmin k r Bs.z Bs.z' (B.sgs p g) ⟨1, by omega⟩ = Dmin k r Bs.z Bs.z' g ⟨1, by omega⟩ :=
  Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g _

private theorem dmin_one_eq_herm_mulVec_fvec {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Dmin k r z z' g ⟨1, by omega⟩ = herm (Hpk k r) (g *ᵥ fvec k r z' 0) (fvec k r z 0) := by
  unfold Dmin
  erw [Matrix.det_fin_one]
  rfl

theorem first_minor_good_function (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) :
    Formalism.FourierDecayAlt.P.JCx2.mnGood Bs ε (fun g => Dmin k r Bs.z Bs.z' g ⟨1, by omega⟩) := by
  refine JCx2.mn_good_congr (c := fun g => herm (Hpk k r) (g *ᵥ fvec k r Bs.z' 0) (fvec k r Bs.z 0)) ?_
    (JCx2.mn_good_herm _ _)
  intro g _
  rw [dmin_one_eq_herm_mulVec_fvec]

theorem first_minor_conj_good_function (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) :
    Formalism.FourierDecayAlt.P.JCx2.mnGood Bs ε (fun g => star (Dmin k r Bs.z Bs.z' g ⟨1, by omega⟩)) := by
  refine JCx2.mn_good_congr
    (c := fun g => (Complex.conjCLE.toContinuousLinearMap.comp
      (JCx2.mnLinHerm (k := k) (r := r) (fvec k r Bs.z' 0) (fvec k r Bs.z 0))) g) ?_
    (JCx2.mn_good_lin _)
  intro g _
  rw [dmin_one_eq_herm_mulVec_fvec]
  simp [JCx2.mnLinHerm]

private theorem wCell_succ_mulVec_bvec_eI_zero_eq_smul {k r : ℕ} (hr : 0 < r) (c : Fin r → ℂ) :
    ∀ (i : ℕ) (hi : i < r), wCell k r ⟨i + 1, by omega⟩ c *ᵥ bvec (eI k r ⟨0, hr⟩) =
      c ⟨0, hr⟩ • bvec (esI k r ⟨0, hr⟩) := by
  intro i
  induction i with
  | zero =>
    intro hi
    have h := Qx6.wCell_succ (k := k) (⟨0, hr⟩ : Fin r) c
    simp only [Fin.succ_mk, Fin.castSucc_mk, Fin.mk_zero, Qx6.wCell_zero, one_mul] at h
    rw [h, Qx4.w1_mulVec_bvec_eI]
  | succ n ih =>
    intro hi
    have h := Qx6.wCell_succ (k := k) (⟨n + 1, hi⟩ : Fin r) c
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h
    have h1 : eI k r ⟨0, hr⟩ ≠ eI k r ⟨n + 1, hi⟩ := by
      simp [eI, Fin.ext_iff]
    have h2 : eI k r ⟨0, hr⟩ ≠ esI k r ⟨n + 1, hi⟩ := by
      simp [eI, esI, Fin.ext_iff]; omega
    rw [h, ← Matrix.mulVec_mulVec, Qx3.reflection_fixes_basis_vector _ _ h1 h2, ih (by omega)]

theorem first_minor_at_cell_eq_coefficient {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hr : 0 < r)
    (c : Fin r → ℂ) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨1, by omega⟩ = c ⟨0, hr⟩ := by
  rw [dmin_one_eq_herm_mulVec_fvec]
  have hf : ∀ w : Fin (2 * r + k + 1) → ℂ, fvec k r w 0 = bvec (eI k r ⟨0, hr⟩) := by
    intro w; simp [fvec, hr]
  rw [hf, hf, ← Matrix.mulVec_mulVec, (hg.2 ⟨0, hr⟩ (by simp; omega)).1]
  have h3 := wCell_succ_mulVec_bvec_eI_zero_eq_smul (k := k) hr c (r - 1) (by omega)
  have e : (⟨r - 1 + 1, by omega⟩ : Fin (r + 1)) = Fin.last r := by ext; simp; omega
  rw [e] at h3
  rw [h3]
  simp only [herm, bvec, eI, esI]
  simp
  rw [Matrix.mulVec_smul, Pi.smul_apply, Matrix.mulVec_single_one]
  simp [Hpk, hr]

end SiteC

open SiteC in
theorem site_operators_preserve_orbital : SiteOpsWaveJC := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D _ _ _ hz hz' hπ hπ' l hl j hj Φ hΦ
  subst hz hz' hπ hπ'
  have hr : 0 < P.r := by have := l.2; omega
  have hl' : l = ⟨0, hr⟩ := Fin.ext hl
  have key : ∀ Ψ, IsWaveJ P D.z D.z' D.π D.π' D l Ψ → IsWaveJ P D.z D.z' D.π D.π' D l (X.op l j Ψ) := by
    rintro Ψ ⟨hlc, s, ε, G, hε, hG, hΨ⟩
    rcases hj with rfl | rfl
    · refine ⟨?_, s, ε, fun g => Dmin P.k P.r D.z D.z' g ⟨1, by omega⟩ • G g, hε, first_minor_good_function D ε G hG, ?_⟩
      · intro c hc
        obtain ⟨U, hU, hcU, K, hK, hKs, hv⟩ := hlc c hc
        refine ⟨U, hU, hcU, K, hK, hKs, fun c' hc' g hg hgK => ?_⟩
        rw [X.op_apply]
        simp [crd, opL, cOp, hv c' hc' g hg hgK]
      · intro y hy
        rw [X.op_apply]
        simp only [crd, opL, cOp]
        rw [hΨ y hy]
        simp only [resG]
        rw [jf_mul_inv D _ (fun p hp g => BigCellZetaMinors.dmin_sgs D hp g _) G,
          first_minor_at_cell_eq_coefficient D.z_mem D.z'_mem hr y.1 hy.2.1, hl']
        simp only [smul_smul]
        ring_nf
    · refine ⟨?_, s, ε, fun g => star (Dmin P.k P.r D.z D.z' g ⟨1, by omega⟩) • G g, hε, first_minor_conj_good_function D ε G hG, ?_⟩
      · intro c hc
        obtain ⟨U, hU, hcU, K, hK, hKs, hv⟩ := hlc c hc
        refine ⟨U, hU, hcU, K, hK, hKs, fun c' hc' g hg hgK => ?_⟩
        rw [X.op_apply]
        simp [crd, opL, cbOp, hv c' hc' g hg hgK]
      · intro y hy
        rw [X.op_apply]
        simp only [crd, opL, cbOp]
        rw [hΨ y hy]
        simp only [resG]
        rw [jf_mul_inv D _ (fun p hp g => by rw [BigCellZetaMinors.dmin_sgs D hp g _]) G,
          first_minor_at_cell_eq_coefficient D.z_mem D.z'_mem hr y.1 hy.2.1, hl']
        simp only [smul_smul]
        ring_nf
  refine Submodule.span_induction (p := fun Φ _ => X.op l j Φ ∈ waveJ P D.z D.z' D.π D.π' D l) ?_ ?_ ?_ ?_ hΦ
  · intro x hx
    exact Submodule.subset_span (key x hx)
  · simp
  · intro x y _ _ hx hy
    rw [map_add (f := _)]
    exact add_mem hx hy
  · intro a x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

theorem site_multiplication_orbital : SiteMulWaveJ := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl Φ hΦ
  exact ⟨site_operators_preserve_orbital Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl 1 (Or.inl rfl) Φ hΦ,
    site_operators_preserve_orbital Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl 4 (Or.inr rfl) Φ hΦ⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section C2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem blockK_waveC (hA : P5.ThmPActualCpt) (hPSC : StandardPairingDecay.PStdC) (hDW : KB.DegWave) (hSS : KB.SizeStdCpt)
    (hVI : KB.VIsoCpt) (hFP : FormPosCpt) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (a : List C.Letter) (ha : D.AdmAt S v a) (haN : a.length ≤ S.Ntop)
    (hwa : KB.CutWord (D.parOf S v) (S.l + 1) a) (K : ℕ) (grid : Fin K → Fin (2 * j + 1) → ℝ)
    (hinj : ∀ b, Function.Injective (grid b))
    (hnodes : ∀ n : Fin K → Fin (2 * j + 1),
        D.AdmAt S v (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        D.AdmAt S v (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.plusW (List.ofFn fun b => grid b (n b)) a) ∧
        KB.CutWord (D.parOf S v) (S.l + 1) (KB.minusW (List.ofFn fun b => grid b (n b)) a) ∧
        (List.ofFn fun b => grid b (n b)).Pairwise (fun y y' => 2 < |y - y'|) ∧
        ∀ y ∈ (List.ofFn fun b => grid b (n b)), NodeOK S v a (decide (j = 0)) y)
    (Xc : ℝ) (hXc0 : 0 ≤ Xc)
    (hXc : (∏ b, ∑ i, |F7.lagCo (grid b) i|) * (((S.g : ℝ) * lamS S j) / (2 * Real.pi)) ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l (decide (j = 0)) (S.pl v)) ^ K ≤ Xc ^ K)
    (l : ℂ) (Y : Finset C.LPt) (hY : ∀ h ∈ Y, D.ptSize h = j) :
    KB.BlockPSD Y Y
      (fun p' q' => ((Xc ^ K : ℝ) : ℂ) * ∑ n : Fin K → Fin (2 * j + 1), (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε j (KB.plusW (List.ofFn fun b => grid b (n b)) a) p' q')
      (fun p' q' => Complex.I ^ K * l ^ K * KB.hatB (setC S p F) v ε (j + 1) 1 a l p' q')
      (fun p' q' => ((Xc ^ K : ℝ) : ℂ) * ∑ n : Fin K → Fin (2 * j + 1), (F7.thGrid grid n : ℂ) *
        KB.gN (setC S p F) v ε j (KB.minusW (List.ofFn fun b => grid b (n b)) a) p' q') := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hgpos := g_pos_of_built hB
  have hlam := lamS_pos S hgpos j
  have hΓ := gam_pos hB j
  have hsa := sizeAt_pos S hGo v a ha
  set T : ℝ := ((S.g : ℝ) * lamS S j) / (2 * Real.pi) with hT
  have hT0 : 0 < T := by positivity
  set t : ℝ := 2 * Real.pi / ((S.g : ℝ) * lamS S j) with ht
  have htT : t * T = 1 := by rw [ht, hT]; field_simp
  set s := sW S j l with hs
  set c0 : ℝ := 1 / (ΓS S j * S.sizeAt v a) with hc0
  set ys : (Fin K → Fin (2 * j + 1)) → List ℝ := fun n => List.ofFn fun b => grid b (n b) with hys
  set Λ : ℝ := ∏ b, ∑ i, |F7.lagCo (grid b) i| with hΛ
  set θ : (Fin K → Fin (2 * j + 1)) → ℝ := fun n => F7.thGrid grid n with hθ
  set lag : (Fin K → Fin (2 * j + 1)) → ℝ := fun n => ∏ b, F7.lagCo (grid b) (n b) with hlag
  set S' := setC S p F with hS'

  set Pn : (Fin K → Fin (2 * j + 1)) → C.LPt → C.LPt → ℂ := fun n p' q' =>
    (((lag n / θ n) * T ^ K * c0 : ℝ) : ℂ) * KB.pairJ ((p v).form j hj a) (ys n)
      (KB.waveG ((p v).T.bs j) s _ (uY S p F v ε j hj (KB.plusW (ys n) a) Y p'))
      (uY S p F v ε j hj (KB.minusW (ys n) a) Y q') with hPn
  have hCS : ∀ n (c d : C.LPt → ℂ), ‖∑ p' ∈ Y, ∑ q' ∈ Y, c p' * conj (d q') * Pn n p' q'‖ ^ 2 ≤
      (Xc ^ K) ^ 2 * ((∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') * KB.gN S' v ε j (KB.plusW (ys n) a) p' p'').re *
        (∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') * KB.gN S' v ε j (KB.minusW (ys n) a) q' q'').re) := by
    intro n c d
    obtain ⟨hAp, hAm, hCp, hCm, hpw, hnd⟩ := hnodes n
    have hCp' : KB.CutWord (D.parOf S v) (p v).l0 (KB.plusW (ys n) a) := by rw [hl0]; exact hCp
    have hCm' : KB.CutWord (D.parOf S v) (p v).l0 (KB.minusW (ys n) a) := by rw [hl0]; exact hCm
    obtain ⟨hqpos, hcs⟩ := hSS hA (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (p v) j hj a (ys n) hCp' hCm' hpw
    set qv : ℝ → ℝ := fun y => (Wd.qw (M.qC (D.parOf S v)) (D.positionted a) (y : ℂ)).re with hqv
    set Q : ℝ := ((ys n).map qv).prod with hQd
    have hQ : 0 < Q := List.prod_pos fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact hqpos y hy
    have hsp := sizeAt_pos S hGo v _ hAp
    have hsm := sizeAt_pos S hGo v _ hAm
    set cp : ℝ := 1 / (ΓS S j * S.sizeAt v (KB.plusW (ys n) a)) with hcp
    set cm : ℝ := 1 / (ΓS S j * S.sizeAt v (KB.minusW (ys n) a)) with hcm
    have hcp0 : 0 < cp := by positivity
    have hcm0 : 0 < cm := by positivity
    set κ : ℂ := (((lag n / θ n) * T ^ K * c0 : ℝ) : ℂ) with hκ
    have hc := cs_choice (CV ((p v).T.bs j) (S := Fin (KB.plusW (ys n) a).length))
      (CV ((p v).T.bs j) (S := Fin (KB.minusW (ys n) a).length))
      ((p v).form j hj (KB.plusW (ys n) a)) ((p v).form j hj (KB.minusW (ys n) a))
      (KB.pairJ ((p v).form j hj a) (ys n))
      cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
      cv_zero (fun x y hx hy => cv_add hx hy) (fun c x hx => cv_smul c hx)
      (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj _ x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj _ x y₁ y₂ c hx h₁ h₂)
      (fun x₁ x₂ y c h₁ h₂ hy => form_slC (p v) j hj _ x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => form_srC (p v) j hj _ x y₁ y₂ c hx h₁ h₂)
      (fun x₁ x₂ y c h₁ h₂ hy => pj_slC (p v) j hj a (ys n) x₁ x₂ y c h₁ h₂ hy)
      (fun x y₁ y₂ c hx h₁ h₂ => pj_srC (p v) j hj a (ys n) x y₁ y₂ c hx h₁ h₂)
      (KB.waveG ((p v).T.bs j) s (KB.plusW (ys n) a))
      (fun x hx => (hVI hA _ _ (D.parOf S v) (p v) j hj _ hCp' s x x hx hx).1)
      (fun x y c _ _ => PBG.waveG_add_smul _ s _ x y c)
      (fun x y hx hy => (hVI hA _ _ (D.parOf S v) (p v) j hj _ hCp' s x y hx hy).2)
      Q hQ (fun x y hx hy => hcs x y hx hy) Y (uY S p F v ε j hj (KB.plusW (ys n) a) Y)
      (uY S p F v ε j hj (KB.minusW (ys n) a) Y) (fun h => uY_cv hB F hF v ε hε j hj _ Y h)
      (fun h => uY_cv hB F hF v ε hε j hj _ Y h) κ cp cm hcp0 hcm0 c d

    have eA : ∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') * KB.gN S' v ε j (KB.plusW (ys n) a) p' p'' =
        ∑ p' ∈ Y, ∑ p'' ∈ Y, c p' * conj (c p'') * ((cp : ℂ) * (p v).form j hj (KB.plusW (ys n) a)
          (uY S p F v ε j hj (KB.plusW (ys n) a) Y p') (uY S p F v ε j hj (KB.plusW (ys n) a) Y p'')) := by
      refine Finset.sum_congr rfl fun p' hp' => Finset.sum_congr rfl fun p'' hp'' => ?_
      rw [uY_mem S p F v ε j hj _ Y p' hp', uY_mem S p F v ε j hj _ Y p'' hp'', gN_uB hB F hF v ε hε j hj _ p' p'']
    have eB : ∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') * KB.gN S' v ε j (KB.minusW (ys n) a) q' q'' =
        ∑ q' ∈ Y, ∑ q'' ∈ Y, d q' * conj (d q'') * ((cm : ℂ) * (p v).form j hj (KB.minusW (ys n) a)
          (uY S p F v ε j hj (KB.minusW (ys n) a) Y q') (uY S p F v ε j hj (KB.minusW (ys n) a) Y q'')) := by
      refine Finset.sum_congr rfl fun p' hp' => Finset.sum_congr rfl fun p'' hp'' => ?_
      rw [uY_mem S p F v ε j hj _ Y p' hp', uY_mem S p F v ε j hj _ Y p'' hp'', gN_uB hB F hF v ε hε j hj _ p' p'']
    have hnnA := quad_nonneg (gN_psdC hA hFP hB F hF v ε hε j hj _ hCp Y) c
    have hnnB := quad_nonneg (gN_psdC hA hFP hB F hF v ε hε j hj _ hCm Y) d
    rw [eA] at hnnA ⊢
    rw [eB] at hnnB ⊢
    refine hc.trans (mul_le_mul_of_nonneg_right ?_ (mul_nonneg hnnA hnnB))

    have hg1 := hB.1
    have hg2 := hB.2.1
    have hGg : 0 < S.G.g := by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2
    have hGk : 0 < S.G.ka := by
      unfold Sz.Glob.ka; rw [S.hv]; have := PBD.rd_pos' E; positivity
    have hsA := supA_nonneg S hGg hGk v (decide (j = 0))
    have hmem : ∀ b, grid b (n b) ∈ ys n := fun b => List.mem_ofFn.2 ⟨b, rfl⟩
    have hPne : ∀ b, S.P v (grid b (n b)) ≠ 0 ∧ S.P v (grid b (n b) + 1) ≠ 0 := by
      intro b
      have hgr : (∃ a', grid b (n b) ∈ S.grid v a') ∨ grid b (n b) ∈ S.grid1 v := by
        rcases hnd _ (hmem b) with ⟨-, a', -, -, h⟩ | ⟨-, h, -⟩
        · exact Or.inl ⟨a', h⟩
        · exact Or.inr h
      obtain ⟨-, -, h1, h2⟩ := (hGo v).2.2.2.2.2 _ hgr
      exact ⟨h1, h2⟩
    have hnorm : ‖κ‖ = Λ * T ^ K * (1 / (ΓS S j * S.sizeAt v a)) := by
      rw [hκ, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_pos (lam_div_theta grid hinj n).1,
        (lam_div_theta grid hinj n).2, abs_of_nonneg (pow_nonneg hT0.le K), abs_of_nonneg (by positivity : (0:ℝ) ≤ c0)]
    rw [hnorm, hQd, hcp, hcm, sizeAt_plusW, sizeAt_minusW, prod_ofFn_map, prod_ofFn_map, prod_ofFn_map]
    exact ratio_bound (fun b => grid b (n b)) (S.P v) qv Λ T (ΓS S j) (S.sizeAt v a)
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l (decide (j = 0)) (S.pl v)) Xc hΓ hsa
      (fun b => hqpos _ (hmem b)) (fun b => (hPne b).1) (fun b => (hPne b).2)
      (fun b => (node_bound hB v a ha haN _ _ (hnd _ (hmem b))).2)
      (Finset.prod_nonneg fun b _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hT0.le
      (mul_nonneg (Real.exp_pos 1).le hsA) hXc
  have hblock := block_of_choices Y (fun n => KB.gN S' v ε j (KB.plusW (ys n) a))
    (fun n => KB.gN S' v ε j (KB.minusW (ys n) a)) Pn θ (Xc ^ K) (Xc ^ K)
    (fun n => (lam_div_theta grid hinj n).1.le)
    (fun n => gN_psdC hA hFP hB F hF v ε hε j hj _ (hnodes n).2.2.1 Y)
    (fun n => gN_psdC hA hFP hB F hF v ε hε j hj _ (hnodes n).2.2.2.1 Y)
    (pow_nonneg hXc0 K) le_rfl hCS
  refine blockPSD_congr (fun _ _ _ _ => rfl) (fun p' hp' q' hq' => ?_) (fun _ _ _ _ => rfl) hblock

  show ∑ n, (θ n : ℂ) * Pn n p' q' = Complex.I ^ K * l ^ K * KB.hatB S' v ε (j + 1) 1 a l p' q'
  rw [hatB_uB_C hPSC hB F hF v ε hε j hj a hwa l p' q' (hY p' hp') (hY q' hq')]
  have hdeg := deg_uB hDW hB F hF v ε hε j hj a K grid hinj s p' q'
  have hIl : Complex.I ^ K * l ^ K = ((T ^ K : ℝ) : ℂ) * s ^ K := by
    rw [hs, sW_eq, mul_pow, mul_pow, ← mul_assoc, ← mul_assoc]
    have : ((T ^ K : ℝ) : ℂ) * (t : ℂ) ^ K = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← mul_pow, mul_comm T t, htT, one_pow, Complex.ofReal_one]
    linear_combination (Complex.I ^ K * l ^ K) * this.symm
  have e1 : Complex.I ^ K * l ^ K * ((c0 : ℂ) * (p v).form j hj a
      (KB.waveG ((p v).T.bs j) s a (uB S p F v ε j hj a p')) (uB S p F v ε j hj a q')) =
      ((T ^ K * c0 : ℝ) : ℂ) * (s ^ K * (p v).form j hj a
      (KB.waveG ((p v).T.bs j) s a (uB S p F v ε j hj a p')) (uB S p F v ε j hj a q')) := by
    rw [hIl]; push_cast; ring
  rw [show (((1 / (ΓS S j * S.sizeAt v a)) : ℝ) : ℂ) = (c0 : ℂ) from rfl, e1, hdeg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hth := (lam_div_theta grid hinj n).1
  have hθ0 : ((F7.thGrid grid n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hth.ne'
  simp only [hPn, uY_mem S p F v ε j hj _ Y p' hp', uY_mem S p F v ε j hj _ Y q' hq', hlag, hθ]
  push_cast
  field_simp
  ring

end C2

end

end Formalism.FourierDecayAlt.P.PBL
end
