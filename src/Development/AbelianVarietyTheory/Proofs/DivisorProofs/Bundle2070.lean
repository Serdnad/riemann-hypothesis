module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1950
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle309
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionGradedIsotropicFlag
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle319
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.BotPairSmall.CvEig

variable {D : D7}

theorem norm_eq_one_of_modulusOneAll {c : ℂ} (h : Mod1All c) : ‖c‖ = 1 := by
  obtain ⟨hx, h2⟩ := h
  simpa using h2 Qbar.val

theorem int_of_inc {b : D.host.E} (hb : inc D b ∈ OhE D) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = b := by
  have h := (VacMove.moves_one D 1 (fun _ => b)).2 (fun i => by simpa using hb)
  simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at h
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h 0)
  exact ⟨o, ho⟩

theorem exists_nat_clear {N : ℕ} (P : Matrix (Fin N) (Fin N) (AE D)) :
    ∃ n : ℕ, 0 < n ∧ ∀ s : Fin N → AE D, (∀ j, s j ∈ OhE D) →
      ∀ i, P.mulVec (fun j => (n : AE D) * s j) i ∈ OhE D := by
  obtain ⟨n, hn, hP⟩ := VacMove.exists_mat_denom P
  refine ⟨n, hn, fun s hs i => ?_⟩
  simp only [Matrix.mulVec, dotProduct]
  refine sum_mem fun j _ => ?_
  have : P i j * ((n : AE D) * s j) = ((n : AE D) * P i j) * s j := by ring
  rw [this]
  exact mul_mem (hP i j) (hs j)

end GlobalTheory.BotPairSmall.CvEig

namespace GlobalTheory.BotPairSmall.CvEig

variable {D : D7}

theorem lam_int_mul {N : ℕ} (𝔫 : Ideal (𝓞 D.host.E)) {h : GL (Fin N) (AE D)}
    (hL : Moves D h (skewLat D 𝔫 N)) {k : Matrix (Fin N) (Fin N) (AE D)} (hk : ∀ i j, k i j ∈ OhE D)
    (u : Fin N → AE D)
    (hu : ∀ i, (((h⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))).mulVec u i ∈ OhE D) :
    ∀ i, (((h⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))).mulVec (k.mulVec u) i ∈ OhE D := by
  obtain ⟨n, hn, hcl⟩ := exists_nat_clear (((h⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)))
  obtain ⟨M, hM, hMs⟩ := GlobalTheory.FunObj.CosetTT.skewLat_smul (D := D) 𝔫 N
  choose y s hs e using fun j => GlobalTheory.TrueTheta.approx D (u j) hn
  have hy : y ∈ skewLat D 𝔫 N := by
    rw [hL y]
    intro i
    have : (fun j => inc D (y j)) = u + fun j => (n : AE D) * s j := funext fun j => e j
    rw [this, Matrix.mulVec_add]
    exact add_mem (hu i) (hcl s hs i)
  choose b t ht eb using fun q : Fin N × Fin N => GlobalTheory.TrueTheta.approx D (k q.1 q.2) (Nat.mul_pos hn hM)
  have hb : ∀ q, ∃ o : 𝓞 D.host.E, (o : D.host.E) = b q := fun q =>
    int_of_inc (by rw [eb q]; exact add_mem (hk _ _) (mul_mem (natCast_mem _ _) (ht q)))
  choose o ho using hb
  have hzL : (fun i => ∑ j, b (i, j) * y j) ∈ skewLat D 𝔫 N := by
    have hy' := hy
    simp only [skewLat, Submodule.mem_pi, Set.mem_univ, true_implies] at hy' ⊢
    intro i
    refine sum_mem fun j _ => ?_
    rw [← ho (i, j)]
    have : ((o (i, j) : 𝓞 D.host.E) : D.host.E) * y j = o (i, j) • y j := (Algebra.smul_def _ _).symm
    rw [this]
    exact Submodule.smul_mem _ _ (hy' j)
  have hMy : ∀ j, inc D ((M : D.host.E) * y j) ∈ OhE D := by
    intro j
    have h1 := hMs y hy
    simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at h1
    obtain ⟨o', ho'⟩ := Submodule.mem_one.1 (h1 j)
    have : ((M : 𝓞 D.host.E) • y) j = (M : D.host.E) * y j := by simp [Algebra.smul_def]
    rw [← this, ← ho']
    exact VacMove.inc_int D o'
  have hw : ∀ i, (∑ j, t (i, j) * inc D ((M : D.host.E) * y j)) ∈ OhE D := fun i =>
    sum_mem fun j _ => mul_mem (ht _) (hMy j)
  have hks : ∀ i, k.mulVec s i ∈ OhE D := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (hk _ _) (hs j)
  have key : k.mulVec u = (fun i => inc D (∑ j, b (i, j) * y j)) -
      (fun i => (n : AE D) * ∑ j, t (i, j) * inc D ((M : D.host.E) * y j)) -
      (fun i => (n : AE D) * k.mulVec s i) := by
    funext i

    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, map_sum, map_mul, map_natCast, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 := e j
    have e2 := eb (i, j)
    push_cast at e2
    linear_combination (-inc D (y j)) * e2 - k i j * e1
  rw [key]
  intro i
  rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
  exact sub_mem (sub_mem ((hL _).1 hzL i) (hcl _ hw i)) (hcl _ hks i)

theorem moves_int_mul {N : ℕ} (𝔫 : Ideal (𝓞 D.host.E)) {h k : GA D N}
    (hL : Moves D (h : GL (Fin N) (AE D)) (skewLat D 𝔫 N)) (hk : k ∈ intG D N) :
    Moves D ((k * h : GA D N) : GL (Fin N) (AE D)) (skewLat D 𝔫 N) := by
  have hk' := (mem_intG k).1 hk
  intro x
  rw [hL x, Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul]
  constructor
  · intro hx i
    rw [← Matrix.mulVec_mulVec]
    exact lam_int_mul 𝔫 hL (fun i j => (hk' i j).2) _ hx i
  · intro hx i
    rw [← Matrix.mulVec_mulVec] at hx
    have := lam_int_mul 𝔫 hL (k := ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)))
      (fun i j => (hk' i j).1) _ hx i
    have hkk : ((k : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).mulVec
        ((((k : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).mulVec
          (fun j => inc D (x j))) = fun j => inc D (x j) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rwa [hkk] at this

end GlobalTheory.BotPairSmall.CvEig

namespace GlobalTheory.BotPairSmall.CvEig

theorem om_unitVec_eig : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ g ∈ intG D a, ∀ g' ∈ intG D d, ∃ c : ℂ, ‖c‖ = 1 ∧ W.Om g g' (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) = c • (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho g hg g' hg'
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he := hv.1
  have hT := VacMove.vac_TT h1 hc he
  have hI : Inp D := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied D
  have hev : Even (a * d) := hd.mul_left a
  have hcc : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
    have h2 : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => VacMove.conj_conj D x
    rw [smul_smul, h2, one_smul]
  have hcop' : IsCoprime (D.host.conj • 𝔪) (D.host.conj • D.host.conj • 𝔪) := by
    rw [hcc, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hcop
  obtain ⟨h, -, -, hmv, -, -⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D (D.host.conj • 𝔪) (GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm) hcop' d
  obtain ⟨c1, hc1, he1, -⟩ := GlobalTheory.NormSum.vacuum_under_adelic_pair D hI ⊤ δ hc a d hev e0 he W 1 h (stdL D a)
    (skewLat D (D.host.conj • 𝔪) d) (VacMove.moves_one D a) hmv
  have hg1 : Moves D (g : GL (Fin a) (AE D)) (stdL D a) := by
    simpa using VacMove.moves_mul_int hg (VacMove.moves_one D a)
  have hmv2 := moves_int_mul (D.host.conj • 𝔪) hmv hg'
  obtain ⟨c2, hc2, he2, -⟩ := GlobalTheory.NormSum.vacuum_under_adelic_pair D hI ⊤ δ hc a d hev e0 he W g (g' * h) (stdL D a)
    (skewLat D (D.host.conj • 𝔪) d) hg1 hmv2
  have n1 := norm_eq_one_of_modulusOneAll hc1
  have n2 := norm_eq_one_of_modulusOneAll hc2
  have c1ne : c1 ≠ 0 := by
    intro h0; rw [h0, norm_zero] at n1; exact zero_ne_one n1
  set F := Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0
    with hF
  have hF1 : F = c1⁻¹ • W.Om 1 h e0 := by
    rw [he1]; funext z; simp only [Pi.smul_apply, smul_eq_mul]; rw [← mul_assoc, inv_mul_cancel₀ c1ne, one_mul]
  refine ⟨c1⁻¹ * c2, by rw [norm_mul, norm_inv, n1, n2]; norm_num, ?_⟩
  have hm2 := W.mul g 1 g' h e0 hT
  rw [mul_one] at hm2
  conv_lhs => rw [hF1, W.smul _ _ _ _ (W.maps 1 h e0 hT), ← hm2, he2]
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.BotPairSmall.CvEig
end
end

section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.HeisTranslate

theorem mem_of_inc_mem_hatId {D : D7} {J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) {e : D.host.E}
    (he : inc D e ∈ hatId D J) : e ∈ (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
  have hJ0 : (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    simpa using hJ
  have key : ∀ y ∈ (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹, ∀ w ∈ hatId D J, w * inc D y ∈ OhE D := by
    intro y hy w hw
    induction hw using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨b, hb, s, hs, rfl⟩ := hz
      have hby : (b : D.host.E) * y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
        rw [← mul_inv_cancel₀ hJ0]
        exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hby
      have e1 : inc D (b : D.host.E) * s * inc D y = inc D ((c : 𝓞 D.host.E) : D.host.E) * s := by
        rw [show ((c : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E c from rfl, hc, map_mul]
        ring
      rw [e1]
      exact mul_mem (VacMove.inc_int D c) hs
    | zero => simpa using (OhE D).zero_mem
    | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
    | neg x _ hx => rw [neg_mul]; exact neg_mem hx
  rw [← inv_inv (J : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), FractionalIdeal.inv_eq,
    FractionalIdeal.mem_div_iff_of_ne_zero (inv_ne_zero hJ0)]
  intro y hy
  rw [FractionalIdeal.mem_one_iff]
  have hint : e * y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.E _ fun v => ?_
    rw [← GlobalTheory.Mem.Col2.SplitChar.vl_inc, map_mul]
    exact GlobalTheory.Mem.Col2.SplitChar.vl_le (key y hy _ he) v
  exact hint

end GlobalTheory.HeisTranslate

namespace GlobalTheory.HeisTranslate

theorem pt_mem_La_skew {D : D7} (δ : ℂ) (𝔫 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E)
    (hz : ∀ i j, z i j ∈ (((𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) :
    pt D (tor0 D ⊤ δ) δ z ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d) := by
  refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, _, ?_, rfl⟩
  refine Submodule.subset_span ⟨1, ?_, _, Submodule.subset_span fun x hx i _ => ?_, (one_smul _ _).symm⟩
  · refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  · have hx' : ∀ j, x j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := fun j => by
      simp only [stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hx
      exact hx j
    show ∑ j, z i j * x j ∈ _
    refine sum_mem fun j _ => ?_
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hx' j)
    rw [← hc, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c (hz i j)

end GlobalTheory.HeisTranslate

namespace GlobalTheory.HeisTranslate

theorem hf_swap (D : D7) (T : Tor D) {N N' : ℕ} (a b : VC D N N') :
    Hf D T b a = starRingEnd ℂ (Hf D T a b) := by

  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem norm_wdPh (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : ‖wdPh D T x‖ = 1 := by
  simp [wdPh, ee, Complex.norm_exp]

theorem wd_wd_unimod (D : D7) (T : Tor D) {N N' : ℕ} (a b : VC D N N') :
    ∃ φ : ℂ, ‖φ‖ = 1 ∧ ∀ F, Wd D T a (Wd D T b F) = φ • Wd D T (a + b) F := by
  have h0 : wdPh D T (a + b) ≠ 0 := Complex.exp_ne_zero _
  refine ⟨wdPh D T a * wdPh D T b / wdPh D T (a + b) *
    Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2), ?_, fun F => ?_⟩
  · have hre : ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2).re = 0 := by
      rw [hf_swap D T a b]
      simp [Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    rw [norm_mul, norm_div, norm_mul, norm_wdPh, norm_wdPh, norm_wdPh, Complex.norm_exp, hre]
    simp
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul, VacMove.hf_add_left, VacMove.hf_add_right, add_assoc]
  have : Complex.exp (-(Real.pi : ℂ) * (Hf D T z b + Hf D T a b) - (Real.pi : ℂ) * Hf D T b b / 2) *
      Complex.exp (-(Real.pi : ℂ) * Hf D T z a - (Real.pi : ℂ) * Hf D T a a / 2) =
      Complex.exp ((Real.pi : ℂ) * (Hf D T b a - Hf D T a b) / 2) *
      Complex.exp (-(Real.pi : ℂ) * (Hf D T z a + Hf D T z b) -
        (Real.pi : ℂ) * (Hf D T a a + (Hf D T b a + (Hf D T a b + Hf D T b b))) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  field_simp
  field_simp at this
  linear_combination (wdPh D T a * wdPh D T b * F (z + (a + b))) * this

end GlobalTheory.HeisTranslate

namespace GlobalTheory.HeisTranslate

theorem wd_unitVec_congr : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), ∀ y y' : Matrix (Fin d) (Fin a) D.host.E, (∀ i l, inc D (y i l - y' i l) ∈ hatId D (D.host.conj • 𝔪)) → ∃ c : ℂ, ‖c‖ = 1 ∧ Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y) (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) = c • Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) := by
  intro D δ t0 hc ht a d hd e0 hv W hep hep' 𝔪 hm hcop hcond o ho y y' hyy
  have hm' : D.host.conj • 𝔪 ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hm
  have hcc : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
    have h : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => VacMove.conj_conj D x
    rw [smul_smul, h, one_smul]
  have hcop' : IsCoprime (D.host.conj • 𝔪) (D.host.conj • D.host.conj • 𝔪) := by
    rw [hcc, Ideal.isCoprime_iff_sup_eq, sup_comm]; exact hcop
  obtain ⟨g', x', -, hg'm, -, -⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D (D.host.conj • 𝔪) hm' hcop' d
  have hsd : SD D (skewLat D (D.host.conj • 𝔪) d) := VacMove.sd_of_moves hg'm
  have hK : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) :=
    Or.inr ⟨_, _, GlobalTheory.FinWeil.RatTransl.sd_std D a, hsd, rfl⟩
  have hF := GlobalTheory.SkewTheta.iop_mem_thSp D δ hc e0 hv.1 (D.host.conj • 𝔪) hsd
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have hne : ((D.host.conj • D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [hcc]; simpa using hm
  have hx : pt D (tor0 D ⊤ δ) δ (y - y') ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d) := by
    refine pt_mem_La_skew δ (D.host.conj • 𝔪) (y - y') fun i j => ?_
    have hmem := mem_of_inc_mem_hatId hm' (hyy i j)
    rw [Matrix.sub_apply, FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero hne]
    intro w hw
    obtain ⟨c, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hw
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ c hmem
  have hfix := VacMove.wd_fix h1 hc hK hF hx
  obtain ⟨φ, hφ1, hφ⟩ := wd_wd_unimod D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ y') (pt D (tor0 D ⊤ δ) δ (y - y'))
  have e := hφ (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d)
    (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0)
  rw [hfix, ← VacMove.pt_add, add_sub_cancel] at e
  have hφ0 : φ ≠ 0 := by
    intro h; rw [h, norm_zero] at hφ1; exact zero_ne_one hφ1
  refine ⟨φ⁻¹, by rw [norm_inv, hφ1, inv_one], ?_⟩
  rw [e, smul_smul, inv_mul_cancel₀ hφ0, one_smul]

end GlobalTheory.HeisTranslate
end
end

section

open NumberField

theorem _root_.GlobalTheory.T.exists_short_generators_of_short_spanning_family : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V) (s : Set V) (A : ℝ), L.FG → (∀ σ x, 0 ≤ N σ x) → (∀ σ (a : K) x, N σ (a • x) = ‖σ a‖ * N σ x) → (∀ σ x y, N σ (x + y) ≤ N σ x + N σ y) → s ⊆ L → Submodule.span K s = ⊤ → (∀ y ∈ s, ∀ σ, N σ y ≤ A) → ∃ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen N L w abelian₂ ∧ abelian₂ ≤ max 1 ((Module.finrank ℚ K : ℝ) ^ 4 * (Formalism.HN.rkK L : ℝ) * |((NumberField.discr K : ℤ) : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ)) * A) ∧ n ≤ 2 * Module.finrank ℚ K * Formalism.HN.rkK L := by
  first | exact @GlobalTheory.exists_isShortGen_of_short_span | exact GlobalTheory.exists_isShortGen_of_short_span | (intros; apply GlobalTheory.exists_isShortGen_of_short_span <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct

theorem _root_.GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ φ : GAd σ J → ℂ, (∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g) → Continuous φ → IsSm σ J φ → ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) := by
  first | exact @GlobalTheory.DerCont.continuous_foldr_lineDer | exact GlobalTheory.DerCont.continuous_foldr_lineDer | (intros; apply GlobalTheory.DerCont.continuous_foldr_lineDer <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Matrix
noncomputable section

namespace GlobalTheory.CptMajorant

theorem exists_frame_le_majCpt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ K : Subgroup (GAd σ J), K ≤ infPts σ J → IsCompact (K : Set (GAd σ J)) →
    ∃ c : (∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)),
      (∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ K ≤ majCpt σ J c := by
  intro F E _ _ _ _ _ σ h n J hJ K hKinf hK
  have key : ∀ w : InfinitePlace F, ∃ c : GL (Fin n) (w.Completion ⊗[F] E),
      (∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) c.1 * JR w.Completion J * c.1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) ∧ ∀ k ∈ K, projArch σ J w k ∈ stabArch σ J w c := by
    intro w
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    let e := RingEquiv.ofBijective _ (infEmb_bijective h τ)
    have : IsTopologicalRing (w.Completion ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
    let φ : GAd σ J →* GL (Fin n) ℂ :=
      (Units.map (infEmb τ).mapMatrix.toMonoidHom).comp ((matHom _ σ J).comp (projArch σ J w))
    have hφv : ∀ x, (φ x).1 = (matHom _ σ J (projArch σ J w x)).1.map (infEmb τ) := fun x => rfl
    have hcv : Continuous fun x : GAd σ J => (φ x).1 := by
      simp only [hφv]
      exact (Units.continuous_val.comp ((isEmbedding_matHom _ σ J).continuous.comp
        (continuous_projArch σ J w))).matrix_map (GlobalTheory.Orb.continuous_infEmb τ)
    have hφ : Continuous φ := Units.continuous_iff.2 ⟨hcv, by
      simp only [← map_inv]; exact hcv.comp continuous_inv⟩
    obtain ⟨P, hPh, hPpos, hPinv⟩ := GlobalTheory.T.exists_posDef_hermitian_invariant_of_isCompact (K.map φ) (by rw [Subgroup.coe_map]; exact hK.image hφ)
    have hG : (J.map τ.1).IsHermitian := by
      ext i j
      exact (h.2.2.2 τ.1 _).symm.trans (congrArg _ (hJ.1 i j))
    have hd : (J.map τ.1).det ≠ 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (map_ne_zero _).2 hJ.2
    obtain ⟨ε, Q, hQ, hQu⟩ := GlobalTheory.T.hermitian_posDef_simultaneous_normal_form hG hd hPh hPpos
    have h1 : (Formalism.UG.bc e.symm.toRingHom Q).1.map (infEmb τ) = Q.1 := Matrix.ext fun i j => e.apply_symm_apply _
    have h1' : ((Formalism.UG.bc e.symm.toRingHom Q)⁻¹).1.map (infEmb τ) = (Q⁻¹).1 :=
      Matrix.ext fun i j => e.apply_symm_apply _
    have h2 : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by ext r s; simp [JR, inclR]
    refine ⟨Formalism.UG.bc e.symm.toRingHom Q, ⟨ε, Matrix.map_injective e.injective ?_⟩, fun k hk => ?_⟩
    · change Matrix.map _ (infEmb τ) = Matrix.map _ (infEmb τ)
      rw [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR h, h1, h2, hQ, Matrix.diagonal_map (map_zero _)]
      congr 1
      funext i
      split_ifs <;> simp
    · rw [mem_stabArch]
      change Formalism.UG.cT _ _ * 1 * _ = 1
      refine Matrix.map_injective e.injective ?_
      change Matrix.map _ (infEmb τ) = Matrix.map _ (infEmb τ)
      have hu := hQu (φ k).1 (hPinv _ ⟨k, hk, rfl⟩) (by
        have : Formalism.UG.cT (sigR _ σ) (matHom _ σ J (projArch σ J w k)).1 * JR w.Completion J *
          (matHom _ σ J (projArch σ J w k)).1 = JR w.Completion J := (projArch σ J w k).2
        have := congrArg (fun A => A.map (infEmb τ)) this
        simpa only [Matrix.map_mul, Frames.map_cT_sigR h, h2, hφv] using this)
      simpa only [Matrix.mul_one, Matrix.map_mul, Frames.map_cT_sigR h, Units.val_mul, h1, h1', hφv,
        Matrix.map_one _ (map_zero _) (map_one _)] using hu
  choose c hc hKc using key
  exact ⟨c, hc, fun k hk => mem_majCpt.2 ⟨hKinf hk, fun w => hKc w k hk⟩⟩

end GlobalTheory.CptMajorant
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

theorem _root_.GlobalTheory.T.definiteKernelNode_rank_le_totalRank : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (X : Node), DefNode D.R.m X → (G.V X).rank ≤ bigN D := by
  first | exact @GlobalTheory.DefRank.rank_le_bigN | exact GlobalTheory.DefRank.rank_le_bigN | (intros; apply GlobalTheory.DefRank.rank_le_bigN <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct

theorem _root_.GlobalTheory.T.leviDecomposition_gradedIsotropicFlag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → (∀ p ∈ parFlag σ J X d, ∃ u ∈ unipFlag σ J X d, ∃ m ∈ leviFlag σ J X Y d, p = u * m ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J)) ∧ unipFlag σ J X d ⊓ leviFlag σ J X Y d = ⊥ ∧ leftGrp σ J X d = unipFlag σ J X d ⊔ (ratPts σ J ⊓ leviFlag σ J X Y d) ∧ ∀ (t : Fin r → ℝ) (a : GAd σ J), (∀ i, t i ≠ 0) → IsTorusElt σ J X Y t a → a ∈ leviFlag σ J X Y d := by
  first | exact @GlobalTheory.LeviFlag.levi_decomposition | exact GlobalTheory.LeviFlag.levi_decomposition | (intros; apply GlobalTheory.LeviFlag.levi_decomposition <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

theorem _root_.GlobalTheory.T.principalLevelLiftModuliLaws_of_core : ∀ (D : D7) (T : CoreJ D) (j : ℕ), LawsJ T → InR D j → Laws D j (T.Q.Xo j) T.Q.c (T.U j) (coreDict T.toCore j) ∧ ∀ (G : WTZ D.host.E) (σ : T.Q.c.F →+* ℂ) (f : cuspW (T.Q.Xo j) T.Q.c (T.U j) G), normW (T.U j) (xiR D) (fun _ => D.sp.W j) (coreDict T.toCore j) G σ f = normW (T.U j) (xiR D) (T.V j) (T.dict j) G σ f := by
  first | exact @GlobalTheory.LevGeo.laws_of_coreJ | exact GlobalTheory.LevGeo.laws_of_coreJ | (intros; apply GlobalTheory.LevGeo.laws_of_coreJ <;> assumption)
end
