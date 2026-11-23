module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevQFiniteIndexAndRoot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle097
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemZmuOfPowPred
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle182
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Proof.levelCharacter_stepZero_typePrime

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem supSum_range {κ : Type} [CommRing κ] {n a k : ℕ} (hn : k ≤ n) (ha : k ≤ a) (M : Matrix (Fin n) (Fin n) κ) (f : ℕ → κ)
    (hf : ∀ (i : ℕ) (h : i + 1 < k), f i = M ⟨i, by omega⟩ ⟨i + 1, by omega⟩) :
    supSum a (Finset.range (k - 1)) M = ∑ i ∈ Finset.range (k - 1), f i := by
  unfold supSum
  have h1 : ∀ i : Fin n, (∑ j : Fin n, if i.val + 1 = j.val ∧ j.val < a ∧ i.val ∈ Finset.range (k - 1) then M i j else 0) =
      if i.val ∈ Finset.range (k - 1) then f i.val else 0 := by
    intro i
    by_cases hi : i.val ∈ Finset.range (k - 1)
    · have hi' := Finset.mem_range.1 hi
      rw [if_pos hi, Finset.sum_eq_single (⟨i.val + 1, by omega⟩ : Fin n), if_pos ⟨rfl, by dsimp only; omega, hi⟩,
        hf _ (by omega)]
      · intro j _ hj
        exact if_neg fun h => hj (Fin.ext h.1.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · simp [hi]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_eq_sum_range (fun i => if i ∈ Finset.range (k - 1) then f i else 0) n,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

variable {E : Type} [Field E]

theorem entB_X (q : ℕ) {k n c i : ℕ} (hn : k ≤ n) (hi : i + 1 < k) (ex : ℕ → ℕ) (x : HomE E (n + c) (n + c)) :
    LocE.entB q k c n c n ex ex x i (i + 1) = Loc.atN (x (Loc.eN E (n + c) (i + 1))) i := by
  have e1 : LocE.fIdx k c n i = i := if_pos (by omega)
  have e2 : LocE.fIdx k c n (i + 1) = i + 1 := if_pos hi
  have e3 : LocE.scE n ex i = 0 := if_pos (by omega)
  have e4 : LocE.scE n ex (i + 1) = 0 := if_pos (by omega)
  unfold LocE.entB
  rw [e1, e2, e3, e4]
  simp

theorem symLevelFrameEntry_superdiag_second_block (q : ℕ) {k n c i : ℕ} (hi : i + 1 < c) (x : HomE E (n + c) (n + c)) :
    LocE.entB q k c n c n (fun i => i + 1) (fun i => i + 1) x (k + i) (k + i + 1) =
      (q : E) * Loc.atN (x (Loc.eN E (n + c) (n + i + 1))) (n + i) := by
  have e1 : LocE.fIdx k c n (k + i) = n + i := by
    unfold LocE.fIdx
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  have e2 : LocE.fIdx k c n (k + i + 1) = n + i + 1 := by
    unfold LocE.fIdx
    rw [if_neg (by omega), if_pos (by omega)]
    omega
  have e3 : LocE.scE n (fun i => i + 1) (n + i + 1) - LocE.scE n (fun i => i + 1) (n + i) = 1 := by
    unfold LocE.scE
    rw [if_neg (by omega), if_neg (by omega)]
    beta_reduce
    omega
  unfold LocE.entB
  rw [e1, e2, e3, zpow_one, mul_comm]

theorem chrG_zero {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (hs : cst.sharp = true)
    (hψ : ∀ a : X.E, IntAt P.1 a → cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) :
    ChrG Ch sel mu cst 0 P 1 (colLev Ch 0 ⟨P.1, hP⟩) := by
  have hm := R.two_le_m
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hc : R.r - R.k - 1 = cOf R 0 - 1 := by unfold Ranks.r cOf; omega
  have hl : colLev Ch 0 ⟨P.1, hP⟩ = ⟨HX (𝓞 X.E ⧸ P.1.asIdeal) (R.N 0) R.k R.t 0,
      lamX (Ch.psi0 ⟨P.1, hP⟩) (extChi fun s => Ch.chi s ⟨P.1, hP⟩) (R.N 0) R.k R.m R.t 0⟩ := if_pos (by omega)
  rw [hl]
  intro hbar g r hr hrg hg
  have hq : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.TopStep.qOf_ne_zero
  have hp0 : psi0P Ch P.1 = Ch.psi0 ⟨P.1, hP⟩ := dif_pos hP
  have hJ := hr.2
  simp only [Jat, hP, hs, if_true] at hJ
  have hst : r ∈ stabL X.E _ (LocE.lamY P.1 (qOf P.1) (R.N 0) (cOf R 0) fun i => i + 1) := by
    have h1 := hJ.1
    simpa using h1
  have hint := fun p p' => GlobalTheory.LastSteps.entB_int (P := P.1) R.k (x := r.toLinearMap) (fun y hy => (hst y).2 hy) p p'
  have ha := GlobalTheory.Mem.LevFin.intAt_n1Arg_G hq r hst
  have h2 : ∑ i ∈ Finset.range (R.r - R.k - 1), LocE.entB (qOf P.1) R.k (cOf R 0) (R.N 0) (cOf R 0) (R.N 0)
      (fun i => i + 1) (fun i => i + 1) r.toLinearMap (R.k + i) (R.k + i + 1) = (qOf P.1 : X.E) * Loc.n1Arg r := by
    rw [hc, Loc.n1Arg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have := Finset.mem_range.1 hi
    exact symLevelFrameEntry_superdiag_second_block _ (by omega) _
  have h3 : cst.psi P (Loc.n1Arg r) = psi0P Ch P.1 (redP P.1 ((qOf P.1 : X.E) * Loc.n1Arg r)) := by
    rw [← hψ _ ha, mul_div_cancel_left₀ _ hq]
  have h4 : ((lamX (Ch.psi0 ⟨P.1, hP⟩) (extChi fun s => Ch.chi s ⟨P.1, hP⟩) (R.N 0) R.k R.m R.t 0 hbar : X.Kˣ) : X.K) =
      Ch.psi0 ⟨P.1, hP⟩ (supSum R.k (Finset.range (R.k - 1)) hbar.1.1) := by
    show ((lamGen _ _ _ R.k [] (SX R.k R.m 0) hbar : X.Kˣ) : X.K) = _
    rw [lamGen_nil, SX_zero]
    rfl
  refine h4.trans ?_
  simp only [chiInv, lamRow, hP, hs, if_true, LocE.lamGBS, LocE.lamGvS, inv_one, one_mul, mul_one, Finset.range_zero,
    Finset.prod_empty]
  rw [h2, h3, hp0, reduction_add (GlobalTheory.TopStep.intAt_sum _ fun i _ => hint _ _) ha, AddChar.map_add_eq_mul,
    GlobalTheory.TopStep.reduction_sum₂ _ fun i _ => hint _ _, mul_comm, mul_inv_cancel_right₀ (AddChar.val_isUnit _ _).ne_zero]
  congr 1
  refine supSum_range hN.ge le_rfl _ _ fun i hi => ?_
  have hi1 : i + 1 < R.N 0 := by omega
  have hi0 : i < R.N 0 := by omega
  have he : Loc.eN X.E (R.N 0 + cOf R 0) (i + 1) = Loc.inX X.E (R.N 0) (cOf R 0) (Loc.eN X.E (R.N 0) (i + 1)) := by
    funext l
    rw [GlobalTheory.QNormal.inX_apply]
    unfold Loc.eN
    split_ifs <;> first | rfl | omega
  have hv : redV P.1 (Loc.eN X.E (R.N 0) (i + 1)) = Pi.single ⟨i + 1, hi1⟩ 1 := by
    funext l
    simp only [redV, Loc.eN, Pi.single_apply, Fin.ext_iff]
    split_ifs
    · exact GlobalTheory.TopStep.reduction_one₂
    · exact GlobalTheory.TopStep.reduction_zero
  have h5 := congrFun (hg _ (GlobalTheory.GO.ChRoot.eN_mem (i := i + 1))) ⟨i, hi0⟩
  rw [hv, Matrix.mulVec_single_one] at h5
  rw [entB_X _ hN.ge hi, he, LinearEquiv.coe_coe, hrg, Loc.atN, dif_pos (by omega), GlobalTheory.QNormal.inX_apply, dif_pos hi0]
  exact h5

end GlobalTheory.Proof.levelCharacter_stepZero_typePrime

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxFin

open GlobalTheory.Mem.LevFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem exists_classes {N q : ℕ} (hq : (q : E) ≠ 0) (e : ℕ → ℤ) (j : ℕ) :
    ∃ (ι : Type) (_ : Finite ι) (f : (Sp E N ≃ₗ[E] Sp E N) → ι), ∀ h h' : Sp E N ≃ₗ[E] Sp E N,
      (∀ x ∈ LocE.sclLat P q N e, h⁻¹ x ∈ LocE.sclLat P q N e ∧ ((q : E) ^ j) • h x ∈ LocE.sclLat P q N e) →
      (∀ x ∈ LocE.sclLat P q N e, h'⁻¹ x ∈ LocE.sclLat P q N e ∧ ((q : E) ^ j) • h' x ∈ LocE.sclLat P q N e) →
      f h = f h' → ∀ x ∈ LocE.sclLat P q N e, (q : E)⁻¹ • ((h⁻¹ * h') x - x) ∈ LocE.sclLat P q N e := by
  classical
  have hc : ((q ^ (j + 1) : ℕ) : E) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hq
  have hq' : ((q ^ (j + 1) : ℕ) : 𝓞 E) ≠ 0 := fun h0 => hc (by simpa using congrArg (algebraMap (𝓞 E) E) h0)
  have hfin : Finite (𝓞 E ⧸ Ideal.span {((q ^ (j + 1) : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa only [Ne, Ideal.span_singleton_eq_bot] using hq')
  have hz : ∀ l : ℕ, (q : E) ^ e l ≠ 0 := fun l => zpow_ne_zero _ hq
  have he : ∀ i : Fin N, (Pi.single i ((q : E) ^ e i.1) : Sp E N) ∈ LocE.sclLat P q N e := by
    intro i
    rw [GlobalTheory.CongLevel.mem_sclLat]
    intro l
    rw [Pi.single_apply]
    split_ifs with hl
    · rw [hl, inv_mul_cancel₀ (hz _)]
      exact GlobalTheory.GO.ChRoot.intAt_one'
    · rw [mul_zero]
      exact GlobalTheory.GO.ChRoot.intAt_zero'
  let m : (Sp E N ≃ₗ[E] Sp E N) → Fin N → Fin N → E :=
    fun h i l => ((q : E) ^ e l.1)⁻¹ * ((q : E) ^ j * h (Pi.single i ((q : E) ^ e i.1)) l)
  have hex : ∀ a : E, ∃ r : 𝓞 E, IntAt P a → IntAt P (((q ^ (j + 1) : ℕ) : E)⁻¹ * (a - algebraMap (𝓞 E) E r)) := by
    intro a
    by_cases ha : IntAt P a
    · obtain ⟨r, hr⟩ := exists_int_congr hc ha
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => (ha h).elim⟩
  choose r hr using hex
  refine ⟨Fin N → Fin N → 𝓞 E ⧸ Ideal.span {((q ^ (j + 1) : ℕ) : 𝓞 E)}, inferInstance,
    fun h i l => Ideal.Quotient.mk _ (r (m h i l)), fun a b ha hb hab x hx => ?_⟩
  have hma : ∀ i l, IntAt P (m a i l) := fun i l => (GlobalTheory.CongLevel.mem_sclLat P q N e _).1 (ha _ (he i)).2 l
  have hmb : ∀ i l, IntAt P (m b i l) := fun i l => (GlobalTheory.CongLevel.mem_sclLat P q N e _).1 (hb _ (he i)).2 l
  have h1 : ∀ i l, IntAt P (((q ^ (j + 1) : ℕ) : E)⁻¹ * (m b i l - m a i l)) := by
    intro i l
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun (congrFun hab i) l))
    have ht' := congrArg (algebraMap (𝓞 E) E) ht
    simp only [map_mul, map_natCast, map_sub] at ht'
    have := ((hr _ (hmb i l)).add (intAt_neg (hr _ (hma i l)))).add (intAt_neg (IntAt.coe P t))
    convert this using 1
    generalize ((q ^ (j + 1) : ℕ) : E) = c at *
    field_simp
    linear_combination ht'
  have e1 : (q : E)⁻¹ • ((a⁻¹ * b) x - x) = a⁻¹ ((q : E)⁻¹ • (b x - a x)) := by
    rw [map_smul, map_sub, show a⁻¹ (a x) = x from LinearEquiv.symm_apply_apply _ x]
    rfl
  rw [e1]
  refine (ha _ ?_).1
  rw [GlobalTheory.CongLevel.mem_sclLat] at hx ⊢
  intro l
  have ex : x = ∑ i, (((q : E) ^ e i.1)⁻¹ * x i) • (Pi.single i ((q : E) ^ e i.1) : Sp E N) := by
    funext l
    have := hz l.1
    simp [Finset.sum_apply, Pi.single_apply]
    field_simp
  have e2 : ((q : E) ^ e l.1)⁻¹ * ((q : E)⁻¹ • (b x - a x)) l =
      ∑ i, (((q : E) ^ e i.1)⁻¹ * x i) * (((q ^ (j + 1) : ℕ) : E)⁻¹ * (m b i l - m a i l)) := by
    conv_lhs => rw [ex]

    simp only [map_sum, map_smul, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
    Finset.mul_sum, m]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hz l.1
    have := hz i.1
    push_cast
    field_simp
    ring
  rw [e2]
  exact Finset.sum_induction _ (IntAt P) (fun _ _ => IntAt.add) GlobalTheory.GO.ChRoot.intAt_zero' fun i _ =>
    (hx i).mul (h1 i l)

theorem exists_finite_index_of_adm_cosets : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), ∃ (ι : Type) (_ : Finite ι) (f : AutY X R j → ι), ∀ h h' : AutY X R j, admitted Pr j P h → admitted Pr j P h' → f h = f h' → h⁻¹ * h' ∈ Jat (Pr := Pr) sharp j P := by
  intro X Pr R sharp j P
  classical
  have hq := qOf_ne P
  have hb : ∀ h : AutY X R j, admitted Pr j P h → ∀ x ∈ lamYat (Pr := Pr) (R := R) j P,
      h⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧ ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P := by
    intro h hh
    by_cases hP : P ∈ Pr.vGs
    · have hs := hh.1 hP
      intro x hx
      refine ⟨((inv_mem hs) x).2 hx, ?_⟩
      rw [← Nat.cast_pow]
      exact natCast_smul_mem _ _ ((hs x).2 hx)
    · exact (between_iff hP h).2 (hh.2 hP)
  obtain ⟨ι, hι, f, hf⟩ := exists_classes (P := P) (N := R.N j + cOf R j) hq
    (LocE.scE (R.N j) (if P ∈ Pr.vGs then fun i => i + 1 else 0)) j
  refine ⟨ι, hι, f, fun h h' hh hh' e => ?_⟩
  have h1 := hf h h' (hb h hh) (hb h' hh') e
  have h2 := hf h' h (hb h' hh') (hb h hh) e.symm
  refine mem_Jat _ _ _ _ (stab_of_cong hq _ _ h1 ?_) h1
  rw [mul_inv_rev, inv_inv]
  exact h2

end GlobalTheory.Mem.Col2.IdxFin

end
end

section

noncomputable section

namespace GlobalTheory.LevelHecke.UpKeeps

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

section Fr

variable {ι : Type} [Fintype ι] {n : ℕ} {E : Type} [Field E]

theorem atInf_mul_inv' (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.mul_inv]
  simp

theorem atInf_inv_mul' (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * atInf emb (γ : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.inv_mul]
  simp

def trans (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) {G : ι → Matrix (Fin n) (Fin n) ℂ} (y : Frames G) : Frames G :=
  ⟨fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ, fun τ => by
    rw [det_mul]
    exact (Matrix.isUnit_det_of_right_inverse (atInf_mul_inv' emb γ τ)).mul (y.2 τ)⟩

theorem isTr_iff (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) {G : ι → Matrix (Fin n) (Fin n) ℂ} (y' y : Frames G) :
    IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) y' y ↔ y' = trans emb γ⁻¹ y := by
  constructor
  · intro h
    apply Subtype.ext
    funext τ
    show y'.1 τ = _ * y.1 τ
    rw [h τ, ← Matrix.mul_assoc, atInf_inv_mul', Matrix.one_mul]
  · rintro rfl τ
    show y.1 τ = _ * (_ * y.1 τ)
    rw [← Matrix.mul_assoc, atInf_mul_inv', Matrix.one_mul]

def twist (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (G : ι → Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    (Frames G → ℂ) →+ (Frames G → ℂ) where
  toFun h := fun y => c * h (trans emb γ⁻¹ y)
  map_zero' := by funext y; simp
  map_add' a b := by funext y; simp [mul_add]

theorem twist_eq_zero (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (G : ι → Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0)
    (h : Frames G → ℂ) (h0 : twist emb γ G c h = 0) : h = 0 := by
  funext z
  have e : z = trans emb γ⁻¹ (trans emb γ z) := (isTr_iff emb γ _ _).1 fun _ => rfl
  have h1 : c * h (trans emb γ⁻¹ (trans emb γ z)) = 0 := congrFun h0 (trans emb γ z)
  rw [← e] at h1
  exact (mul_eq_zero.1 h1).resolve_left hc

end Fr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

theorem atV_conj {v : HeightOneSpectrum (𝓞 F)} {η : GA σ J} (h : AtV v η) (κ : GA σ J) : AtV v (κ * η * κ⁻¹) := by
  intro v' hv'
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, h v' hv', mul_one, mul_inv_cancel]

variable (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
  {k : Type} [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k)

theorem pair_move (hp : PMap S v hv p) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (x x' κ : GA σ J)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1) (η : GA σ J) :
    p (x' * η) = (p (x * (κ * η))).act (glE γ) := by
  apply hp.1 γ hγ
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, hx, mul_assoc, mul_assoc]

theorem valAt_move (hb : v ∉ bad) (hp : PMap S v hv p) (g : GA σ J → Frames (gramC J emb) → ℂ) (hg : g ∈ AdFun S emb)
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (x x' : GA σ J) (κ : S.U)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1) (q : Pr (𝓞 E) (Fin n → E) k) :
    valAt v p g x' (q.act (glE γ)) = twist emb γ (gramC J emb) (S.chi κ : ℂ) (valAt v p g x q) := by
  have hκ := (S.U_eq κ.1).1 κ.2
  let c : GA σ J := ⟨κ.1, hκ.1⟩
  have hcv : p (x * c) = p x := (hp.2.1 x c).2 (hκ.2 v)
  have hmv := pair_move S v hv p hp γ hγ x x' c hx
  have hU : ∀ z : GA σ J, p (z * c) = p z := fun z => (hp.2.1 z c).2 (hκ.2 v)
  unfold valAt
  by_cases h : ∃ η, AtV v η ∧ p (x * η) = q
  · have h' : ∃ η, AtV v η ∧ p (x' * η) = q.act (glE γ) := by
      obtain ⟨η, h1, h2⟩ := h
      refine ⟨c⁻¹ * η * c⁻¹⁻¹, atV_conj h1 _, ?_⟩
      rw [hmv, ← h2, ← hU (x * η)]
      congr 2
      group
    rw [dite_eq_left h, dite_eq_left h']
    obtain ⟨h1, h2⟩ := h.choose_spec
    obtain ⟨h1', h2'⟩ := h'.choose_spec
    generalize h.choose = η at h1 h2
    generalize h'.choose = η' at h1' h2'
    rw [hmv] at h2'
    have h3 := Pr.act_injective _ h2'
    have h4 : p (x * η * (η⁻¹ * c * η')) = p (x * η) := by
      rw [h2, ← h3]; congr 1; group
    have h5 := (hp.2.1 _ _).1 h4
    have hoff : ∀ v', v' ≠ v → bc (prV (E := E) v') (η⁻¹ * c * η' : GA σ J).1 = bc (prV (E := E) v') κ.1 := by
      intro v' hv'
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, h1 v' hv', h1' v' hv',
        inv_one, one_mul, mul_one]
    have hmem : (η⁻¹ * c * η' : GA σ J).1 ∈ S.U := by
      refine (S.U_eq _).2 ⟨(η⁻¹ * c * η' : GA σ J).2, fun v' => ?_⟩
      by_cases e : v' = v
      · subst e; exact h5
      · rw [hoff v' e]; exact hκ.2 v'
    have hchi : S.chi ⟨_, hmem⟩ = S.chi κ := by
      have := S.chi_triv (κ⁻¹ * ⟨_, hmem⟩) fun v' hv' => by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        show _ * bc (prV (E := E) v') (η⁻¹ * c * η' : GA σ J).1 = 1
        rw [hoff v' (fun e => hb (e ▸ hv')), inv_mul_cancel]
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    funext y
    have := hg γ hγ (x * η) (x' * η') ⟨_, hmem⟩ (by
      show (x' * η').1 = _ * (x * η).1 * (η⁻¹ * c * η' : GA σ J).1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hx]
      show _ = _ * _ * (_ * κ.1 * _)
      group) y (trans emb γ⁻¹ y) ((isTr_iff emb γ _ _).2 rfl)
    rw [this, hchi]
    rfl
  · have h' : ¬ ∃ η, AtV v η ∧ p (x' * η) = q.act (glE γ) := by
      rintro ⟨η, h1, h2⟩
      rw [hmv] at h2
      have h3 := Pr.act_injective _ h2
      refine h ⟨c * η * c⁻¹, atV_conj h1 _, ?_⟩
      rw [← h3, ← hU (x * (c * η * c⁻¹))]
      congr 1
      group
    rw [dite_eq_right h, dite_eq_right h', map_zero]

theorem upAd_mem_adForms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (ι : Type) [Fintype ι] (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (k : Type) [Field k] (p : GA σ J → Pr (𝓞 E) (Fin n → E) k), v ∉ bad → PMap S v hv p → ∀ (res : 𝓞 E →+* k) (t : 𝓞 E) (lam : ι → DomWeight n), ∀ g ∈ AdForms S emb lam, upAd res t v p g ∈ AdForms S emb lam := by
  intro F E _ _ _ _ _ σ n J T f bad ι _ S emb v hv k _ p hb hp res t lam g hg
  refine ⟨?_, fun x _ => ?_⟩
  · intro γ hγ x x' κ hx y y' hy
    have hκ := (S.U_eq κ.1).1 κ.2
    have hpx : p x' = (p x).act (glE γ) := by
      have := pair_move S v hv p hp γ hγ x x' ⟨κ.1, hκ.1⟩ hx 1
      rwa [mul_one, mul_one, (hp.2.1 x ⟨κ.1, hκ.1⟩).2 (hκ.2 v)] at this
    have key : upAd res t v p g x' = twist emb γ (gramC J emb) (S.chi κ : ℂ) (upAd res t v p g x) := by
      have hz := twist_eq_zero emb γ (gramC J emb) (S.chi κ : ℂ) (Units.ne_zero _)
      unfold upAd
      rw [AddMonoidHom.map_finsum_of_preimage_zero _ hz]
      simp only [AddMonoidHom.map_finsum_of_preimage_zero _ hz]
      symm
      refine finsum_mem_eq_of_bijOn (Pr.act (glE γ)) ⟨fun q hq => ?_, (Pr.act_injective _).injOn, fun q hq => ?_⟩ fun q _ => ?_
      · rw [hpx]; exact Pr.Inc.act hq _
      · have e : (q.act (glE γ).symm).act (glE γ) = q := by
          rw [Pr.act_act, LinearEquiv.symm_trans_self, Pr.act_refl]
        refine ⟨q.act (glE γ).symm, ?_, e⟩
        rw [hpx, ← e] at hq
        exact (Pr.inc_act_iff _ _ _).1 hq
      · exact (valAt_move S emb v hv p hb hp g hg.1 γ hγ x x' κ hx q).symm
    rw [key, (isTr_iff emb γ _ _).1 hy]
    rfl
  · have hval : ∀ q, valAt v p g x q ∈ ValC (gramC J emb) lam := by
      intro q
      unfold valAt
      split_ifs with h
      · exact hg.2 _ (Set.mem_univ _)
      · exact zero_mem _
    show upAd res t v p g x ∈ ValC (gramC J emb) lam
    unfold upAd
    refine finsum_induction (· ∈ ValC (gramC J emb) lam) (zero_mem _) (fun _ _ => add_mem) fun q => ?_
    exact finsum_induction (· ∈ ValC (gramC J emb) lam) (zero_mem _) (fun _ _ => add_mem) fun _ => hval q

end GlobalTheory.LevelHecke.UpKeeps

end
end

section

open NumberField IsDedekindDomain Formalism.L2.Ker Matrix
open scoped BigOperators

theorem _root_.GlobalTheory.T.nonempty_isoKG_of_trace_positive : ∀ (K E : Type) [Field K] [CharZero K] [Field E] [Algebra K E] [FiniteDimensional K E] (cj : E →+* E) (σ : K →+* K) (ι : Type) [Fintype ι], Fintype.card ι = Module.finrank K E → (∀ x, cj (algebraMap K E x) = algebraMap K E (σ x)) → (∀ y, cj (cj y) = y) → (∀ y, Algebra.trace K E (cj y) = σ (Algebra.trace K E y)) → (∀ y, y ≠ 0 → ∃ a : ℚ, 0 < a ∧ Algebra.trace K E (y * cj y) = (a : K)) → Nonempty (IsoKG K E cj ι) := by
  first | exact @GlobalTheory.FourCopiesIso.nonempty_isoKG | exact GlobalTheory.FourCopiesIso.nonempty_isoKG | (intros; apply GlobalTheory.FourCopiesIso.nonempty_isoKG <;> assumption)
end
