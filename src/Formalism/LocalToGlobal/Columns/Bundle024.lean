module

public import Formalism.LocalToGlobal.Columns.Bundle005
public import Formalism.LocalToGlobal.Columns.CardPathsEqSubmodulePairs
public import Formalism.LocalToGlobal.Columns.MemOfSmulMemOfAddEqOne
public import Formalism.LocalToGlobal.Columns.NeighbourConjOfTopNeighbour
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.Bundle021
public import Formalism.LocalToGlobal.Columns.Bundle020
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Formalism.LocalToGlobal.Columns.Bundle019
import Formalism.LocalToGlobal.Columns.XtLamGvSCongr
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.Columns.Bundle008
public import Formalism.LocalToGlobal.Columns.Bundle022
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem pathCount_symmetric_holds : DecorationPathSymmetry E n ST SG := by
  intro P Q hP hQ hSTP hSGP hSTQ hSGQ i j d f
  by_cases hQP : Q = P
  · subst hQP
    exact pathCount_symm_same_prime Q hP hSTP hSGP i j d f
  by_cases hQP' : Q = conjPrime₂ P
  · subst hQP'
    exact pathCount_conj_symm (P := P) hP hSTP hSGP (fun i j d f => pathCount_symm_same_prime P hP hSTP hSGP i j d f) i j d f
  exact pathCount_symm_distinct P Q hP hQ hQP hQP' hSTP hSGP hSTQ hSGQ i j d f

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

theorem heckeOperators_commute (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : HeckeComm c S0 :=
  heckeComm_of_paths c S0 pathCount_symmetric_holds

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QExact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

def FrExact (q : QLoc hc n Q Θ) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (p : DecoF E n ST SG Q) : Prop :=
  decoOf ST SG x = p.deco ∧ ∀ P : Q, q.at P x = bc (q.phi P) (qGL n (p.fr P))

theorem FrExact.over {q : QLoc hc n Q Θ} {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {p : DecoF E n ST SG Q} (h : FrExact q x p) :
    FrOver q x p := by
  refine ⟨h.1, fun P => ?_⟩
  rw [h.2 P, inv_mul_cancel]
  exact (q.U P).one_mem

variable {H : Subgroup (GLG (E := E) (n := n) (SG := SG))}

def recClsFy (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hE : FrExists (n := n) ST SG Q)
    (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q) (hs : ∀ c, (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q H Θ) = c)
    (y : DecoFCl (K := K) n ST SG Q H Θ → UAd hc n) (hy : ∀ c, FrOver q (y c).1 (s c)) :
    RecClsF hc n ST SG Q H q s where
  y c := y c
  y_bij := by
    constructor
    · intro c c' h
      have hr := Quotient.exact' h
      obtain ⟨h0, hh, k, hk, e⟩ := DoubleCoset.rel_iff.1 hr
      obtain ⟨γ, hγ⟩ := Formalism.L2.DIV.ratEl_surjective (⟨h0, hh⟩ : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E))
      have hh' : ((h0 : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) :=
        (congrArg (fun z : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E) =>
          ((z : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) hγ).symm
      have hk' : ((k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ ∈ levUQ hc n ST SG Q H q :=
        Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hk)
      have e' : ((y c' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
          Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            (((⟨_, hk'⟩ : levUQ hc n ST SG Q H q) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))⁻¹ := by
        have e2 := congrArg (fun z : UAd hc n => (z : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) e
        simp only [Subgroup.coe_mul] at e2
        rw [e2, hh', inv_inv]
      obtain ⟨a, -, -, ha⟩ := qdf_orbit_of_rel H q (hy c) (hy c') γ ⟨_, hk'⟩ e'
      rw [← hs c, ← hs c']
      exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨a⁻¹, by show a⁻¹ • s c' = s c; rw [ha, inv_smul_smul]⟩)
    · intro Qc
      induction Qc using Quotient.inductionOn' with
      | h x =>
        obtain ⟨p, hp⟩ := qdf_over_exists q hF hE x
        refine ⟨Quotient.mk'' p, ?_⟩
        obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.1 (Quotient.exact (hs (Quotient.mk'' p)))
        have ha' : a • p = s (Quotient.mk'' p) := ha
        have hx' : FrOver q (y (Quotient.mk'' p)).1 (a • p) := by
          rw [ha']; exact hy _
        obtain ⟨γ, κ, -, e⟩ := qdf_rel_of_orbit H q a hp hx'
        exact (qdf_mk_eq H q γ κ e).symm
  y_lat c x := by
    have h := decoRaw_carries hc n ST SG (y c).2 x
    rw [← rlc_decoOf_val hc n ST SG (y c).2, (hy c).1] at h
    exact h
  stabI c := qdStab H (s c)
  stabI_inj c := by
    intro a b hab
    have h1 : a.1.1 = b.1.1 := by rw [← qdf_ratHom_stab (hc := hc) H (s c) a, ← qdf_ratHom_stab (hc := hc) H (s c) b, hab]
    have ha := qdf_stab_deco H (s c) a
    have hb := qdf_stab_deco H (s c) b
    have hab' : ((a.1.1, (a.1.2.1 : GLG (E := E) (n := n) (SG := SG))) : UF E n × GLG (E := E) (n := n) (SG := SG)) • (s c).deco = (s c).deco := ha
    have hbb' : ((b.1.1, (b.1.2.1 : GLG (E := E) (n := n) (SG := SG))) : UF E n × GLG (E := E) (n := n) (SG := SG)) • (s c).deco = (s c).deco := hb
    have h2 := DecoSet.stab_fst_injective (s c).deco hab' hbb' h1
    have h3 : a.1.2.2 = b.1.2.2 := by
      apply Subtype.ext
      funext P
      apply Subtype.ext
      rw [qdf_stab_fr H (s c) a P, qdf_stab_fr H (s c) b P, h1]
    exact Subtype.ext (Prod.ext h1 (Prod.ext (Subtype.ext (congrArg Prod.snd h2)) h3))
  stabI_range c γ hγ := by
    constructor
    · rintro ⟨a, ha⟩
      have hx := hy c
      have hx' : FrOver q (y c).1 (a.1 • s c) := by rw [a.2]; exact hx
      obtain ⟨γ', κ, h1, e⟩ := qdf_rel_of_orbit H q a.1 hx hx'
      have hγ' : γ' = ⟨γ, hγ⟩ := by
        rw [← ha]
        exact (ratHom_bijective hc n).1 (h1.trans (qdf_ratHom_stab (hc := hc) H (s c) a).symm)
      refine ⟨κ.1, κ.2, ?_⟩
      show ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * κ.1 *
        ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ = _
      have e' : Formalism.UG.bc (iA F E) (γ' : GL (Fin n) E) = ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          κ.1 * ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ :=
        eq_mul_inv_of_mul_eq (eq_mul_inv_iff_mul_eq.1 e).symm
      rw [← e', hγ']
    · rintro ⟨k, hk, e⟩
      have e' : ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * k *
          ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ =
          Formalism.UG.bc (iA F E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) E) := e
      have e2 : ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
          Formalism.UG.bc (iA F E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) E) *
            ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            ((⟨k, hk⟩ : levUQ hc n ST SG Q H q) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
        rw [← e']; group
      obtain ⟨a, ha1, -, ha⟩ := qdf_orbit_of_rel H q (hy c) (hy c) ⟨γ, hγ⟩ ⟨k, hk⟩ e2
      refine ⟨⟨a, ha.symm⟩, ?_⟩
      apply (ratHom_bijective hc n).1
      rw [qdf_ratHom_stab (hc := hc) H (s c) ⟨a, ha.symm⟩, ha1]
  stabI_lat c a x := by
    have h := stabRat_lat hc n ST SG H (s c).deco ⟨_, qdf_stab_deco H (s c) a⟩ x
    have e : stabRat hc n ST SG H (s c).deco ⟨_, qdf_stab_deco H (s c) a⟩ = qdStab H (s c) a :=
      (ratHom_bijective hc n).1 ((rlc_ratHom_stabRat hc n ST SG H _ _).trans (qdf_ratHom_stab (hc := hc) H (s c) a).symm)
    rw [e] at h
    exact h

end QExact

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section TopG

variable {X : Fields} {Pr : Primes X} {R : Ranks}

structure TopNum (R : Ranks) (i : ℕ) : Prop where
  a_eq : R.r + (i + 1 - 1) * R.t = R.N i
  a_le : R.r + (i + 1 - 1) * R.t ≤ (R.N (i + 1) - 1) + 0
  c0 : cOf R i = 0

theorem topNum_of {m2 : ℕ} (hm : R.m = m2 + 2) : TopNum R (m2 + 1) := by
  have h := xt_a_eq (R := R) hm
  have e : R.m - 1 = m2 + 1 + 1 - 1 := by omega
  rw [e] at h
  refine ⟨h, ?_, xt_cOf hm⟩
  rw [h]
  unfold Ranks.N
  have e2 : (m2 + 1 + 1) * (R.t + 1) = (m2 + 1) * (R.t + 1) + (R.t + 1) := by ring
  omega

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem xtPhiTopG_congr (hX : X.Ok) (hPr : Pr.Ok) {i : ℕ} (hn : TopNum R i) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x x' : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0))
    (hD : ∀ p p', p < (R.N (i + 1) - 1) + 0 → p' < R.N i → ∃ d, IntAt P d ∧
      LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x p p' + (qOf P : X.E) * d) :
    PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x' = PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x := by
  have hu := ciQ_notMem_sq hX hPr hP
  have hq := ciQ_mem P
  have hq0 : ((qOf P : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  have hkr : R.k ≤ R.r := by unfold Ranks.r; have := R.two_le_m; omega
  unfold PhiTopG
  rw [ite_eq_left hP]
  cases sharp
  · simp only [Bool.false_eq_true, ite_false]
    refine ciPhiG_congr hq hq0 _ _ false x x' ?_ ?_ (Nat.le_add_right _ _) hn.a_le fun p p' hp hp' => hD p p' hp (hn.a_eq ▸ hp')
    · unfold Ranks.r; have := R.two_le_m; omega
    · unfold Ranks.r; have := R.two_le_m; omega
  · simp only [ite_true]
    exact xtPhiGS_congr hq hq0 _ _ x x' hkr hn.a_le fun p p' hp hp' => hD p p' hp (hn.a_eq ▸ hp')

theorem xtPhiTopG_int {i : ℕ} (hn : TopNum R i) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x : HomE X.E (R.N i + cOf R i) ((R.N (i + 1) - 1) + 0)) (h : PhiTopG Ch mu sharp i (i + 1) (R.N (i + 1)) P x ≠ 0) :
    ∀ p p', p < (R.N (i + 1) - 1) + 0 → p' < R.N i →
      IntAt P (LocE.entB (qOf P) R.k (cOf R i) (R.N i) 0 (R.N (i + 1) - 1) (fun i => i + 1) (fun i => i + 1) x p p') := by
  unfold PhiTopG at h
  rw [ite_eq_left hP] at h
  intro p p' hp hp'
  cases sharp
  · simp only [Bool.false_eq_true, ite_false] at h
    exact ciPhiG_int _ _ false x h p p' hp (hn.a_eq.symm ▸ hp')
  · simp only [ite_true] at h
    exact xtPhiGS_int _ _ x h p p' hp (hn.a_eq.symm ▸ hp')

def topDat (i : ℕ) (P : rowSG Pr sel mu) (y : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) : X.K :=
  PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1 (prXpG X.E (R.N (i + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R i))) *
    ftY sel mu cst P (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ y) y''

theorem XiTop_eq {u : Pr.Word} (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i))) (p' : ChPt (R := R) sel mu u (i + 1))
    (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiTop Ch sel mu cst i p Y p' x = phiT X.K p.deco.1 p'.deco.1 x *
      ∏ P : rowSG Pr sel mu, topDat Ch sel mu cst i P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p P).symm (repY Y)) := rfl

theorem xt_last_lt (R : Ranks) (j : ℕ) : R.N j - 1 < R.N j := by have := R.N_pos j; omega

theorem xt_atNL (j : ℕ) (a : Sp X.E (R.N j)) : atNL X.E (R.N j) (R.N j - 1) a = a ⟨R.N j - 1, xt_last_lt R j⟩ := by
  unfold atNL
  rw [dite_eq_left (xt_last_lt R j)]
  rfl

theorem xt_split {P : HeightOneSpectrum (𝓞 X.E)} (j : ℕ) (a : Sp X.E (R.N j)) :
    (∀ i, IntAt P (a i)) ↔ (∀ i, IntAt P (prXpG X.E (R.N j) a i)) ∧ IntAt P (atNL X.E (R.N j) (R.N j - 1) a) := by
  rw [xt_atNL]
  constructor
  · intro h
    exact ⟨fun i => h _, h _⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i.1 < R.N j - 1
    · exact h1 ⟨i.1, by omega⟩
    · have : i = ⟨R.N j - 1, xt_last_lt R j⟩ := Fin.ext (by show i.1 = R.N j - 1; have := i.2; omega)
      rw [this]
      exact h2

theorem topDat_congr (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) {i : ℕ} (hn : TopNum R i) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y y₁ : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) (hy : ∀ j, IntAt P.1 ((qOf P.1 : X.E) * y'' j))
    (H : ∀ j : Fin (R.N i), ((∀ l, IntAt P.1 (y (Pi.single j 1) l)) ↔ ∀ l, IntAt P.1 (y₁ (Pi.single j 1) l)) ∧
      ((∀ l, IntAt P.1 (y (Pi.single j 1) l)) → ∀ l, redP P.1 (y (Pi.single j 1) l) = redP P.1 (y₁ (Pi.single j 1) l))) :
    topDat Ch sel mu cst i P y y'' = topDat Ch sel mu cst i P y₁ y'' := by
  classical
  have key := xtLocal (K := X.K) (P := P.1) (q := qOf P.1) (ciQ_mem P.1) (ciQ_notMem_sq hX hPr hP) (k₀ := R.k) (c' := cOf R i)
    (n' := R.N i) (n := R.N (i + 1) - 1) (N := R.N (i + 1)) hn.c0 (PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1)
    (fun x x' h => xtPhiTopG_congr Ch mu hX hPr hn cst.sharp hP x x' h) (fun x h => xtPhiTopG_int Ch mu hn cst.sharp hP x h)
    (cst.psi P) (cst.D P) (hc.D_pos P) (hc.psi_add P) (hc.psi_int P) epsSg (prXpG X.E (R.N (i + 1))) (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1))
    (fun a => xt_split (i + 1) a) y (prXpG X.E (R.N (i + 1)) ∘ₗ y₁) (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ y₁)
    (fun j => ⟨(H j).1.trans (xt_split (i + 1) _), fun hall => ⟨fun l => (H j).2 hall _, by
      show redP P.1 (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) _) = redP P.1 (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) _)
      rw [xt_atNL, xt_atNL]
      exact (H j).2 hall _⟩⟩) y'' hy
  unfold topDat ftY
  rw [ite_eq_left hP, ite_eq_left hP]
  exact key

theorem topDat_int {i : ℕ} (hn : TopNum R i) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y : HomE X.E (R.N i) (R.N (i + 1))) (y'' : Sp X.E (R.N i)) (h : topDat Ch sel mu cst i P y y'' ≠ 0) (j : Fin (R.N i)) (l : Fin (R.N (i + 1))) :
    IntAt P.1 (y (Pi.single j 1) l) := by
  classical
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  refine (xt_split (i + 1) (y (Pi.single j 1))).2 ⟨fun l => ?_, ?_⟩ l
  · have := xtPhiTopG_int Ch mu hn cst.sharp hP _ h1 l.1 j.1 l.2 j.2
    rwa [xtEntB hn.c0 _ (by have := l.2; omega) j.2, LinearMap.comp_apply, LinearMap.comp_apply, xtRes j.2] at this
  · unfold ftY at h2
    rw [ite_eq_left hP] at h2
    by_contra h3
    exact h2 (ite_eq_right fun hh => h3 (hh j))

end TopG

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem frm_exists_c (p p0 : DecoF X.E n ST SG Q) (h : p.deco = p0.deco) :
    ∃ c : GLQ X.E n Q, p = ((1, 1, c) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • p0 := by
  refine ⟨fun P => ⟨(p.fr P)⁻¹ * p0.fr P, ?_⟩, ?_⟩
  · show ∀ x, ((p.fr P)⁻¹ * p0.fr P) x ∈ stdAt X.E n P.1 ↔ x ∈ stdAt X.E n P.1
    intro x
    have hx : p.1.2 P (((p.fr P)⁻¹ * p0.fr P) x) = p0.1.2 P x := LinearEquiv.apply_symm_apply _ _
    have h' : p.1.1 = p0.1.1 := h
    rw [← p.2 P, hx, h', p0.2 P]
  · apply Subtype.ext
    simp only [HSMul.hSMul, SMul.smul]
    refine Prod.ext ?_ ?_
    · have h1 := one_smul (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) p0.1.1
      simp only [HSMul.hSMul, SMul.smul] at h1
      exact h.trans h1.symm
    · funext P
      simp only [DecoF.fr, OneMemClass.coe_one, one_mul, InvMemClass.coe_inv, _root_.mul_inv_rev, inv_inv,
        ← mul_assoc, mul_inv_cancel]

variable (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q)

theorem frm_root (hroot : ∀ c : ↥Θ.grp, ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : X.Kˣ) : X.K) ^ m = 1) (g : FrmG Λ Θ) :
    ∃ m : ℕ, 0 < m ∧ (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) ^ m = 1 := by
  haveI : ∀ w : SG, Finite (𝓞 X.E ⧸ w.1.asIdeal) := fun w =>
    Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  obtain ⟨m2, hm2, h2⟩ := hroot g.2.2
  have hfo : IsOfFinOrder g.2.1 := isOfFinOrder_of_finite _
  have ha : ((Λ.chr g.2.1 : X.Kˣ) : X.K) ^ orderOf g.2.1 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  refine ⟨orderOf g.2.1 * m2, Nat.mul_pos hfo.orderOf_pos hm2, ?_⟩
  rw [Units.val_mul, mul_pow, pow_mul, ha, one_pow, one_mul, mul_comm (orderOf _) m2, pow_mul, h2,
    one_pow]


open Classical in
theorem frmGSD_ok_of_finIdx (hX : X.Ok) (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (hC : C.Eqv)
    (hfi : ∀ P : Q, Finite (↥(GLint X.E n P.1) ⧸ (Θ P).H))
    (hroot : ∀ c : ↥Θ.grp, ∃ m : ℕ, 0 < m ∧ ((Θ.chr c : X.Kˣ) : X.K) ^ m = 1) : (frmGSD (C.pull DecoF.deco) Λ Θ).Ok := by
  refine { fin_orb := ?_, fin_stab := ?_, nab_smul := ?_, del_smul := ?_, inv := ?_ }
  · obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have : Finite s := hs

    let pt : s → (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) → Option (DecoF X.E n ST SG Q) := fun d cb =>
      if h : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d.1 then
        some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • h.choose) else none
    have hfin : Finite (Option (s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H))) := inferInstance
    by_cases hne : Nonempty (frmGSD (C.pull DecoF.deco) Λ Θ).Cl
    swap
    · have := not_nonempty_iff.1 hne
      exact inferInstance
    obtain ⟨c00⟩ := hne
    refine Finite.of_surjective (fun a : s × (∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H) =>
      match pt a.1 a.2 with
      | some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p
      | none => c00) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h p =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep (DecoF.deco p)

      let p1 : DecoF X.E n ST SG Q := ((g, 1, 1) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q)⁻¹ • p
      have hp1 : p1.deco = d0 := by
        show ((g, (1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG))⁻¹ • p.deco = d0
        rw [hg, inv_smul_smul]
      have hex : ∃ p0 : DecoF X.E n ST SG Q, p0.deco = d0 := ⟨p1, hp1⟩
      obtain ⟨c, hc⟩ := frm_exists_c p1 hex.choose (hp1.trans hex.choose_spec.symm)

      let cb : ∀ P : Q, ↥(GLint X.E n P.1) ⧸ (Θ P).H := fun P => QuotientGroup.mk ((c P)⁻¹)
      have hout : ∀ P : Q, ((c P)⁻¹)⁻¹ * (cb P).out ∈ (Θ P).H := fun P => QuotientGroup.eq.1 (QuotientGroup.out_eq' (cb P)).symm
      refine ⟨(⟨d0, hd0⟩, cb), ?_⟩
      have hpt : pt ⟨d0, hd0⟩ cb = some (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • hex.choose) := dif_pos hex
      show (match pt ⟨d0, hd0⟩ cb with
        | some p => (frmGSD (C.pull DecoF.deco) Λ Θ).cls p
        | none => c00) = _
      rw [hpt]
      let θ : ↥Θ.grp := ⟨fun P => ((c P)⁻¹)⁻¹ * (cb P).out, fun P _ => hout P⟩
      refine ((frmGSD (C.pull DecoF.deco) Λ Θ).cls_eq_iff _ p).mpr ⟨((g, 1, θ) : FrmG Λ Θ)⁻¹, ?_⟩
      refine inv_smul_eq_iff.2 (Eq.symm ?_)
      show ((g, (1 : GLG (E := X.E) (n := n) (SG := SG)), (θ : GLQ X.E n Q)) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) •
        (((1, 1, fun P => ((cb P).out)⁻¹) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) • hex.choose) = p
      rw [← mul_smul]
      have e : ((g, (1 : GLG (E := X.E) (n := n) (SG := SG)), (θ : GLQ X.E n Q)) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG) × GLQ X.E n Q) * (1, 1, fun P => ((cb P).out)⁻¹) =
          (g, 1, 1) * (1, 1, c) := by
        refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
        funext P
        show ((c P)⁻¹)⁻¹ * (cb P).out * ((cb P).out)⁻¹ = 1 * c P
        group
      rw [e, mul_smul, ← hc]
      exact smul_inv_smul _ p
  · intro p
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (DecoF.deco p : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (frmGSD (C.pull DecoF.deco) Λ Θ).G p =>
        (⟨(a.1.1, (a.1.2.1 : GLG (E := X.E) (n := n) (SG := SG))), congrArg DecoF.deco a.2⟩ :
          MulAction.stabilizer (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (DecoF.deco p : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)))) ?_
    intro a b hab
    have h0 : ((a.1.1, (a.1.2.1 : GLG (E := X.E) (n := n) (SG := SG))) : UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) = (b.1.1, (b.1.2.1 : GLG (E := X.E) (n := n) (SG := SG))) :=
      congrArg Subtype.val hab
    exact Subtype.ext (dga_frm_stab_inj Λ Θ p a.2 b.2 (Prod.mk.inj h0).1)
  · intro g d
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    exact (hC.nab_smul (g.1, (g.2.1 : GLG (E := X.E) (n := n) (SG := SG))) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  · intro g d
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    exact (hC.del_smul (g.1, (g.2.1 : GLG (E := X.E) (n := n) (SG := SG))) (DecoF.deco d)).trans (map_root_smul _ _ hm hc).symm
  · intro g (x : C.V) (y : C.V)
    obtain ⟨m, hm, hc⟩ := frm_root Λ Θ hroot g
    show C.pair ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 x)
      ((((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star (((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ)) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

end Gen

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

theorem chF_ok_of_finIdx (hX : X.Ok) (u : Pr.Word) (j : ℕ)
    (hfi : ∀ (b : L.β j) (P : QE sel (mu : Chr X.F X.E X.K)), Finite (↥(GLint X.E (R.N j) P.1) ⧸ (L.levQ j b P).H))
    (hroot : ∀ (b : L.β j) (c : ↥(L.levQ j b).grp), ∃ m : ℕ, 0 < m ∧ (((L.levQ j b).chr c : X.Kˣ) : X.K) ^ m = 1) :
    (chF W sel mu L u j).Ok := by
  intro b
  have hC : (colVal W u j (Pr.vT u) Pr.vGs).Eqv :=
    ⟨colVal_nab_smul W u j, colVal_del_smul W u j, roundPk_inv X _ _ hX.emb_star⟩
  exact frmGSD_ok_of_finIdx (L.levG j b) (L.levQ j b) hX (colVal W u j (Pr.vT u) Pr.vGs)
    hC (hfi b) (hroot b)

end Chain

end Formalism.L2.Col
end
end
