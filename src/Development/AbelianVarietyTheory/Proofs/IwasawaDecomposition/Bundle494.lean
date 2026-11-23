module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle485
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle484
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedInvMulLe
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle486
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT

theorem chr_mul_prod_top_core {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι)
    (Λ : LevFam B.fields.E B.fields.K (B.R.N B.R.m) (B.primes X).vGs)
    (hΛ : ∀ w, Λ w = levDiag (Nat.sub_le _ 1) (rowTyG I.Ch (rPsymF I.Ch) w))
    (Θ : LevQFam B.fields.E B.fields.K (B.R.N B.R.m) (I.Q a))
    (hΘ : ∀ Q, Θ Q = levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
      (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q))
    (x : Λ.grp) (y : Θ.grp)
    (g g' : SBof I a → Sp B.fields.E (B.R.N B.R.m) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N B.R.m)) (z : SBof I a → B.fields.K)
    (H : ∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) B.R.m P (g P) (z P) ∧
      (g' P ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N B.R.m) P.1 ∧
        (∀ h : P.1 ∈ (B.primes X).vGs, ∀ v ∈ stdAt B.fields.E (B.R.N B.R.m) P.1,
          redV P.1 (g' P v) = ((x.1 ⟨P.1, h⟩)⁻¹).1.mulVec (redV P.1 v)) ∧
        ∀ h : P.1 ∈ I.Q a, g' P = ((y.1 ⟨P.1, h⟩)⁻¹).1) ∧
      CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) :
    (((Λ.chr x * Θ.chr y : B.fields.Kˣ) : B.fields.K)) * ∏ P, z P = 1 := by
  classical
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_left.2 fun P h1 h2 => Q_notMem_of_ok hOk a P h2 h1
  have e2 : ∏ P, z P = (∏ w : (B.primes X).vGs, z ⟨w.1, Finset.mem_union_left _ w.2⟩) *
      ∏ Q : I.Q a, z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ := by
    rw [← Fintype.prod_equiv (Equiv.Finset.union _ _ hd) _ _ (fun _ => rfl), Fintype.prod_sum_type]
    rfl
  rw [e2, LevFam.chr_apply, levQ_chr_apply, Units.val_mul, Units.coe_prod, Units.coe_prod]
  have hG : ∀ w : (B.primes X).vGs, (((Λ w).lam ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨w.1, Finset.mem_union_left _ w.2⟩ = 1 := by
    intro w
    obtain ⟨⟨g'', hg''m, hpr, -, hz⟩, ⟨hg'G, hred, -⟩, hc⟩ := H ⟨w.1, Finset.mem_union_left _ w.2⟩
    have key : ∀ (l : Lev (𝓞 B.fields.E ⧸ w.1.asIdeal) B.fields.K (B.R.N B.R.m)),
        l = levDiag (Nat.sub_le _ 1) (rowTyG I.Ch (rPsymF I.Ch) w) → ∀ A (hA : A ∈ l.H),
        ∃ h0, ∃ hh0 : h0 ∈ (rowTyG I.Ch (rPsymF I.Ch) w).H, A = diagEmb _ (Nat.sub_le (B.R.N B.R.m) 1) h0 ∧
          l.lam ⟨A, hA⟩ = (rowTyG I.Ch (rPsymF I.Ch) w).lam ⟨h0, hh0⟩ := by
      intro l hl A hA
      subst hl
      obtain ⟨h0, hh0, rfl⟩ := hA
      exact ⟨h0, hh0, rfl, levDiag_lam _ _ rfl _ hh0⟩
    obtain ⟨h0, hh0, eA, elam⟩ := key _ (hΛ w) _ (x.2 w (Set.mem_univ w))
    rw [elam]
    have hmem : g'' ∈ LocE.JGsym w.1 (qOf w.1) B.R.k B.R.rS B.R.r B.R.t (B.R.N B.R.m - 1) 0 := by
      have h1 := hg''m
      unfold GlobalTheory.TwU.rowLevTop at h1
      rwa [if_pos w.2, hOk.sharp a, if_pos rfl] at h1
    have hz' : z ⟨w.1, Finset.mem_union_left _ w.2⟩ = LocE.lamGBS (qOf w.1) (psi0P I.Ch w.1) (chiP I.Ch w.1)
        B.R.k B.R.r B.R.t B.R.m (B.R.N B.R.m - 1) 0 g''.toLinearMap := by
      rw [hz]
      unfold GlobalTheory.TwU.rowChrTop
      rw [if_pos w.2, hOk.sharp a, if_pos rfl]
    have eA' : x.1 ⟨w.1, w.2⟩ = diagEmb _ (Nat.sub_le (B.R.N B.R.m) 1) h0 := eA
    have hred' : ∀ v ∈ stdAt B.fields.E (B.R.N B.R.m) w.1, redV w.1 (g' ⟨w.1, Finset.mem_union_left _ w.2⟩ v) =
        ((diagEmb (𝓞 B.fields.E ⧸ w.1.asIdeal) (Nat.sub_le (B.R.N B.R.m) 1) h0)⁻¹ : GL (Fin (B.R.N B.R.m)) _).1.mulVec (redV w.1 v) := by
      intro v hv
      rw [hred w.2 v hv, eA']
    have hc' : CongE w.1 1 (g ⟨w.1, Finset.mem_union_left _ w.2⟩) (g' ⟨w.1, Finset.mem_union_left _ w.2⟩) := by
      have h1 := hc
      unfold GlobalTheory.TwU.topDep at h1
      rwa [if_pos w.2] at h1
    rw [mul_comm, hz']
    exact GlobalTheory.T.typePrime_rowType_topRestriction_mul_levelChar_eq_one I.Ch w h0 hh0 _ _ g'' hmem hpr hg'G hred' hc'
  have hQ : ∀ Q : I.Q a, (((Θ Q).lam ⟨y.1 Q, y.2 Q (Set.mem_univ Q)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ = 1 := by
    intro Q
    obtain ⟨⟨g'', hg''m, hpr, -, hz⟩, ⟨-, -, hgy⟩, hc⟩ := H ⟨Q.1, Finset.mem_union_right _ Q.2⟩
    have hnot : Q.1 ∉ (B.primes X).vGs := Q_notMem_of_ok hOk a Q.1 Q.2
    have key : ∀ (l : LevI B.fields.E B.fields.K (B.R.N B.R.m) Q.1),
        l = levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M) (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q) →
        ∀ k (hk : k ∈ l.H), ∃ hk' : k ∈ (levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
          (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q)).H,
          l.lam ⟨k, hk⟩ = (levCong (N_m_succ B.R) Q.1 (topDep B.R (I.cst a).M)
            (rowTyQ B.R (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q)).lam ⟨k, hk'⟩ := by
      intro l hl k hk
      subst hl
      exact ⟨hk, rfl⟩
    obtain ⟨hk', elam⟩ := key _ (hΘ Q) _ (y.2 Q (Set.mem_univ Q))
    rw [elam]
    have hmem : g'' ∈ LocE.JQ Q.1 (qOf Q.1) B.R.r (B.R.N B.R.m - 1) 0 := by
      have h1 := hg''m
      unfold GlobalTheory.TwU.rowLevTop at h1
      rwa [if_neg hnot] at h1
    have hz' : z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ = LocE.lamQB (resChar (I.tup a : Chr B.fields.F B.fields.E B.fields.K) Q.1)
        B.R.r (B.R.N B.R.m - 1) g''.toLinearMap := by
      rw [hz]
      unfold GlobalTheory.TwU.rowChrTop
      rw [if_neg hnot]
    have hc' : CongE Q.1 (2 * (I.cst a).M) (g ⟨Q.1, Finset.mem_union_right _ Q.2⟩) ((y.1 Q)⁻¹).1 := by
      have h1 := hc
      unfold GlobalTheory.TwU.topDep at h1
      rw [if_neg hnot, hgy Q.2] at h1
      exact h1
    rw [mul_comm, hz']
    exact GlobalTheory.T.twistPrime_rowType_topRestriction_mul_levelChar_eq_one (I.tup a : Chr B.fields.F B.fields.E B.fields.K) (I.Q a) Q _ _ (hOk.idx_ok a).cst_ok.M_pos (y.1 Q) hk' _ g'' hmem hpr hc'
  calc _ = (∏ w : (B.primes X).vGs, (((Λ w).lam ⟨x.1 w, x.2 w (Set.mem_univ w)⟩ : B.fields.Kˣ) : B.fields.K) *
        z ⟨w.1, Finset.mem_union_left _ w.2⟩) * ∏ Q : I.Q a, (((Θ Q).lam ⟨y.1 Q, y.2 Q (Set.mem_univ Q)⟩ : B.fields.Kˣ) : B.fields.K) *
      z ⟨Q.1, Finset.mem_union_right _ Q.2⟩ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]; ring
    _ = 1 := by
        rw [Finset.prod_eq_one fun w _ => hG w, Finset.prod_eq_one fun Q _ => hQ Q, one_mul]

theorem chr_mul_prod_topVal : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ), i = B.R.m → ∀ (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (g g' : SBof I a → Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)) (z : SBof I a → B.fields.K), (∀ P, GlobalTheory.TwU.TopLev (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P (g P) (z P) ∧ LiftsInv I κ P (g' P) ∧ CongE P.1 (GlobalTheory.TwU.topDep I.sel (I.tup a) (I.cst a) P) (g P) (g' P)) → (((I.stp u a i).chr b κ : B.fields.Kˣ) : B.fields.K) * ∏ P, z P = 1 := by
  intro B X I hOk u a i hi b κ g g' z H
  subst hi
  rcases b with ⟨_ | b1, hb⟩
  swap
  · exact absurd (hb.1 rfl) (lt_irrefl _)
  exact chr_mul_prod_top_core I hOk a _ (fun w => congrFun (topLevAt_levG_m I.Ch I.sel (I.tup a) I.Ps _) w) _
    (fun Q => congrFun (topLevAt_levQ_m I.Ch I.sel (I.tup a) I.Ps _) Q) κ.2.1 κ.2.2 g g' z H

end GlobalTheory.Mem.Col2.AdT
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.AdTieNear

theorem entries_le_of_add_mul {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ))) {n : ℕ}
    (A D : Matrix (Fin n) (Fin n) K) (c : WithZero (Multiplicative ℤ)) (hA : ∀ r s, v (A r s) < 1)
    (h : ∀ r s, v ((D + A * D) r s) ≤ c) (r s : Fin n) : v (D r s) ≤ c := by
  obtain ⟨p, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v (D p.1 p.2)) ⟨(r, s), Finset.mem_univ _⟩
  refine (hmax (r, s) (Finset.mem_univ _)).trans ?_
  by_cases hμ : v (D p.1 p.2) = 0
  · rw [hμ]; exact zero_le'
  have hlt : v ((A * D) p.1 p.2) < v (D p.1 p.2) := by
    rw [Matrix.mul_apply]
    refine Valuation.map_sum_lt _ hμ fun k _ => ?_
    rw [map_mul]
    calc v (A p.1 k) * v (D k p.2) ≤ v (A p.1 k) * v (D p.1 p.2) :=
          mul_le_mul_right (hmax (k, p.2) (Finset.mem_univ _)) _
      _ < 1 * v (D p.1 p.2) := mul_lt_mul_of_pos_right (hA p.1 k) (zero_lt_iff.2 hμ)
      _ = v (D p.1 p.2) := one_mul _
  have e := Valuation.map_add_eq_of_lt_left v hlt
  rw [← e, ← Matrix.add_apply]
  exact h p.1 p.2

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

theorem adAt_ratA {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (G : GL (Fin n) E) (r s : Fin n) :
    adAt F P ((GlobalTheory.TwU.ratA F G : GL (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) ((G : Matrix (Fin n) (Fin n) E) r s) := by
  exact adAt_inclE F P _

theorem congE_of_near (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (d d' : ℕ) (hd' : 1 ≤ d') (hdd : d' ≤ d)
    (x : GL (Fin n) (AfE F E)) (g g' : Sp E n ≃ₗ[E] Sp E n) (G G' : GL (Fin n) E)
    (hG : ∀ w, (G : Matrix (Fin n) (Fin n) E) *ᵥ w = g w) (hG' : ∀ w, (G' : Matrix (Fin n) (Fin n) E) *ᵥ w = g' w)
    (hg : g ∈ Formalism.L2.Col.GLint E n P)
    (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ))
    (hy : ∀ r s, Valued.v (adAt F P (((x⁻¹ * GlobalTheory.TwU.ratA F G : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)
      - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(d : ℤ)))
    (hy' : ∀ r s, Valued.v (adAt F P (((x⁻¹ * GlobalTheory.TwU.ratA F G' : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s)
      - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(d' : ℤ))) :
    CongE P d' g' g := by
  set φ := adAt F P
  set y := x⁻¹ * GlobalTheory.TwU.ratA F G
  set y' := x⁻¹ * GlobalTheory.TwU.ratA F G'
  set H : GL (Fin n) E := G⁻¹ * G'
  have hyH : y * GlobalTheory.TwU.ratA F H = y' := by
    simp only [y, y', H, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  set Y : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (y : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  set Y' : Matrix (Fin n) (Fin n) (P.adicCompletion E) := (y' : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  set R : Matrix (Fin n) (Fin n) (P.adicCompletion E) := ((GlobalTheory.TwU.ratA F H : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map φ
  have hYR : Y * R = Y' := by
    simp only [Y, Y', R, ← Matrix.map_mul, ← Units.val_mul, hyH]
  have hdA : ∀ r s, Valued.v ((Y - 1) r s) < 1 := fun r s => by
    refine lt_of_le_of_lt (hy r s) ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hsum : ∀ r s, Valued.v (((R - 1) + (Y - 1) * (R - 1)) r s) ≤ WithZero.exp (-(d' : ℤ)) := fun r s => by
    have e : (R - 1) + (Y - 1) * (R - 1) = (Y' - 1) - (Y - 1) := by
      rw [← hYR]; noncomm_ring
    rw [e, Matrix.sub_apply]
    refine Valuation.map_sub_le _ (hy' r s) ((hy r s).trans ?_)
    rw [WithZero.exp_le_exp]; omega
  have hD := entries_le_of_add_mul Valued.v (Y - 1) (R - 1) _ hdA hsum

  have hH : ∀ r s, Valued.v (algebraMap E (P.adicCompletion E) (((H : Matrix (Fin n) (Fin n) E) - 1) r s)) ≤ WithZero.exp (-(d' : ℤ)) := by
    intro r s
    have e : (R - 1) r s = algebraMap E (P.adicCompletion E) (((H : Matrix (Fin n) (Fin n) E) - 1) r s) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub]
      simp only [R, Matrix.map_apply, φ, adAt_ratA]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [← e]; exact hD r s
  intro w hw
  have hHw : g ((H : Matrix (Fin n) (Fin n) E) *ᵥ w) = g' w := by
    rw [← hG, Matrix.mulVec_mulVec, ← Units.val_mul, ← hG']
    simp only [H, mul_inv_cancel_left]
  have e : (((qOf P : ℕ) : E) ^ d')⁻¹ • (g' w - g w) =
      g ((((qOf P : ℕ) : E) ^ d')⁻¹ • (((H : Matrix (Fin n) (Fin n) E) - 1) *ᵥ w)) := by
    rw [map_smul, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, hHw]
  rw [e]
  refine (hg _).2 ?_
  rw [GlobalTheory.Mem.ColAd.mem_stdAt_val] at hw ⊢
  intro l
  have hs : Valued.v (algebraMap E (P.adicCompletion E) ((((H : Matrix (Fin n) (Fin n) E) - 1) *ᵥ w) l)) ≤ WithZero.exp (-(d' : ℤ)) := by

    simp only [Matrix.mulVec, dotProduct, map_sum]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul, map_mul]
    calc _ ≤ WithZero.exp (-(d' : ℤ)) * 1 := mul_le_mul' (hH l k) (hw k)
      _ = _ := mul_one _
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_mul, map_inv₀, map_inv₀, map_pow, map_pow, map_natCast, hq]
  calc _ ≤ (WithZero.exp (-1 : ℤ) ^ d')⁻¹ * WithZero.exp (-(d' : ℤ)) := mul_le_mul_right hs _
    _ = 1 := by
      rw [← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
      simp

end Gen

end GlobalTheory.Mem.Col2.AdT.AdTieNear

namespace GlobalTheory.Mem.Col2.AdT.AdTieNear



theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (i : ℕ) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) (dep dep' : SBof I a → ℕ) (P : SBof I a) (κ : GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) (g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)), g ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → 1 ≤ dep' P → dep' P ≤ dep P → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep P κ g → GlobalTheory.TwU.InFrame (i := i) (sm I l Z) fb dep' P κ g' → CongE P.1 (dep' P) g' g := by
  intro B X I hOk l Z a i fb dep dep' P κ g g' hg h1 hdd hF hF'
  unfold GlobalTheory.TwU.InFrame GlobalTheory.TwU.NearAt at hF hF'
  have hq := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) 0 P 1).2.1
  have hy := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a _ (dep P) P _).2.2.1 hF
  have hy' := (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a _ (dep' P) P _).2.2.1 hF'
  exact congE_of_near (F := B.host.F) P.1 (dep P) (dep' P) h1 hdd _ g g'
    (GlobalTheory.TwU.seamGL (sm I l Z) g) (GlobalTheory.TwU.seamGL (sm I l Z) g')
    (fun w => GlobalTheory.TwU.seamGL_mulVec (sm I l Z) g w) (fun w => GlobalTheory.TwU.seamGL_mulVec (sm I l Z) g' w)
    hg hq hy hy'

end GlobalTheory.Mem.Col2.AdT.AdTieNear
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.FrameMove

open GlobalTheory.Mem.Col2.LevFun GlobalTheory.Mem.Col2.Splice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inv_mul_ratA_apply {n : ℕ} (g : GL (Fin n) (AfE F E)) (γ : GL (Fin n) E) (r s : Fin n) :
    ((g⁻¹ * GlobalTheory.TwU.ratA F γ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s =
      pullV g (fun t => (γ : Matrix (Fin n) (Fin n) E) t s) r := by
  unfold pullV
  rw [Units.val_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rfl

theorem val_sub_lt_of_liftFr [StarRing E] {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (w : SG) (r s : Fin n) :
    Valued.v (adAt F w.1 (pullV g (p.deco.1.liftFr w (Pi.single s 1)) r) -
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) r s) < 1 := by
  classical
  have hL := GlobalTheory.TopStep.liftFr_spec p.deco.2 w
  have hs := single_mem_stdAt (E := E) (n := n) w.1 s
  have hx : p.deco.1.liftFr w (Pi.single s 1) ∈ p.deco.1.at w.1 := (hL.1 _).2 hs
  obtain ⟨t, ht, htx⟩ := (mem_locP _ _ _).1 hx
  have h1 := h.be w _ htx r
  rw [p.deco.2.be_smul w t _ hx, hL.2 _ hs, redV_single, adAt_pullV_osmul] at h1
  have h2 : HasRes w.1 (adAt F w.1 (pullV g (p.deco.1.liftFr w (Pi.single s 1)) r))
      (Ideal.Quotient.mk w.1.asIdeal (if r = s then 1 else 0)) := by
    refine hasRes_of_mul ht ?_
    convert h1 using 1
    by_cases e : r = s
    · subst e; simp
    · simp [e]
  have h3 := hasRes_sub_lt h2
  convert h3 using 3
  by_cases e : r = s
  · subst e; simp
  · simp [e, Matrix.one_apply]

theorem val_mul_sub_one_le {P : HeightOneSpectrum (𝓞 E)} {n N : ℕ} {A B : Matrix (Fin n) (Fin n) (P.adicCompletion E)}
    (hA : ∀ r s, Valued.v (A r s - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (hB : ∀ r s, Valued.v (B r s - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (r s : Fin n) :
    Valued.v ((A * B) r s - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  first
  | exact @_root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le
  | exact _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le
  | (apply _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le ..)

theorem le_exp_neg_one_of_lt_one' {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with h0 | h0
  · rw [h0]; exact zero_le'
  rw [← WithZero.exp_log h0] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem seamGL_apply {D : D7} {Xf : Fields} (sd : Seam D Xf) {n : ℕ} (f : Sp Xf.E n ≃ₗ[Xf.E] Sp Xf.E n) (t s : Fin n) :
    ((GlobalTheory.TwU.seamGL sd f : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) t s = sd.iE (f (Pi.single s 1) t) := by
  have h : ((GlobalTheory.TwU.seamGL sd f : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' f.toLinearMap).map (sd.iE : Xf.E →+* D.host.E) := rfl
  rw [h, Matrix.map_apply, LinearMap.toMatrix'_apply]
  rfl

theorem adAt_pullV_fr [StarRing E] {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) (r s : Fin n) :
    adAt F P.1 (pullV g (p.fr P (Pi.single s 1)) r) = (1 : Matrix (Fin n) (Fin n) (P.1.adicCompletion E)) r s := by
  have e1 : GlobalTheory.Mem.ColAd.locM P.1 (g⁻¹ * g) = 1 := by rw [inv_mul_cancel, GlobalTheory.Mem.ColAd.locM_one]
  rw [← e1, GlobalTheory.Mem.ColAd.locM_mul, Matrix.mul_apply]
  unfold pullV

  rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, adAt_inclE, ← h.fr P t s]
  rfl

theorem frame_near : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ∀ P : SBof I a, GlobalTheory.TwU.NearAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (((K (chOf c)).y ⟨c, rfl⟩).1 * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P)) (GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P)) := by
  classical
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c fb hfb P
  have hpt := hR.pt c
  have hd := fun z => (GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a ((I.rec7 l Z).R.N i) ((I.cst a).D P) P z).2.2
  unfold GlobalTheory.TwU.NearAt
  rw [hd]
  have hfb2 := (hd _).1 (hfb P).2
  have e : ∀ {G : Type} [Group G] (y k A C : G), (y * A)⁻¹ * C = (A⁻¹ * k) * ((y * k)⁻¹ * C) := by
    intros; group
  have key := e (G := GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) ((K (chOf c)).y ⟨c, rfl⟩).1
    (k (chOf c)) (GlobalTheory.TwU.ratA _ (fb P))
    (GlobalTheory.TwU.ratA _ (GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P)))
  rw [key]
  intro r s
  show Valued.v (GlobalTheory.Mem.ColAd.locM P.1 (_ * _) r s - _) ≤ _
  erw [GlobalTheory.Mem.ColAd.locM_mul]
  refine val_mul_sub_one_le hfb2 ?_ r s
  clear r s
  intro r s
  show Valued.v (adAt B.host.F P.1 (_) - _) ≤ _
  rw [inv_mul_ratA_apply]
  have hfr := frsF_eq_ptFr I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P
  have hcol : (fun t => ((GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P) :
      GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) :
        Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) t s) =
      ptFr ((I.stp u a i).rep c).1.1 P.1 (Pi.single s 1) :=
    funext fun t => by rw [seamGL_apply]; exact congrArg (fun f => f (Pi.single s 1) t) hfr
  rw [hcol]
  by_cases hG : P.1 ∈ (B.primes X).vGs
  · rw [(hOk.idx_ok a).depthG P hG]
    have e2 : ptFr ((I.stp u a i).rep c).1.1 P.1 = (extTo I.SQ ((I.stp u a i).rep c).1.1).deco.1.liftFr ⟨P.1, hG⟩ := by
      unfold ptFr
      rw [dite_eq_left hG]
      rfl
    rw [e2]
    exact le_exp_neg_one_of_lt_one' (val_sub_lt_of_liftFr hpt ⟨P.1, hG⟩ r s)
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hG
    have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
    have e3 : ptFr ((I.stp u a i).rep c).1.1 P.1 = (extTo I.SQ ((I.stp u a i).rep c).1.1).fr ⟨P.1, hSQ⟩ := rfl
    have h0 := adAt_pullV_fr hpt ⟨P.1, hSQ⟩ r s
    rw [e3]
    erw [h0, sub_self, map_zero]
    exact zero_le'

end GlobalTheory.Mem.Col2.AdT.FrameMove
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT.Approx

open scoped TensorProduct

variable {F E : Type} {_iF : Field F} [NumberField F] {_iE : Field E} [NumberField E] {_iA : Algebra F E} {n : ℕ}

theorem comp_mul_rat (P : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) :
    ((k⁻¹ * GlobalTheory.TwU.ratA F γ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) _).map (adAt F P) =
      ((Formalism.UG.bc (adAt F P) k)⁻¹ : GL (Fin n) (P.adicCompletion E)).1 * γ.1.map (algebraMap E (P.adicCompletion E)) := by
  rw [← map_inv, Units.val_mul, Matrix.map_mul]
  congr 1
  show (γ.1.map (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (adAt F P) = _
  rw [Matrix.map_map]
  congr 1
  funext x
  exact adAt_inclE F P x

theorem comp_rat_mul (P : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E) :
    (((GlobalTheory.TwU.ratA F γ)⁻¹ * k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) _).map (adAt F P) =
      (γ⁻¹).1.map (algebraMap E (P.adicCompletion E)) * (Formalism.UG.bc (adAt F P) k : GL (Fin n) (P.adicCompletion E)).1 := by
  rw [← map_inv, Units.val_mul, Matrix.map_mul]
  congr 1
  show ((γ⁻¹).1.map (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F))).map (adAt F P) = _
  rw [Matrix.map_map]
  congr 1
  funext x
  exact adAt_inclE F P x

end GlobalTheory.Mem.Col2.AdT.Approx

namespace GlobalTheory.Mem.Col2.AdT

theorem frNear_exists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (n : ℕ) (k : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), ∃ fb : SBof I a → GL (Fin n) (I.rec7 l Z).host.E, FrNear I l Z a k fb := by
  intro B X I hOk l Z a n k
  have key : ∀ P : SBof I a, ∃ γ : GL (Fin n) (I.rec7 l Z).host.E,
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (k⁻¹ * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F γ) ∧
      GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) ((GlobalTheory.TwU.ratA (I.rec7 l Z).host.F γ)⁻¹ * k) := by
    intro P
    obtain ⟨γ, hγ⟩ := GlobalTheory.T.numberFieldGL_dense_in_completionGL_two_sided B.fields.E P.1 n ((I.cst a).D P) (Formalism.UG.bc (adAt B.host.F P.1) k)
    refine ⟨γ, ?_, ?_⟩
    · rw [(GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a n ((I.cst a).D P) P _).2.2]
      intro r s
      have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) _ => M r s) (Approx.comp_mul_rat P.1 k γ)
      simp only [Matrix.map_apply] at h1
      have h2 := (hγ r s).1
      rw [Matrix.sub_apply] at h2
      convert h2 using 3
      exact h1
    · rw [(GlobalTheory.T.adelicMatrixCongruenceBadPrime_iff_completion I hOk l Z a n ((I.cst a).D P) P _).2.2]
      intro r s
      have h1 := congrArg (fun M : Matrix (Fin n) (Fin n) _ => M r s) (Approx.comp_rat_mul P.1 k γ)
      simp only [Matrix.map_apply] at h1
      have h2 := (hγ r s).2
      rw [Matrix.sub_apply] at h2
      convert h2 using 3
      exact h1
  choose fb hfb using key
  exact ⟨fb, hfb⟩

end GlobalTheory.Mem.Col2.AdT
end
