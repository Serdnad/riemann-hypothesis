module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiAtTransport
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle359
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle313
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle551
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTranslateOrthogonalOfSupportMovedOff
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Transport.TwistCpl

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep

variable {E : Type} [Field E] [NumberField E]

theorem intAt_iff_val (P : HeightOneSpectrum (𝓞 E)) (a : E) : IntAt P a ↔ P.valuation E a ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 : P.valuation E (algebraMap (𝓞 E) E s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, h1, one_mul] at h2
    rw [h2]
    exact P.valuation_le_one r
  · intro h
    obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer a h
    exact ⟨n, d, d.2, by rw [mul_comm]; exact hnd⟩

theorem intAt_inv_pow_mul {P : HeightOneSpectrum (𝓞 E)} {q B c : ℕ} (hq : (q : E) ≠ 0) {z : E}
    (hz : P.valuation E z ≤ P.valuation E (((q ^ B * c : ℕ) : ℕ) : E)) : IntAt P (((q : E) ^ B)⁻¹ * z) := by
  rw [intAt_iff_val, map_mul, map_inv₀]
  have hc : P.valuation E ((c : ℕ) : E) ≤ 1 :=
    (intAt_iff_val P _).1 ⟨(c : 𝓞 E), 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have h1 : P.valuation E z ≤ P.valuation E ((q : E) ^ B) := by
    refine hz.trans ?_
    rw [Nat.cast_mul, Nat.cast_pow, map_mul]
    exact mul_le_of_le_one_right' hc
  have h0 : P.valuation E ((q : E) ^ B) ≠ 0 := (Valuation.ne_zero_iff _).2 (pow_ne_zero _ hq)
  exact (inv_mul_le_one₀ (zero_lt_iff.2 h0)).2 h1

end GlobalTheory.Transport.TwistCpl

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

theorem GlobalTheory.Transport.TwistCpl.psiAt_transport_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (hm : i + 2 = B.R.m) (al : (I.idx a).β i) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a))
    (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u (i)) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N (i))) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i)) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 → cosetIn q' = cosetIn p' →
    ∃ M : ℕ, 0 < M ∧ ∀ M₀ : ℕ, M ∣ M₀ → ∀ x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P)
                (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)
                ((Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P).symm (Formalism.L2.Col.repY p'.1.2)) =
        Formalism.L2.Col.PsiAt I.Ch I.sel (I.tup a) (I.cst a) i P ((I.idx a).h i al P)
          (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x)
          ((Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P).symm (Formalism.L2.Col.repY q'.1.2)) := by
  intro B X I hI l u a i hm al P p q p' q' k y k' y' hp hN hp' hN' hq hq' hc
  have hL := hI.idx_ok a
  rw [show B.R.m - 2 = i by omega] at hL
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · refine ⟨Formalism.L2.Col.qOf P.1, Nat.pos_of_ne_zero fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    exact GlobalTheory.Transport.Pen.psiAt_frames (base_fields_primes_ok B X).1 l.pr hL al P hP p q p' q' hp hN hp' hN' hq hq' hc
      (GlobalTheory.Transport.Pen.lt_of_congAt hx)
  · have hPQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hP
    have hq0n : Formalism.L2.Col.qOf P.1 ≠ 0 := fun h => P.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    have hq0 : ((Formalism.L2.Col.qOf P.1 : ℕ) : B.fields.E) ≠ 0 := Nat.cast_ne_zero.2 hq0n
    refine ⟨Formalism.L2.Col.qOf P.1 ^ (I.cst a).B, pow_pos (Nat.pos_of_ne_zero hq0n) _, ?_⟩
    rintro _ ⟨c, rfl⟩ x x₀ hx
    have hr := GlobalTheory.T.twist_prime_congruent_maps_frame_readings_bound I u a i P hPQ (GlobalTheory.Mem.Df.disjoint_vGs_Q I hI l a) p q p' q' k y k' y' hp hN hp' hN' hq hq' _ x x₀ hx
    have hm' : i + 1 + 1 = B.R.m := by omega
    set x₁ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀ with hx₁
    set x₂ := Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x with hx₂
    set y₁ := (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P).symm (Formalism.L2.Col.repY p'.1.2) with hy₁
    set y₂ := (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P).symm (Formalism.L2.Col.repY q'.1.2) with hy₂
    have s1 := hL.psiInvX al P x₁ (x₂ - x₁) y₁ fun s l => by
      have := hr l s
      rw [Matrix.sub_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply] at this
      exact GlobalTheory.Transport.TwistCpl.intAt_inv_pow_mul hq0 (by rw [LinearMap.sub_apply, Pi.sub_apply]; exact this)
    rw [add_sub_cancel] at s1
    rw [← s1]
    have h1 : y₁ ∈ cosetIn p' P := ⟨_, p'.repY_mem hm', by simp [hy₁]⟩
    rw [← hc] at h1
    obtain ⟨z, hz, h2⟩ := h1
    rw [if_neg hP] at h2
    have h3 := add_mem h2 ((GlobalTheory.TopLaw.coset_sub q'.1.1 (q'.mem_ybSet hm') hz (q'.repY_mem hm') P).2 hP)
    rw [← smul_add, sub_add_sub_cancel] at h3
    have h4 := hL.psiInv al P x₂ y₂ (y₁ - y₂) fun j => by
      rw [if_neg hP]
      open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.TopStep in exact mem_stdAt.1 h3 j
    rwa [add_sub_cancel] at h4
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LineAct.ColTrans

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem adelicConj_adelicConj_eq_self (x : AE D) : cA D (cA D x) = x := by
  have := congrFun (congrFun (adj_adj (D := D) (m := 1) (n := 1) (Matrix.of fun _ _ => x)) 0) 0
  simpa [adj] using this

theorem e_mul_sec (p : SplitPt D k) (x : k) : p.e * p.sec x = p.sec x := by
  rw [← p.sec_pr, p.pr_sec]

theorem map_pr_rat (p : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    (rat M : Mx D m n).map p.pr = M.map (iota p) := by
  ext i j; rfl

theorem matrix_mul_replicateCol_eq_replicateCol_mulVec {R : Type} [CommRing R] {m l : Type} [Fintype l] (A : Matrix m l R) (x : l → R) :
    A * replicateCol (Fin 1) x = replicateCol (Fin 1) (A *ᵥ x) := by
  ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

variable {n : Type} [Fintype n] [DecidableEq n]

theorem adj_wCol (p : SplitPt D k) {W₀ L' : HSp D} (ζ' : Fin L'.rank → D.host.E) (β : Frame p W₀ n) (t : n → k) :
    adj (wCol p ζ' β t) = Matrix.of fun i j => p.sec (dualPick ((L'.gram.map (iota p)) *ᵥ fun i => iota p (ζ' i)) j *
      ((iota p D.host.xi0)⁻¹ * ((W₀.gram.map (iota p)) *ᵥ (β.b *ᵥ t)) i)) := by
  ext i j
  simp only [adj, wCol, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, adelicConj_adelicConj_eq_self]

end GlobalTheory.FinPl.LineAct.ColTrans

namespace GlobalTheory.FinPl.LineAct
open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)
open GlobalTheory.FinPl.LineAct.ColTrans



theorem kappa_wCol_translate : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (L' W₀ : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ'), IsLineVec L' ζ' → ∀ (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p W₀ n), IsSumFrame B.o B.ζ α α₀ → ∀ t : n → k, IsHalf p.e ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wCol p ζ' β t))) ∧ ∀ i j, rd α₀ β ((B.o.resS W₀).symm (0, l.κ W₀ (GlobalTheory.FinPl.LineAct.wCol p ζ' β t))) i j = Sum.elim (fun _ => 0) (fun _ => -t i) j := by
  intro D k _ _ _ _ p n n' _ _ _ _ ρ B L' W₀ ζ' l hL α α₀ β hsum t
  set ι := iota p with hι
  set g' : Fin L'.rank → k := (L'.gram.map ι) *ᵥ fun i => ι (ζ' i) with hg'
  set v : Fin W₀.rank → k := fun j => (ι D.host.xi0)⁻¹ * ((W₀.gram.map ι) *ᵥ (β.b *ᵥ t)) j with hv
  have hadj : adj (wCol p ζ' β t) = Matrix.of fun i j => p.sec (dualPick g' j * v i) := adj_wCol p ζ' β t
  have hu : (B.o.resS W₀).symm (0, l.κ W₀ (wCol p ζ' β t)) =
      (incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝ (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB) := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, Link.κ, ofAdj, adj_mul]
    simp only [Matrix.smul_mul, Matrix.mul_assoc]
  rw [hu]
  constructor
  · have hA : p.e • adj (wCol p ζ' β t) = adj (wCol p ζ' β t) := by
      rw [hadj]; ext i j; simp [e_mul_sec]
    intro i j
    have : p.e • ((incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝ (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB)) =
        (incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝ (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB) := by
      conv_rhs => rw [← hA]
      rw [Matrix.mul_smul (incA D (-D.host.xi0⁻¹) • giA W₀) p.e (adj (wCol p ζ' β t)),
        Matrix.smul_mul p.e ((incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t))]
    exact congrFun (congrFun this i) j
  · generalize hUdef : (incA D (-D.host.xi0⁻¹) • giA W₀) ⬝ adj (wCol p ζ' β t) ⬝
        (adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB) = U
    replace hUdef := hUdef.symm
    have hR : adj (rat l.τ) ⬝ gA B.L ⬝ B.o.pB = rat (l.τᴴ * B.L.gram * B.o.qB) := by
      rw [← rat_conjTranspose, gA, OrthDec.pB, ← rat_mul, ← rat_mul]
    have hX : (incA D (-D.host.xi0⁻¹) • giA W₀ : Mx D W₀.rank W₀.rank).map p.pr =
        ι (-D.host.xi0⁻¹) • (W₀.gram⁻¹).map ι := by
      ext i j; simp [giA, rat, hι, iota]
    have hW : (adj (wCol p ζ' β t)).map p.pr = vecMulVec v (dualPick g') := by
      rw [hadj]; ext i j; simp [vecMulVec, p.pr_sec, mul_comm]
    have hUm : U.map p.pr = (ι (-D.host.xi0⁻¹) • (W₀.gram⁻¹).map ι) * vecMulVec v (dualPick g') *
        (l.τᴴ * B.L.gram * B.o.qB).map ι := by
      rw [hUdef, hR, Matrix.map_mul, Matrix.map_mul, hX, hW, map_pr_rat]
    have hUA : U ⬝ B.o.jA = 0 := by
      simp only [hUdef, Matrix.mul_assoc, OrthDec.pB_jA, Matrix.mul_zero]

    have hrat : (l.τᴴ * B.L.gram * B.o.qB) *ᵥ vecB B.o B.ζ =
        -((D.host.xi0 * star D.host.xi0) • (L'.gram *ᵥ ζ')) := by
      have hz : B.ζ = -(l.τ *ᵥ ζ') := by rw [l.map, neg_neg]
      rw [vecB, Matrix.mulVec_mulVec, Matrix.mul_assoc, B.o.qB_iB, Matrix.mul_one, hz, Matrix.mulVec_neg,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, GlobalTheory.Unf.Model.tau_gram l hL, Matrix.smul_mulVec]
    have hgi : ∀ i, g' i = ι ((L'.gram *ᵥ ζ') i) := fun i => (RingHom.map_mulVec ι _ _ i).symm
    have hg0 : g' ≠ 0 := by
      intro h0
      apply hL.2
      have h1 : L'.gram *ᵥ ζ' = 0 := by
        funext i
        apply ι.injective
        rw [← hgi, h0, Pi.zero_apply, Pi.zero_apply, map_zero]
      rw [h1, dotProduct_zero]
    have hxi : ι D.host.xi0 ≠ 0 := fun h => GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D ((iota p).injective (h.trans (map_zero _).symm))
    have hGG : (W₀.gram⁻¹).map ι * W₀.gram.map ι = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (gram_isUnit_det W₀), Matrix.map_one _ (map_zero _) (map_one _)]
    have hcol : U.map p.pr *ᵥ (fun i => p.pr (ratV (vecB B.o B.ζ) i)) = -(β.b *ᵥ t) := by
      have h1 : (fun i => p.pr (ratV (vecB B.o B.ζ) i)) = ι ∘ vecB B.o B.ζ := rfl
      have h2 : (l.τᴴ * B.L.gram * B.o.qB).map ι *ᵥ (ι ∘ vecB B.o B.ζ) =
          (-(ι (D.host.xi0 * star D.host.xi0))) • g' := by
        funext i
        rw [← RingHom.map_mulVec, hrat, Pi.smul_apply, hgi]
        simp [map_neg, map_mul]
      have h3 : vecMulVec v (dualPick g') *ᵥ g' = v := by
        rw [Matrix.vecMulVec_mulVec, dualPick_dot g' hg0, MulOpposite.op_one, one_smul]
      have h4 : v = (ι D.host.xi0)⁻¹ • ((W₀.gram.map ι) *ᵥ (β.b *ᵥ t)) := rfl
      rw [h1, hUm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h3, h4,
        Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_mulVec, hGG, Matrix.one_mulVec,
        smul_smul, smul_smul, ← neg_one_smul k (β.b *ᵥ t)]
      congr 1
      have hs : ι (star D.host.xi0) = -ι D.host.xi0 := by rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, map_neg]
      rw [map_mul, hs, map_neg, map_inv₀]
      field_simp
    have hrd : rd α₀ β U = fromCols 0 (replicateCol (Fin 1) (-t)) := by
      have hb : α₀.b = _ := hsum
      rw [rd, hb, Matrix.mul_assoc, Matrix.mul_fromCols, Matrix.mul_fromCols, ← Matrix.mul_assoc (U.map p.pr),
        ← Matrix.map_mul, hUA, Matrix.map_zero _ (map_zero _), Matrix.zero_mul, Matrix.mul_zero, matrix_mul_replicateCol_eq_replicateCol_mulVec,
        matrix_mul_replicateCol_eq_replicateCol_mulVec, hcol, Matrix.mulVec_neg, Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec]
    intro i j
    rw [hrd]
    cases j with
    | inl j => simp
    | inr j => simp

end GlobalTheory.FinPl.LineAct

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfSep

theorem map_infPart_eq_zero {D : D7} {S T : HSp D} {b : AE D} (hb : infPart D b = 0) {y : WO S T}
    (hy : IsHalf b y) : y.map (infPart D) = 0 := by
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rw [← hy i j, map_mul, hb, zero_mul]

theorem sep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ f₀ Φ f : WO S T → ℂ, IsSBHalf e (latO S T ΛS ΛT fun _ => True) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Φ f → ∀ g : GA D S, (∀ x, Φ x ≠ 0 → Φ (actO S T g 1 x) = 0) → ∃ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), (∀ i, (y i).map (infPart D) = 0 ∧ (actO S T g⁻¹ 1 (-(y i))).map (infPart D) = 0) ∧ ∑ i, a i • heisO ψ S T (y i) f = f ∧ ∑ i, conj (a i) • heisO ψ S T (actO S T g⁻¹ 1 (-(y i))) f = 0 := by
  classical
  intro D ψ S T hψ ΛS ΛT hS hT Z e he f₀ Φ f hΦ hth g hsupp
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  have hfT : f = Tm Φ := hall Tm hTm
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hinfc : infPart D (cA D e) = 0 := ho.conj.infPart_eq
  obtain ⟨k, hk, hinv, hsup⟩ := hΦ.2
  obtain ⟨M, hM, hMact⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).2 g 1
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛ
  set N : ℕ := M * k with hN
  have hNpos : 0 < N := Nat.mul_pos hM hk
  let Ψ : WO S T → ℂ := fun u => if ∃ t, Φ t ≠ 0 ∧ N • t = u then 1 else 0
  have hNt : ∀ t, Φ t ≠ 0 → N • t ∈ Λ := fun t ht => by
    rw [hN, mul_smul]; exact Λ.nsmul_mem (hsup t ht) M
  have hΨ : IsSBHalf e Λ Ψ := by
    refine ⟨fun u hu => ?_, N * k, Nat.mul_pos hNpos hk, fun v hv hvh u => ?_, fun u hu => ?_⟩
    · have : ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        by_contra h; exact hu (if_neg h)
      obtain ⟨t, ht, rfl⟩ := this
      exact GlobalTheory.ThetaOrth.isHalf_nsmul (hΦ.1 t ht) N
    · have key : (∃ t, Φ t ≠ 0 ∧ N • t = u + (N * k) • v) ↔ ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        constructor
        · rintro ⟨t, ht, h⟩
          refine ⟨t + k • (-v), by rwa [hinv (-v) (Λ.neg_mem hv) (GlobalTheory.ThetaOrth.isHalf_neg hvh) t], ?_⟩
          exact GlobalTheory.ThetaOrth.nsmul_add_neg N k t u v h
        · rintro ⟨t, ht, rfl⟩
          refine ⟨t + k • v, by rwa [hinv v hv hvh t], ?_⟩
          exact GlobalTheory.ThetaOrth.nsmul_add_mul N k t v
      show (if _ then _ else _) = (if _ then _ else _)
      simp only [key]
    · have : ∃ t, Φ t ≠ 0 ∧ N • t = u := by
        by_contra h; exact hu (if_neg h)
      obtain ⟨t, ht, rfl⟩ := this
      exact Λ.nsmul_mem (hNt t ht) _
  have hspan := (GlobalTheory.PlaceTensor.halfWaves_span D ψ S T ΛS ΛT hψ hS hT e ho.idem he.2 ho.infPart_eq).2 Ψ hΨ
  obtain ⟨q, hq, hqΨ⟩ := GlobalTheory.ThetaOrth.exists_char_of_wave N hspan
  have hq1 : ∀ t, Φ t ≠ 0 → q t = 1 := fun t ht => by
    rw [← hqΨ t (hΦ.1 t ht) (hNt t ht)]
    exact if_pos ⟨t, ht, rfl⟩
  have hq0 : ∀ t, Φ t ≠ 0 → q (actO S T g 1 t) = 0 := fun t ht => by
    have h1 : N • actO S T g 1 t ∈ Λ := by
      have := hMact (k • t) (hsup t ht)
      have e : actO S T g 1 (k • t) = k • actO S T g 1 t := map_nsmul (GlobalTheory.LatLevel.actHom S T g 1) k t
      rwa [e, ← mul_smul] at this
    rw [← hqΨ _ (GlobalTheory.SplitHecke.isHalf_actO _ _ (hΦ.1 t ht)) h1]
    refine if_neg ?_
    rintro ⟨t', ht', h⟩
    have : t' = actO S T g 1 t := GlobalTheory.ThetaOrth.nsmul_inj hNpos h
    exact ht' (this ▸ hsupp t ht)

  obtain ⟨n, a, yy, hqs⟩ := (Submodule.mem_span_set' (R := ℂ)).1 hq
  choose y hy hyq using fun i => (yy i).2
  have hqt : ∀ t, q t = ∑ i, a i * ψ (symplO S T t (y i)) := fun t => by
    rw [← hqs, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, hyq i, smul_eq_mul]
  set w : Fin n → WO S T := fun i => actO S T g⁻¹ 1 (-(y i)) with hw
  have hwh : ∀ i, IsHalf (cA D e) (w i) := fun i =>
    GlobalTheory.SplitHecke.isHalf_actO _ _ (GlobalTheory.ThetaOrth.isHalf_neg (hy i))
  have hact : ∀ i, actO S T g 1 (w i) = -(y i) := fun i => by
    have := GlobalTheory.AdelicLatMove.actO_actO_inv S T g 1 (-(y i))
    rwa [inv_one] at this
  refine ⟨n, a, y, fun i => ⟨map_infPart_eq_zero hinfc (hy i), map_infPart_eq_zero hinfc (hwh i)⟩, ?_, ?_⟩
  · have e1 : (fun t => q t * Φ t) = Φ := by
      funext t
      by_cases h : Φ t = 0
      · rw [h, mul_zero]
      · rw [hq1 t h, one_mul]
    have e2 : (fun t => q t * Φ t) = ∑ i, a i • fun t => ψ (symplO S T t (y i)) * Φ t := by
      funext t
      rw [hqt, Finset.sum_mul, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    have e3 := congrArg Tm e2

    rw [e1, map_sum, ← hfT] at e3
    refine (Finset.sum_congr rfl fun i _ => ?_).trans e3.symm
    rw [map_smul, hTm.modul Φ hΦ (y i) (hy i), ← hfT]
  · have e1 : (fun t => conj (q (actO S T g 1 t)) * Φ t) = 0 := by
      funext t
      by_cases h : Φ t = 0
      · simp [h]
      · simp [hq0 t h]
    have e2 : (fun t => conj (q (actO S T g 1 t)) * Φ t) =
        ∑ i, conj (a i) • fun t => ψ (symplO S T t (w i)) * Φ t := by
      funext t

      rw [hqt, map_sum, Finset.sum_mul, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.ThetaOrth.conj_psi hψ,
        ← GlobalTheory.ThetaOrth.symplO_neg_right, ← hact i, GlobalTheory.SymplOInv.symplO_actO D S T g 1 t (w i), mul_assoc]
    have e3 := congrArg Tm e2

    rw [e1, map_zero, map_sum] at e3
    rw [e3]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hfT, hTm.modul Φ hΦ (w i) (hwh i)]

end GlobalTheory.HalfSep

end
end
