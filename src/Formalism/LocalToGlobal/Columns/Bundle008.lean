module

public import Formalism.HarderNarasimhan.Bundle001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle004
public import Formalism.MeanHeightDescent.AverageDegreeBounds.Bundle002
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.ExistsNsmulMem
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds
public import Formalism.LocalToGlobal.Columns.Bundle007
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Columns.StandardDeltaIntegralCoeffs
public import Formalism.HermitianLattices.Bundle001
public import Formalism.LocalToGlobal.Columns.PolyFn
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.GlobalTheory.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Module
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN

section F3

variable {K : Type} [Field K] [NumberField K] [StarRing K]

variable [_root_.NumberField.IsTotallyComplex K] {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem slope_line_le_neg_log (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0)
    (c : ℝ) (hc : 0 < c) (hn : ∀ v, c ≤ normAt b X v x ^ 2) :
    muDef b X (Submodule.span (𝓞 K) ({x} : Set V)) ≤ -Real.log c := by
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_singleton x)
  have hL0 : L ≠ ⊥ := fun h => hx ((Submodule.span_singleton_eq_bot).1 h)
  have hrk : rkK (K := K) L = 1 := Formalism.ExtensionFiltration.rkK_span_singleton x hx
  have hf : 0 < nPl K := Fintype.card_pos
  have hfR : (0 : ℝ) < (nPl K : ℝ) := by exact_mod_cast hf
  obtain ⟨-, hmu, -⟩ := size_maximal_slope K V ι b X hX L hLfg hL0
  have hpos : 0 < ht b X L := (place_lattice_structure K V ι b X hX L hLfg).2.2
  have hli : LinearIndependent K (fun _ : Fin 1 => x) := LinearIndependent.of_subsingleton (0 : Fin 1) hx
  have hrange : Set.range (fun _ : Fin 1 => x) = {x} := Set.range_const
  have hg := (height_gram_determinant K V ι b X hX 1 (fun _ : Fin 1 => x) hli).1
  rw [hrange] at hg
  have hht : c ^ (nPl K) ≤ ht b X L := by
    rw [hL, hg]
    have h1 : ∀ v : InfinitePlace K, c ≤ (gramPl b X v (fun _ : Fin 1 => x)).det.re := by
      intro v
      rw [Matrix.det_fin_one]
      simp only [gramPl, Matrix.of_apply]
      rw [Formalism.ExtensionFiltration.majAt_self_re]
      exact hn v
    calc c ^ (nPl K) = ∏ _v : InfinitePlace K, c := by rw [Finset.prod_const, Finset.card_univ]; rfl
      _ ≤ ∏ v, (gramPl b X v (fun _ : Fin 1 => x)).det.re := Finset.prod_le_prod₀ (fun v _ => hc.le) (fun v _ => h1 v)
  have hlog : (nPl K : ℝ) * Real.log c ≤ Real.log (ht b X L) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hht
  rw [hmu]
  unfold size
  rw [Real.log_rpow hpos, hrk]
  have : Real.log c / 2 ≤ (1 : ℝ) / (2 * (nPl K : ℝ) * ((1 : ℕ) : ℝ)) * Real.log (ht b X L) := by
    rw [Nat.cast_one, mul_one, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  linarith

theorem max_slope_line_neg_log (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0)
    (c : ℝ) (hc : 0 < c) (hn : ∀ v, c ≤ normAt b X v x ^ 2) :
    muMaxDef b X (Submodule.span (𝓞 K) ({x} : Set V)) ≤ -Real.log c := by
  have : Module.Finite K V := Module.Finite.of_basis b
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) ({x} : Set V) with hL
  have hLfg : L.FG := Submodule.fg_span (Set.finite_singleton x)
  have hL0 : L ≠ ⊥ := fun h => hx ((Submodule.span_singleton_eq_bot).1 h)
  have hrk : rkK (K := K) L = 1 := Formalism.ExtensionFiltration.rkK_span_singleton x hx
  refine Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_le b X hL0 fun Q hQ hQ0 => ?_
  have h1 : rkK (K := K) Q ≤ 1 := by
    rw [← hrk]
    exact Submodule.finrank_mono (Submodule.span_mono hQ)
  have h2 : 0 < rkK (K := K) Q := Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hQ0
  have hrkQ : rkK (K := K) Q = rkK (K := K) L := by omega
  have hi := (Formalism.LFunctionChainParameters.LLcv.index_slope_formula K V ι b X hX L Q hLfg hQ hQ0 hrkQ).1
  have hl : 0 ≤ Real.log (Q.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := Real.log_natCast_nonneg _
  have hn' : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd : 0 ≤ 2 * Real.log (Q.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) / ((Module.finrank ℚ K : ℝ) * (rkK L : ℝ)) := by
    rw [hrk]
    positivity
  have := slope_line_le_neg_log b X hX x hx c hc hn
  rw [hi]
  linarith

end F3

section F3b

variable {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]

end F3b

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Roots

variable {K : Type} [Field K] [NumberField K]

theorem map_root_smul {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (N : Submodule (𝓞 K) V) (f : Module.End K V) {c : K} {m : ℕ} (hm : 0 < m) (hc : c ^ m = 1) :
    N.map ((c • f).restrictScalars (𝓞 K)) = N.map (f.restrictScalars (𝓞 K)) := by
  have hint : IsIntegral ℤ c := ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [hc]⟩
  let c' : 𝓞 K := ⟨c, hint⟩
  have hc' : ∀ x : V, c' • x = c • x := fun x => by
    rw [← algebraMap_smul K c' x]; rfl
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c' • x, N.smul_mem _ hx, ?_⟩
    show f (c' • x) = c • f x
    rw [hc', map_smul]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c' ^ (m - 1) • x, N.smul_mem _ hx, ?_⟩
    show c • f (c' ^ (m - 1) • x) = f x
    have h2 : ∀ (k : ℕ) (x : V), c' ^ k • x = c ^ k • x := by
      intro k
      induction k with
      | zero => intro x; simp
      | succ k ih => intro x; rw [pow_succ, mul_smul, ih, hc', pow_succ, mul_smul]
    rw [h2, map_smul, smul_smul, ← pow_succ', Nat.sub_add_cancel hm, hc, one_smul]

theorem star_mul_root [StarRing K] (h : ∃ σ₀ : K →+* ℂ, ∀ x : K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    {c : K} {m : ℕ} (hm : 0 < m) (hc : c ^ m = 1) : star c * c = 1 := by
  obtain ⟨σ₀, hσ⟩ := h
  apply σ₀.injective
  rw [map_mul, hσ, map_one, mul_comm, Complex.mul_conj]
  have h1 : ‖σ₀ c‖ = 1 := by
    have : σ₀ c ^ m = 1 := by rw [← map_pow, hc, map_one]
    exact Complex.norm_eq_one_of_pow_eq_one this hm.ne'
  rw [Complex.normSq_eq_norm_sq, h1]
  simp

end Roots

section Form

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

theorem FormG.incl_injective : Function.Injective (FormG.incl Λ) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Prod.ext h1 (Subtype.ext h2)

theorem formGSD_rho (a : (formGSD C Λ).G) (x : C.V) :
    (formGSD C Λ).ρ a x = ((Λ.chr a.2 : X.Kˣ) : X.K) • C.rho a.1 x := rfl

theorem mem_formGSD_EqFun (φ : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) → C.V) :
    φ ∈ (formGSD C Λ).EqFun ↔ ∀ (γ : UF X.E n) (h : ↥Λ.grp) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)),
      φ ((γ, (h : GLG (E := X.E) (n := n) (SG := SG))) • d) = ((Λ.chr h : X.Kˣ) : X.K) • C.rho γ (φ d) :=
  ⟨fun H γ h d => H (γ, h) d, fun H a d => H a.1 a.2 d⟩

theorem LevFam.chr_root (h : ↥Λ.grp) : ∃ m : ℕ, 0 < m ∧ ((Λ.chr h : X.Kˣ) : X.K) ^ m = 1 := by
  have hf : IsOfFinOrder h := isOfFinOrder_of_finite h
  refine ⟨orderOf h, hf.orderOf_pos, ?_⟩
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]

theorem formGSD_ok (hX : X.Ok) (hC : C.Eqv) : (formGSD C Λ).Ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s, hs, hrep⟩ := DecoSet.finite_reps (ST := ST) (SG := SG) (n := n) (posStar_of_conj hX.conjE)
    have : Finite s := hs
    refine Finite.of_surjective (fun d : s => (formGSD C Λ).cls d.1) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h d =>
      obtain ⟨d0, hd0, g, hg⟩ := hrep d
      refine ⟨⟨d0, hd0⟩, ?_⟩
      refine ((formGSD C Λ).cls_eq_iff d0 d).mpr ⟨((g, 1) : FormG Λ)⁻¹, ?_⟩
      have h1 : d = (((g, 1) : FormG Λ) : (formGSD C Λ).G) • (d0 : (formGSD C Λ).D) := hg
      rw [h1, inv_smul_smul]
  · intro d
    have := DecoSet.finite_stabilizer (posStar_of_conj hX.conjE) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))
    refine Finite.of_injective
      (fun a : MulAction.stabilizer (formGSD C Λ).G d =>
        (⟨FormG.incl Λ a.1, a.2⟩ : MulAction.stabilizer (UF X.E n × GLG (E := X.E) (n := n) (SG := SG)) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)))) ?_
    intro a b hab
    exact Subtype.ext (FormG.incl_injective Λ (congrArg Subtype.val hab))
  · intro g d
    obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2
    exact (hC.nab_smul (FormG.incl Λ g) d).trans (map_root_smul _ _ hm hc).symm
  · intro g d
    obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2
    exact (hC.del_smul (FormG.incl Λ g) d).trans (map_root_smul _ _ hm hc).symm
  · intro g x y
    obtain ⟨m, hm, hc⟩ := Λ.chr_root g.2
    show C.pair (((Λ.chr g.2 : X.Kˣ) : X.K) • C.rho g.1 x) (((Λ.chr g.2 : X.Kˣ) : X.K) • C.rho g.1 y) = C.pair x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hC.inv, smul_smul]
    show (star ((Λ.chr g.2 : X.Kˣ) : X.K) * _) • _ = _
    rw [star_mul_root hX.conjK hm hc, one_smul]

theorem formGSD_stab_inj (d : (formGSD C Λ).D) {a b : (formGSD C Λ).G} (ha : a • d = d) (hb : b • d = d)
    (hab : a.1 = b.1) : a = b :=
  FormG.incl_injective Λ (DecoSet.stab_fst_injective (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) ha hb hab)

end Form

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem colVal_eqv (hX : X.Ok) (u : Pr.Word) (j : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 X.E))) :
    (colVal W u j ST SG).Eqv :=
  ⟨colVal_nab_smul W u j, colVal_del_smul W u j, roundPk_inv X _ _ hX.emb_star⟩

theorem colOk (hX : X.Ok) (u : Pr.Word) (j : ℕ) : (colGSD W Ch u j).Ok :=
  formGSD_ok _ _ hX (colVal_eqv W hX u j _ _)

theorem colLev_of_lt {j : ℕ} (hj : j < R.m) (w : Pr.vGs) :
    colLev Ch j w = ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j,
      lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j⟩ := if_pos hj

end Cols

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms

section FockN

def fockN {σ : Type} (f : MvPolynomial σ ℂ) : ℝ := ∑ m ∈ f.support, ‖AddMonoidAlgebra.coeff f m‖ ^ 2 * (mfact m : ℝ)

theorem fockF_self {σ : Type} (f : MvPolynomial σ ℂ) : Formalism.REAL.fockF f f = (fockN f : ℂ) := by
  unfold Formalism.REAL.fockF fockN
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.star_def, RCLike.mul_conj]
  simp [Formalism.L2.DIV.mfact]

theorem fockN_nonneg {σ : Type} (f : MvPolynomial σ ℂ) : 0 ≤ fockN f :=
  Finset.sum_nonneg fun _ _ => by positivity

theorem fockN_pos {σ : Type} (f : MvPolynomial σ ℂ) (hf : f ≠ 0) : 0 < fockN f := by
  have hne : f.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr fun h0 => hf (MvPolynomial.support_eq_empty.mp h0)
  obtain ⟨m, hm⟩ := hne
  unfold fockN
  refine Finset.sum_pos' (fun i _ => by positivity) ⟨m, hm, ?_⟩
  have h1 : AddMonoidAlgebra.coeff f m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have h2 : (0 : ℝ) < (mfact m : ℝ) := by
    have : 0 < mfact m := Finset.prod_pos fun k _ => Nat.factorial_pos _
    exact_mod_cast this
  exact mul_pos (pow_pos (norm_pos_iff.mpr h1) 2) h2

theorem fockN_sum_le {σ : Type} (f : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ)) :
    ∑ m ∈ S, ‖AddMonoidAlgebra.coeff f m‖ ^ 2 * (mfact m : ℝ) ≤ fockN f := by
  classical
  unfold fockN
  rw [← Finset.sum_filter_of_ne (p := fun m => m ∈ f.support)]
  · exact Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => (Finset.mem_filter.mp hm).2)
      (fun _ _ _ => by positivity)
  · intro m _ hne
    rw [MvPolynomial.mem_support_iff]
    intro h0
    apply hne
    simp [h0]

variable {ι : Type} [Fintype ι] {n : ℕ}

def extremalFockNormProduct (lam : ι → DomWeight n) : ℝ := ∏ τ, fockN (extremal ℂ n (lam τ))

theorem extR_pos (lam : ι → DomWeight n) : 0 < extremalFockNormProduct lam :=
  Finset.prod_pos fun _ _ => fockN_pos _ (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _)

theorem nfL_self (lam : ι → DomWeight n) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfL lam P P = ((fockN P / extremalFockNormProduct lam : ℝ) : ℂ) := by
  rw [nfL_apply, nfAll, fockF_self]
  simp only [fockF_self, extremalFockNormProduct]
  push_cast
  rfl

end FockN

section FinalTheorems

variable (K : Type) [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

end FinalTheorems

section Tgt

variable (K : Type) [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

def monW (m : MonI lam) : ℝ := (mfact m.1 : ℝ) / extremalFockNormProduct lam

theorem mfact_pos {σ : Type} (m : σ →₀ ℕ) : 0 < mfact m := Finset.prod_pos fun _ _ => Nat.factorial_pos _

theorem monW_pos (m : MonI lam) : 0 < monW lam m := by
  unfold monW
  exact div_pos (Nat.cast_pos.mpr (mfact_pos _)) (extR_pos lam)

def monD : Matrix (MonI lam) (MonI lam) ℂ := Matrix.diagonal fun m => ((Real.sqrt (monW lam m) : ℝ) : ℂ)

theorem monD_det : IsUnit (monD lam).det := by
  rw [monD, Matrix.det_diagonal, isUnit_iff_ne_zero]
  refine Finset.prod_ne_zero_iff.2 fun m _ => ?_
  exact_mod_cast (Real.sqrt_pos.2 (monW_pos lam m)).ne'

theorem monH_fcoord (v : InfinitePlace K) (x : MonI lam → K) (m : MonI lam) :
    fcoord (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v x m = ((Real.sqrt (monW lam m) : ℝ) : ℂ) * v.embedding (x m) := by
  rw [fcoord, Matrix.nonsing_inv_nonsing_inv _ (monD_det lam)]
  simp [monD, Matrix.mulVec_diagonal, vecAt]

theorem monH_norm (v : InfinitePlace K) (x : MonI lam → K) :
    normAt (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v x ^ 2 = ∑ m, monW lam m * ‖v.embedding (x m)‖ ^ 2 := by
  unfold normAt cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [monH_fcoord, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (monW_pos lam m).le]

end Tgt

section Norm

def hsN {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ a, ∑ b, ‖U a b‖ ^ 2

theorem hsN_nonneg {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN U :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

def FockSubNorm : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (U : ι → Matrix (Fin n) (Fin n) ℂ) (d : ι → ℕ) (F : MvPolynomial (ι × Fin n × Fin n) ℂ),
    (∀ m, AddMonoidAlgebra.coeff F m ≠ 0 → ∀ τ, ∑ a, ∑ s, m (τ, a, s) = d τ) →
    fockN (Formalism.GradedWeylDivisibility.blockAct ℂ U F) ≤ (∏ τ, hsN (U τ) ^ d τ) * fockN F

variable (K : Type) [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

def dW (lam : DomWeight n) : ℕ := ∑ s, lam.natW s

def gN (g : ι → GL (Fin n) K) (v : InfinitePlace K) (τ : ι) : ℝ :=
  hsN (((g τ : Matrix (Fin n) (Fin n) K)ᵀ).map v.embedding)

variable [_root_.NumberField.IsTotallyComplex K]

end Norm

end Formalism.L2.Col
end
end
