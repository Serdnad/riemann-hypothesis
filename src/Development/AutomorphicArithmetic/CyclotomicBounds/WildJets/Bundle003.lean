module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle228
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
open GlobalTheory.SignedHC

private theorem parBd_block {c x : ℚ} {len : ℕ} (h : x ∈ TPar.block c len) :
    |(x : ℝ) - (c : ℝ)| ≤ (len : ℝ) / 2 := by
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 h
  have : (a' : ℝ) + 1 ≤ len := by exact_mod_cast (Finset.mem_range.1 ha')
  have h0 : (0 : ℝ) ≤ a' := Nat.cast_nonneg a'
  push_cast
  rw [abs_le]; constructor <;> linarith

private theorem parBd_generic (G : GlobalTheory.SignedHC.GridData) (B : ℝ) (hB : 12 ≤ B) (hN : G.NearMid)
    (hv : ∀ i, 2 ≤ i → i ≤ G.k → (0 : ℝ) ≤ G.v i ∧ (G.v i : ℝ) ≤ B) (ha : ((G.a 0 : ℚ) : ℝ) ≤ B)
    (hb : ∀ l, 1 ≤ l → l ≤ G.m → (0 : ℝ) ≤ G.b l ∧ (G.b l : ℝ) ≤ G.e l ∧ (G.e l : ℝ) ≤ 4 * B)
    (ht : (G.t : ℝ) ≤ B) (hs : (G.s : ℝ) ≤ B) {j : ℕ} (hj : j ≤ G.m) :
    (∀ i, ∀ x ∈ entries (G.parD i j), |(x : ℝ)| ≤ 5 * B) ∧ ∀ x ∈ G.weightX j, |(x : ℝ)| ≤ 5 * B := by
  have hal : ∀ l, l ≤ G.m → (0 : ℝ) ≤ ((G.a l : ℚ) : ℝ) ∧ ((G.a l : ℚ) : ℝ) ≤ B := by
    intro l hl
    have h2 := (hv 2 le_rfl G.two_le_k).1
    have hl' : (l : ℝ) ≤ G.m := by exact_mod_cast hl
    have hl0 : (0 : ℝ) ≤ l := by positivity
    have hg : (0 : ℝ) ≤ G.ga := by positivity
    have h1 : (0 : ℝ) ≤ (l : ℝ) * G.ga := mul_nonneg hl0 hg
    have h3 : (0 : ℝ) ≤ ((G.m : ℝ) + 1 - l) * G.ga := mul_nonneg (by linarith) hg
    unfold GlobalTheory.SignedHC.GridData.a at ha ⊢
    push_cast at ha ⊢
    constructor <;> nlinarith
  have hcen : ∀ l, 1 ≤ l → l ≤ G.m → |(((G.cen l : ℤ) : ℚ) : ℝ)| ≤ B + 1 := by
    intro l h1 h2
    have e := hN l (Finset.mem_Icc.2 ⟨h1, h2⟩)
    have e' : |(((G.cen l : ℤ) : ℚ) : ℝ) - (((G.a (l - 1) : ℚ) : ℝ) + ((G.a l : ℚ) : ℝ)) / 2| ≤ 1 := by
      unfold GlobalTheory.SignedHC.GridData.mid at e
      exact_mod_cast e
    have a1 := hal l h2
    have a2 := hal (l - 1) (by omega)
    rw [abs_le] at e' ⊢
    constructor <;> linarith [e'.1, e'.2, a1.1, a1.2, a2.1, a2.2]
  have hC : ∀ l len, 1 ≤ l → l ≤ G.m → len ≤ G.s → ∀ x ∈ TPar.block (G.cen l : ℚ) len, |(x : ℝ)| ≤ 5 * B := by
    intro l len h1 h2 h3 x hx
    have e := abs_le.1 (parBd_block hx)
    have e' := abs_le.1 (hcen l h1 h2)
    have : (len : ℝ) ≤ G.s := by exact_mod_cast h3
    rw [abs_le]; constructor <;> linarith [e.1, e.2, e'.1, e'.2]
  have hM : ∀ l len, 1 ≤ l → l ≤ G.m → len ≤ G.t + 1 → ∀ x ∈ TPar.block (-(G.e l : ℚ)) len, |(x : ℝ)| ≤ 5 * B := by
    intro l len h1 h2 h3 x hx
    have e := abs_le.1 (parBd_block hx)
    obtain ⟨b1, b2, b3⟩ := hb l h1 h2
    have : (len : ℝ) ≤ G.t + 1 := by exact_mod_cast h3
    push_cast at e
    rw [abs_le]; constructor <;> linarith [e.1, e.2]
  constructor
  · intro i x hx
    obtain ⟨sg, hx⟩ := mem_entries.1 hx
    rcases GlobalTheory.SignedHC.GridData.mem_parD.1 hx with ⟨hc, -⟩ | ⟨l, h1, h2, he⟩ | ⟨l, h1, h2, hc, -⟩ | ⟨l, h1, h2, hc, -⟩
    · obtain ⟨i', h2, hk, e⟩ := GlobalTheory.SignedHC.GridData.mem_cloud.1 hc
      simp only at e
      obtain ⟨v1, v2⟩ := hv i' h2 hk
      rw [e]; push_cast
      rw [abs_le]; constructor <;> linarith
    · have e : x = -(G.b l : ℚ) := congrArg Prod.fst he
      obtain ⟨b1, b2, b3⟩ := hb l h1 h2
      rw [e]; push_cast
      rw [abs_le]; constructor <;> linarith
    · exact hM l G.t h1 (by omega) (by omega) x hc
    · exact hC l G.s (by omega) h2 le_rfl x hc
  · intro x hx
    rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨l, h1, h2, hc⟩ | ⟨l, h1, h2, hc⟩
    · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
      obtain ⟨a1, a2⟩ := hal i hi
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨i, h2, hk, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
      obtain ⟨v1, v2⟩ := hv i h2 hk
      unfold GlobalTheory.SignedHC.GridData.vHalf
      push_cast
      rw [abs_le]; constructor <;> linarith
    · exact hC l (G.s - 1) h1 h2 (by omega) x hc
    · exact hM l (G.t + 1) h1 (by omega) le_rfl x hc

end

theorem UpperTheory.WildA.parBd :
    ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → ∀ X : Node, DefNode D.R.m X → ∀ (τ : D.what₂.Tau),
      ∀ x ∈ GlobalTheory.SignedHC.entries (Node.par D 1 X τ), |(x : ℝ)| ≤ 6 * large₂.sc.b := by
  intro D large₂ hS hH X hX τ
  obtain ⟨hN, -, -, -, hm2, -, -, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSb, hpos, -⟩ := hS
  set G := GlobalTheory.ChiGrid.num D 1 τ with hG
  have hk : G.k = D.R.k := rfl
  have hm : G.m = D.R.m := rfl
  have hga : G.ga = GlobalTheory.ChiGrid.gap D 1 := rfl
  obtain ⟨hv0, hb0, he0⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (GlobalTheory.ChiGrid.sLen D) (GlobalTheory.ChiGrid.gap D 1)
    (GlobalTheory.ChiGrid.cen D 1 τ)
  have hv : ∀ i : Fin (D.R.k - 1), (((D.hc τ).v i : ℚ) : ℝ) = ((G.v (i.1 + 2) : ℤ) : ℝ) := by
    intro i
    have e : (D.hc τ).v i = ((G.v (i.1 + 2) : ℤ) : ℚ) := hv0 i
    rw [e, Rat.cast_intCast]
  have hb : ∀ l : Fin D.R.m, (((D.hc τ).b l : ℚ) : ℝ) = ((G.b (l.1 + 1) : ℤ) : ℝ) := by
    intro l
    have e : (D.hc τ).b l = ((G.b (l.1 + 1) : ℤ) : ℚ) := hb0 l
    rw [e, Rat.cast_intCast]
  have he : ∀ l : Fin D.R.m, (((D.hc τ).e l : ℚ) : ℝ) = ((G.e (l.1 + 1) : ℤ) : ℝ) := by
    intro l
    have e : (D.hc τ).e l = ((G.e (l.1 + 1) : ℤ) : ℚ) := he0 l
    rw [e, Rat.cast_intCast]
  have hprod : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := by positivity
  have hvv : ∀ i, 2 ≤ i → i ≤ G.k → (0 : ℝ) ≤ G.v i ∧ (G.v i : ℝ) ≤ large₂.Sc := by
    intro i h2 hi
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' h2
    have h := large₂.cloud_v τ ⟨a, by omega⟩
    rw [hv] at h
    exact h
  have hts : D.R.t + sLen D + 1 ≤ bigN D := by
    unfold bigN
    have : 1 * (D.R.t + sLen D + 1) ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hgen : ∀ j, j ≤ G.m → (∀ i, ∀ x ∈ GlobalTheory.SignedHC.entries (G.parD i j), |(x : ℝ)| ≤ 5 * large₂.sc.b) ∧
      ∀ x ∈ G.weightX j, |(x : ℝ)| ≤ 5 * large₂.sc.b := by
    intro j hj
    refine parBd_generic G large₂.sc.b h12 (GlobalTheory.ChiGrid.num_nearMid D 1 τ) ?_ ?_ ?_ ?_ ?_ hj
    · intro i h2 hi
      obtain ⟨a, b⟩ := hvv i h2 hi
      exact ⟨a, by linarith⟩
    · have h := (hvv 2 le_rfl G.two_le_k).2
      have e : (((G.a 0 : ℚ)) : ℝ) = ((G.v 2 : ℤ) : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := by
        unfold GlobalTheory.SignedHC.GridData.a; rw [hm, hga]; push_cast; ring
      rw [e]; linarith
    · intro l h1 hl
      obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' h1
      obtain ⟨p1, p2⟩ := hpos τ ⟨a, by omega⟩
      have g := (hH.gap τ ⟨a, by omega⟩).1
      have ht0 : (0 : ℚ) ≤ D.R.t := by positivity
      have g' : (D.hc τ).b ⟨a, by omega⟩ ≤ (D.hc τ).e ⟨a, by omega⟩ := by linarith
      have g'' : (((D.hc τ).b ⟨a, by omega⟩ : ℚ) : ℝ) ≤ (((D.hc τ).e ⟨a, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast g'
      have p1' : (0 : ℝ) ≤ (((D.hc τ).b ⟨a, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast p1.le
      rw [hb] at p1' g''
      rw [he] at p2 g''
      exact ⟨p1', g'', p2⟩
    · have : (D.R.t : ℝ) ≤ bigN D := by exact_mod_cast (by omega : D.R.t ≤ bigN D)
      exact this.trans hN
    · have : (sLen D : ℝ) ≤ bigN D := by exact_mod_cast (by omega : sLen D ≤ bigN D)
      exact this.trans hN
  intro x hx
  cases X with
  | core i => exact hX.elim
  | top j =>
    obtain ⟨sg, hx⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    have h := (hgen j hX).2 x (GlobalTheory.SignedHC.mem_plus.1 hx).1
    linarith
  | grid i j =>
    obtain ⟨sg, hx⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    have hj : j ≤ G.m := le_of_eq hX.2
    have hx' := GlobalTheory.SignedHC.mem_shift.1 hx
    have h := (hgen j hj).1 i _ (GlobalTheory.SignedHC.fst_mem_entries hx')
    simp only at h
    rw [abs_le] at h ⊢
    split_ifs at h <;> push_cast at h <;> constructor <;> linarith [h.1, h.2]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem jetOp_mul_tab' {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a)
    (lam' : ι → DomWeight b) (c : K) (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) :
    Formalism.L2.Ker.jetOp lam lam' (fun k => c * J k) n = c • Formalism.L2.Ker.jetOp lam lam' J n := by
  have e : Formalism.L2.Ker.jetLin (fun k => c * J k) = c • Formalism.L2.Ker.jetLin J := by
    refine (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) K).ext fun m => ?_
    simp only [Formalism.L2.Ker.jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, MvPolynomial.smul_monomial,
      smul_eq_mul]
  ext1 P
  simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, e, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

private theorem prod_pow_fiber {α ι : Type} [Fintype ι] [DecidableEq ι] (f : α → ι) (c : ι → ℂ) (m : α →₀ ℕ) :
    (m.prod fun v e => c (f v) ^ e) = ∏ τ, c τ ^ (m.sum fun v e => if f v = τ then e else 0) := by
  simp only [Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp [pow_ite]

private theorem degree_fiber {α ι : Type} [Fintype ι] [DecidableEq ι] (f : α → ι) (m : α →₀ ℕ) :
    m.degree = ∑ τ, (m.sum fun v e => if f v = τ then e else 0) := by
  simp only [Finsupp.sum]
  rw [Finset.sum_comm, Finsupp.degree_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp

private theorem period_ne {D : D7} {δ : ℂ} (hδ : δ ≠ 0) (τ : D.what₂.Tau) : period δ τ ≠ 0 := by
  refine div_ne_zero hδ (Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 ?_))
  have : 0 < ‖tauE D τ D.host.xi0‖ := norm_pos_iff.2 ((_root_.map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  positivity

private theorem delta_ne {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) : δ ≠ 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.CurveLattice.exists_periodPair_lamOf D cc δ hc
  rintro rfl
  have h1 := (hL L.ω₁).2 L.ω₁_mem_lattice
  have h2 : Formalism.MainNotions.TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
    rw [Formalism.MainNotions.TaylorLogMetric.lamOf, AddSubgroup.closure_le]
    rintro w ⟨c, -, rfl⟩
    simp
  exact L.indep.ne_zero 0 (by simpa using h2 h1)

theorem UpperTheory.WildA.kkTab :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U : Set T} {N : Std G U} (Z : Normal W N) {t : T} {p : GlobalTheory.ChiGrid.Pair T}, DefPair D.R.m p →
      ∀ (d : FinDatum G t p) (x : FinPt G p.small) (y : FinPt G p.big) (Θ : Formalism.MainNotions.TaylorLogMetric.VC D (G.pS p).rank (G.pT p).rank → ℂ),
      (∀ mon, jetTab W N.frC p (Z.vec d) (x * N.u _) (y * N.u _) mon =
        Z.c0 p * opp p (((mon.mapDomain (fvar G p)).prod fun v e => period Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) Θ)) →
      Z.kkMap 1 d x y = Formalism.L2.Ker.jetOp (wt G p.small) (wt G p.big)
        (fun mon => if mon.degree = ∑ τ, fockDeg G p τ then
          opp p (Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) Θ) else 0) (nuEnd G p) := by
  intro D T L sc G W U N Z t p hp d x y Θ h
  classical
  have hδ : Z.δ ≠ 0 := delta_ne Z.crv
  have hf : ∀ k, (fvar G p k).1 = k.1 := fun k => by cases p <;> rfl
  rw [Normal.kkMap, fockComp, ← jetOp_mul_tab']
  refine UpperTheory.WildA.jetDeg _ _ _ (wtOK_of_defPair G p hp).2 _ _ fun m hm => ?_
  have hm' : ∀ τ, (m.sum fun v e => if v.1 = τ then e else 0) = fockDeg G p τ := hm
  have h1 : m.degree = ∑ τ, fockDeg G p τ := by
    rw [degree_fiber Prod.fst m]
    exact Finset.sum_congr rfl fun τ _ => hm' τ
  have h2 : ((m.mapDomain (fvar G p)).prod fun v e => period Z.δ v.1 ^ e) = ∏ τ, period Z.δ τ ^ fockDeg G p τ := by
    rw [Finsupp.prod_mapDomain_index (by simp) (by simp [pow_add])]
    simp only [hf]
    rw [prod_pow_fiber Prod.fst (period Z.δ) m]
    exact Finset.prod_congr rfl fun τ _ => by rw [hm' τ]
  have h3 : (∏ τ, opp p ((1 : D.what₂.Tau → ℂ) τ / period Z.δ τ) ^ fockDeg G p τ) *
      opp p (∏ τ, period Z.δ τ ^ fockDeg G p τ) = 1 := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [map_pow, ← mul_pow, ← map_mul, Pi.one_apply, div_mul_cancel₀ _ (period_ne hδ τ), map_one, one_pow]
  rw [if_pos h1, h, h2, Normal.scal, map_mul, mul_mul_mul_comm, Units.inv_mul, one_mul, ← mul_assoc, h3, one_mul]
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem mx_eq_of_nsmul_eq_of_ne_zero {D : D7} {m n : ℕ} (c : ℕ) (hc : c ≠ 0) {x y : Mx D m n}
    (h : c • x = c • y) : x = y := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply] at h1
  have hF : ((c : ↥D.host.F)) ≠ 0 := Nat.cast_ne_zero.mpr hc
  rw [← Nat.cast_smul_eq_nsmul (↥D.host.F), ← Nat.cast_smul_eq_nsmul (↥D.host.F)] at h1
  calc x i j = ((c : ↥D.host.F))⁻¹ • ((c : ↥D.host.F) • x i j) := (inv_smul_smul₀ hF _).symm
    _ = ((c : ↥D.host.F))⁻¹ • ((c : ↥D.host.F) • y i j) := by rw [h1]
    _ = y i j := inv_smul_smul₀ hF _

theorem UpperTheory.WildA.depthDrop :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {t : T} {p : GlobalTheory.ChiGrid.Pair T} (d : FinDatum G t p) (l : ℕ), l.Prime → (∀ w ∈ d.P, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) →
      ∀ k : ℕ, 0 < k → IsCosetDatum k d → ∃ k' : ℕ, 0 < k' ∧ ¬ l ∣ k' ∧ IsCosetDatum k' d := by
  intro D T L sc G t p d l hl hP k hk hcos
  obtain ⟨x₀, hx₀, hkx, hfn⟩ := hcos
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk.ne' l hl.one_lt.ne'
  have hc : ∀ w ∈ d.P, (((l ^ a : ℕ)) : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro w hw h
    rw [Nat.cast_pow] at h
    exact hP w hw (w.isPrime.mem_of_pow_mem _ h)
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  have hhalf : ∀ (c : ℕ) (u : Mx D (G.pT p).rank (G.pS p).rank), IsHalf d.e u → IsHalf d.e (c • u) := by
    intro c u hu i j
    simp only [Matrix.smul_apply, mul_smul_comm, hu i j]
  obtain ⟨v, hvL, hvH, hv⟩ :=
    UpperTheory.WildA.halfUnit p d.P d.e d.e_is (l ^ a) hc _ hkx (hhalf _ _ hx₀)
  have hmx : m • x₀ = v := by
    apply mx_eq_of_nsmul_eq_of_ne_zero (l ^ a) (pow_ne_zero _ hl.ne_zero)
    rw [hv, smul_smul]
  refine ⟨m, hm0, hm, x₀, hx₀, by rw [hmx]; exact hvL, ?_⟩
  rw [hfn]
  congr 1
  ext x
  simp only [GlobalTheory.RowTest.halfCoset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, hu, huH, rfl⟩
    refine ⟨(l ^ a) • u, AddSubgroup.nsmul_mem _ hu _, hhalf _ _ huH, ?_⟩
    rw [smul_smul, mul_comm m]
  · rintro ⟨u, hu, huH, rfl⟩
    obtain ⟨u', hu', hu'H, rfl⟩ := UpperTheory.WildA.halfUnit p d.P d.e d.e_is (l ^ a) hc u hu huH
    exact ⟨u', hu', hu'H, by rw [smul_smul, mul_comm m]⟩
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.WildA.expLoss :
    ∀ (D : D7) (S : Finset ℕ) (h : ℕ → ℝ) (B : ℝ), GlobalTheory.NormSum.Exponents S h B →
      Loss (fun w : PlL D => (vw w ((GlobalTheory.SumSize.TopInt.primeUnder w : ℕ) : D.what₂.LL) : ℝ) * h (GlobalTheory.SumSize.TopInt.primeUnder w)) B := by
  intro D S h B hE
  have e : (fun w : PlL D => (vw w ((GlobalTheory.SumSize.TopInt.primeUnder w : ℕ) : D.what₂.LL) : ℝ) *
      h (GlobalTheory.SumSize.TopInt.primeUnder w)) = Formalism.PairingDivisionLocalBalance.wt (K := D.what₂.LL) S h := by
    funext w
    rw [hE.wt_eq (TopInt.primeUnder_prime w) w (TopInt.primeUnder_mem w), mul_comm]
  rw [e]
  refine ⟨hE.wt_size.1, ?_, hE.wt_size.2⟩
  have hf : ∀ l : ℕ, {w : PlL D | vw w (l : D.what₂.LL) ≠ 0}.Finite := fun l => by
    have hf := FractionalIdeal.finite_factors (K := D.what₂.LL)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.what₂.LL)) (l : D.what₂.LL))
    rw [Filter.eventually_cofinite] at hf
    exact hf
  refine (S.finite_toSet.biUnion fun l _ => hf l).subset fun w hw => ?_
  obtain ⟨l, hl, h0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  refine Set.mem_biUnion (Finset.mem_coe.2 hl) fun h1 => h0 ?_
  rw [h1]; simp
end
