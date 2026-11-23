module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle018
public import Formalism.PieriBlockIdeals.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2369
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle097
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvTrans

theorem epsMul_comp_algebraMap {R : Type} [CommRing R] (c : R) :
    spMap (epsMul c) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) := by
  simp only [spMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X Y : Scheme.{0}} {t : SAB H Y} {p : X ⟶ Y} {G' : Over X} [GrpObj G'] {ψ : G'.left ⟶ t.G.left}

theorem trv_epsMul (hψ : IsPullback ψ G'.hom t.G.hom p) (g : G'.left ⟶ G'.left) {R : Type} [CommRing R]
    (q : Sp R ⟶ X) (c : R) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g q (spMap (epsMul c) ≫ v) = spMap (epsMul c) ≫ trv hψ g q v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ g q w hw hw', trv_eq hψ g q (spMap (epsMul c) ≫ w) (by rw [Category.assoc, hw])
    (by rw [Category.assoc, hw', ← Category.assoc, epsMul_comp_algebraMap])]
  simp only [Category.assoc]

end GlobalTheory.EqvTrans


open MonObj GlobalTheory.EqvTrans in
theorem GlobalTheory.EqvTrans.trv_comb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X Y : Scheme.{0}} (t : SAB H Y) (p : X ⟶ Y) (G' : Over X) [GrpObj G'] (ψ : G'.left ⟶ t.G.left) (b : X ⟶ X) (g : G'.left ⟶ G'.left) (hG : IsGrpPullback G' t.G p ψ), IsGrpPullback G' G' b g → ∀ {R : Type} [CommRing R] (q : Sp R ⟶ X) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) (a : Fin n → R) (w : Sp (DualNumber R) ⟶ t.G.left), (∀ i, IsTanAtG t (q ≫ p) (v i)) → IsTanAtG t (q ≫ p) w → IsCombAtG t (q ≫ p) v a w → IsCombAtG t ((q ≫ b) ≫ p) (fun i => GlobalTheory.EqvTrans.trv hG.1 g q (v i)) a (GlobalTheory.EqvTrans.trv hG.1 g q w) := by
  intro E _ _ _ H X Y t p G' _ ψ b g hG hg R _ q n v a w hv _ hc
  obtain ⟨u, hu, hw⟩ := hc

  let T : Over X := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ q)
  let e1 : Over.mk (T.hom ≫ p) ⟶ tEpsG (q ≫ p) := Over.homMk (𝟙 _) (by simp [T])
  let T' : Over X := Over.mk (T.hom ≫ b)
  let e2 : Over.mk (T'.hom ≫ p) ⟶ tEpsG ((q ≫ b) ≫ p) := Over.homMk (𝟙 _) (by simp [T, T'])
  have hov : ∀ x : tEpsG (q ≫ p) ⟶ t.G,
      x.left ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p := fun x => by
    simpa using Over.w x

  let L : (tEpsG (q ≫ p) ⟶ t.G) → (T ⟶ G') := fun x =>
    Over.homMk (hG.1.lift x.left T.hom (by rw [hov x]; simp [T])) (hG.1.lift_snd _ _ _)
  have hL : ∀ x, (L x).left ≫ ψ = x.left := fun x => hG.1.lift_fst _ _ _
  have hLw : ∀ x, (L x).left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q := fun x => Over.w (L x)
  have hgw : g ≫ G'.hom = G'.hom ≫ b := hg.1.w

  let Φ : (tEpsG (q ≫ p) ⟶ t.G) → (tEpsG ((q ≫ b) ≫ p) ⟶ t.G) := fun x =>
    Over.homMk (trv hG.1 g q x.left) (by
      have := trv_over hG.1 g hgw q (hov x)
      simpa using this)
  have hΦ : ∀ x, (Φ x).left = (L x).left ≫ g ≫ ψ := fun x => trv_eq hG.1 g q (L x).left (hL x) (hLw x)

  let M : (tEpsG (q ≫ p) ⟶ t.G) → (T' ⟶ G') := fun x =>
    Over.homMk ((L x).left ≫ g) (by
      show ((L x).left ≫ g) ≫ G'.hom = T.hom ≫ b
      rw [Category.assoc, hgw, ← Category.assoc, Over.w])
  have hmul : ∀ x y, Φ (x * y) = Φ x * Φ y := fun x y => by
    have h1 : ((e1 ≫ x) * (e1 ≫ y)).left = (L x * L y).left ≫ ψ :=
      hG.2 T (L x) (L y) (e1 ≫ x) (e1 ≫ y) (by simp [e1, hL]) (by simp [e1, hL])
    rw [← MonObj.comp_mul] at h1
    have h1' : (L x * L y).left ≫ ψ = (x * y).left := by rw [← h1]; simp [e1]
    have h2 : (M x * M y).left = (L x * L y).left ≫ g :=
      hg.2 T (L x) (L y) (M x) (M y) rfl rfl
    have h3 : ((e2 ≫ Φ x) * (e2 ≫ Φ y)).left = (M x * M y).left ≫ ψ :=
      hG.2 T' (M x) (M y) (e2 ≫ Φ x) (e2 ≫ Φ y) (by simp [e2, hΦ, M]) (by simp [e2, hΦ, M])
    rw [← MonObj.comp_mul, h2] at h3
    apply Over.OverMorphism.ext
    have h4 : (Φ (x * y)).left = (L x * L y).left ≫ g ≫ ψ :=
      trv_eq hG.1 g q (L x * L y).left h1' (Over.w (L x * L y))
    rw [h4, ← Category.assoc, ← h3]
    simp [e2]
  let Φm : (tEpsG (q ≫ p) ⟶ t.G) →* (tEpsG ((q ≫ b) ≫ p) ⟶ t.G) := MonoidHom.mk' Φ hmul
  refine ⟨fun i => Φ (u i), fun i => ?_, ?_⟩
  · show trv hG.1 g q (u i).left = _
    rw [hu i, trv_epsMul hG.1 g q (a i) (hv i).1]
  · have : (List.ofFn fun i => Φ (u i)) = (List.ofFn u).map Φm := by
      rw [List.map_ofFn]; rfl
    rw [this, ← map_list_prod]
    show trv hG.1 g q _ = _
    rw [hw]
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn
  GlobalTheory.ExpTie

namespace GlobalTheory.ExpTie

theorem rows_big_of_largeParameter {D : D7} (L : SizeData₂ D) (P5 : ParameterChoice' D L) (j : Fin D.R.m) (eps C x : ℝ)
    (hx : L.sc.x = x) (heps : L.sc.eps = eps) (hC : 2 * L.Ct + 1 ≤ C) (hC0 : L.Ct ≤ C) (hx2 : 2 ≤ x)
    (hB : Formalism.CohomologicalDescent.LargeParameterEstimates.Big (x ^ eps) x (Real.exp (x ^ (eps / 3))) (x ^ C)) :
    Formalism.CohomologicalDescent.LargeParameterEstimates.Rows (parOf L j) L.sc.X' (x ^ C) ∧
      Formalism.CohomologicalDescent.LargeParameterEstimates.Big (parOf L j).L (parOf L j).x L.sc.X' (x ^ C) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hX : 0 < L.sc.X' := Real.exp_pos _
  have hk2 : (2 : ℝ) ≤ D.R.k := by
    have h1 := D.R.f_le_k
    have h2 : 0 < D.R.ord := Formalism.HC.Frame.ord_pos _
    exact_mod_cast (show 2 ≤ D.R.k by omega)
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    exact_mod_cast this
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos

  have hw : L.sc.X' * L.sc.w'' D.R.n = L.sc.b / D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a
    rw [hx]
    field_simp
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a Scale.b
    rw [hx]
    positivity
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hbn : L.sc.b / D.R.n ≤ L.sc.b := div_le_self hb0.le hn1
  have hkS := P5.kS_le
  have hmt := P5.mteta
  have hS_le : L.Sc ≤ L.sc.w'' D.R.n / 2 := by
    have : 2 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := mul_le_mul_of_nonneg_right hk2 hSc.le
    linarith
  have heta_le : L.etaSz ≤ L.sc.w'' D.R.n / 2 := by
    have h1 : (2 : ℝ) ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by nlinarith
    have : 2 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := mul_le_mul_of_nonneg_right h1 heta.le
    linarith

  have htw := L.t_win
  rw [hx] at htw
  have hkt : D.R.k + D.R.m + 4 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hkt' : (D.R.k : ℝ) + D.R.m + 4 ≤ D.R.t := by exact_mod_cast hkt
  have hCt : x ^ L.Ct ≤ x ^ C := Real.rpow_le_rpow_of_exponent_le hx1 hC0
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, rfl, D.R.f_le_k, ?_, ?_⟩, ?_⟩
  ·
    show L.sc.a / L.sc.X' = L.sc.x * Real.exp L.sc.L / L.sc.X'
    rfl
  · show L.sc.X' * (L.Sc + L.etaSz) ≤ Real.exp L.sc.L
    have : L.sc.X' * (L.Sc + L.etaSz) ≤ L.sc.X' * L.sc.w'' D.R.n :=
      mul_le_mul_of_nonneg_left (by linarith) hX.le
    have hb : Real.exp L.sc.L = L.sc.b := rfl
    rw [hb]
    linarith
  · exact hkS
  · show 1 ≤ L.Sc
    rw [L.Sc_eq]
    have hD := P5.Del_ge.2.2.2
    have hN : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      have : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
      exact_mod_cast this
    have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by linarith)
    have h1 : (1 : ℝ) ≤ (D.s.Del : ℝ) := by nlinarith
    nlinarith
  · exact D.R.two_le_m
  · exact htw.2.trans hCt
  ·
    show (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ x ^ C * L.sc.x
    rw [hx]
    have hT := htw.2
    have ht1 := htw.1
    have hN3 : (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ 3 * (x ^ L.Ct) ^ 2 := by
      have h3 : (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) ≤ 3 * (D.R.t : ℝ) ^ 2 := by nlinarith
      have h4 : (D.R.t : ℝ) ^ 2 ≤ (x ^ L.Ct) ^ 2 := pow_le_pow_left₀ ht0 hT 2
      linarith
    have hsq : (x ^ L.Ct) ^ 2 * x ≤ x ^ C := by
      rw [sq, ← Real.rpow_add hx0]
      calc x ^ (L.Ct + L.Ct) * x = x ^ (L.Ct + L.Ct + 1) := by rw [Real.rpow_add hx0 (L.Ct + L.Ct) 1, Real.rpow_one]
        _ ≤ x ^ C := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hpos : 0 ≤ (x ^ L.Ct) ^ 2 := sq_nonneg _
    nlinarith
  · show Formalism.CohomologicalDescent.LargeParameterEstimates.Big (L.sc.x ^ L.sc.eps) L.sc.x (Real.exp (L.sc.x ^ (L.sc.eps / 3))) (x ^ C)
    rw [hx, heps]
    exact hB

end GlobalTheory.ExpTie

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogKSDiv.DetChange

open GlobalTheory.LogKSDiv
open Classical

theorem sandwich {ι κ K : Type} [Fintype ι] [DecidableEq ι] [CommRing K] (B : Matrix ι κ K) (a b : ι) (x y : κ) :
    (Matrix.transpose B * Matrix.of (fun u v => (if u = a ∧ v = b then (1 : K) else 0) + (if u = b ∧ v = a then 1 else 0)) * B) x y =
      B a x * B b y + B b x * B a y := by
  simp [Matrix.mul_apply, add_mul, mul_add, Finset.sum_add_distrib, ite_and, Finset.sum_mul, Finset.mul_sum]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem hostRoot_conj_eq_neg_and_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hre0 : H.rt0.re = 0 := by
    by_contra hne
    have : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨Complex.ext (by simp [hre0]) (by simp), ?_⟩
  intro h0
  rw [h0] at hre
  simp at hre
  exact H.d_prime.ne_zero hre

theorem emb_rt_cases (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [H.sqrt_neg_disc_sq, ← map_pow]
  have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  rw [this]; simp

theorem conj_off (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) (h : τ (H.rt : E) = H.rt0) :
    ((starRingEnd ℂ).comp τ) (H.rt : E) ≠ H.rt0 := by
  obtain ⟨h1, h2⟩ := hostRoot_conj_eq_neg_and_ne_zero H
  rw [RingHom.comp_apply, h, h1]
  intro h3
  exact h2 (by linear_combination (-1/2 : ℂ) * h3)

theorem conj_on (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) (h : τ (H.rt : E) ≠ H.rt0) :
    ((starRingEnd ℂ).comp τ) (H.rt : E) = H.rt0 := by
  rcases emb_rt_cases H τ with h' | h'
  · exact absurd h' h
  · rw [RingHom.comp_apply, h', map_neg, (hostRoot_conj_eq_neg_and_ne_zero H).1, neg_neg]

theorem conj_conj_emb (τ : E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp τ) = τ := by
  ext x; simp

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {K : Type} [Field K]

theorem flatFrame_eq (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (a b : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) :
    flatFrame A e e' (e a) (e' b) = Matrix.blockDiagonal' A a b := by
  simp [flatFrame]

def kronBlocks (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    Matrix (PairIx H Dw) (PairIx H Dw) K :=
  Matrix.blockDiagonal' fun τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} =>
    Matrix.kroneckerMap (· * ·) (A τ.1).transpose (A ((starRingEnd ℂ).comp τ.1)).transpose

theorem lhs_entry (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (P Q : PairIx H Dw) :
    (Matrix.transpose (flatFrame A e e') * symPair (R := K) e P * flatFrame A e e')
      (e' ⟨Q.1.1, Q.2.1⟩) (e' ⟨(starRingEnd ℂ).comp Q.1.1, Q.2.2⟩) = kronBlocks A Q P := by
  unfold symPair
  rw [sandwich, flatFrame_eq, flatFrame_eq, flatFrame_eq, flatFrame_eq]
  obtain ⟨⟨τ, hτ⟩, i, k⟩ := P
  obtain ⟨⟨σ, hσ⟩, i', k'⟩ := Q
  have hne : (starRingEnd ℂ).comp τ ≠ σ := fun h => conj_off H τ hτ (h ▸ hσ)
  dsimp only
  rw [Matrix.blockDiagonal'_apply_ne A _ _ hne, zero_mul, add_zero]
  by_cases h : τ = σ
  · subst h
    simp [kronBlocks, Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply]
  · have h' : (⟨σ, hσ⟩ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) ≠ ⟨τ, hτ⟩ := fun h2 => h (congrArg Subtype.val h2).symm
    simp [kronBlocks, Matrix.blockDiagonal'_apply_ne _ _ _ h', Matrix.blockDiagonal'_apply_ne A _ _ h]

theorem sym_entry {n' : ℕ} (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n') (P Q : PairIx H Dw) :
    symPair (R := K) e' P (e' ⟨Q.1.1, Q.2.1⟩) (e' ⟨(starRingEnd ℂ).comp Q.1.1, Q.2.2⟩) = if P = Q then 1 else 0 := by
  obtain ⟨⟨τ, hτ⟩, i, k⟩ := P
  obtain ⟨⟨σ, hσ⟩, i', k'⟩ := Q
  have h2 : ¬ (e' ⟨σ, i'⟩ = e' ⟨(starRingEnd ℂ).comp τ, k⟩ ∧
      e' ⟨(starRingEnd ℂ).comp σ, k'⟩ = e' ⟨τ, i⟩) := by
    rintro ⟨h, -⟩
    have h5 : σ = (starRingEnd ℂ).comp τ := congrArg Sigma.fst (e'.injective h)
    exact conj_off H τ hτ (h5 ▸ hσ)
  simp only [symPair, Matrix.of_apply, if_neg h2, add_zero, e'.apply_eq_iff_eq]
  by_cases h : τ = σ
  · subst h
    simp [Sigma.mk.inj_iff, eq_comm]
    intro h5
    exact (conj_off H τ hτ (by rw [← h5]; exact hτ)).elim
  · have h3 : ¬ (σ = τ) := Ne.symm h
    simp [h, h3]
    intro h5
    exact (conj_off H τ hτ (by rw [← h5]; exact hσ)).elim

theorem L_eq_submatrix (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) {n n' : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K)
    (hL : ∀ j, Matrix.transpose (flatFrame A e e') * symPair (R := K) e (ε j) * flatFrame A e e' =
      ∑ k, L k j • symPair (R := K) e' (ε' k)) :
    L = (kronBlocks A).submatrix ε' ε := by
  ext a j
  have h := congrFun (congrFun (hL j) (e' ⟨(ε' a).1.1, (ε' a).2.1⟩)) (e' ⟨(starRingEnd ℂ).comp (ε' a).1.1, (ε' a).2.2⟩)
  rw [lhs_entry, Matrix.sum_apply] at h
  simp only [Matrix.smul_apply, sym_entry, smul_eq_mul, mul_ite, mul_one, mul_zero, ε'.apply_eq_iff_eq] at h
  rw [Finset.sum_ite_eq' Finset.univ a] at h
  simpa using h.symm

theorem det_kronBlocks (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    (kronBlocks A).det = ∏ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
      ((A τ.1).det ^ Dw.mult ((starRingEnd ℂ).comp τ.1) * (A ((starRingEnd ℂ).comp τ.1)).det ^ Dw.mult τ.1) := by
  rw [kronBlocks, GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod]
  simp [Matrix.det_kronecker, Matrix.det_transpose]

theorem prod_pairs (f : (E →+* ℂ) → K) :
    ∏ τ : E →+* ℂ, f τ ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) =
      ∏ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0},
        (f τ.1 ^ Dw.mult ((starRingEnd ℂ).comp τ.1) * f ((starRingEnd ℂ).comp τ.1) ^ Dw.mult τ.1) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0), Finset.prod_mul_distrib]
  congr 1
  · refine Finset.prod_congr (by convert rfl) fun τ _ => ?_
    rw [if_pos τ.2, Datum.mult, if_neg (conj_off H τ.1 τ.2)]
  · symm
    refine Fintype.prod_equiv
      { toFun := fun τ => ⟨(starRingEnd ℂ).comp τ.1, conj_off H τ.1 τ.2⟩
        invFun := fun σ => ⟨(starRingEnd ℂ).comp σ.1, conj_on H σ.1 σ.2⟩
        left_inv := fun τ => Subtype.ext (conj_conj_emb τ.1)
        right_inv := fun σ => Subtype.ext (conj_conj_emb σ.1) } _ _ (fun τ => ?_)
    simp only [Equiv.coe_fn_mk]
    rw [if_neg (conj_off H τ.1 τ.2), Datum.mult, if_pos τ.2]

end GlobalTheory.LogKSDiv.DetChange

theorem GlobalTheory.LogKSDiv.det_frameChange_balanced :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (K : Type) [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) (n n' : ℕ)
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (e' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n')
    (ε ε' : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (L : Matrix (Fin Dw.dim) (Fin Dw.dim) K),
    (∀ j, _root_.Matrix.transpose (GlobalTheory.LogKSDiv.flatFrame A e e') * GlobalTheory.LogKSDiv.symPair (R := K) e (ε j) * GlobalTheory.LogKSDiv.flatFrame A e e' =
      ∑ k, L k j • GlobalTheory.LogKSDiv.symPair (R := K) e' (ε' k)) →
    ∃ u : K, (u = 1 ∨ u = -1) ∧
      L.det = u * ∏ τ : E →+* ℂ, (A τ).det ^ (if τ (H.rt : E) = H.rt0 then Dw.q else Dw.p) := by
  intro E _ _ _ H Dw K _ A n n' e e' ε ε' L hL
  classical
  rw [GlobalTheory.LogKSDiv.DetChange.L_eq_submatrix A e e' ε ε' L hL]
  have hs : (GlobalTheory.LogKSDiv.DetChange.kronBlocks A).submatrix ε' ε =
      ((GlobalTheory.LogKSDiv.DetChange.kronBlocks A).submatrix ε ε).submatrix (ε'.trans ε.symm) id := by
    ext a b; simp
  refine ⟨((Equiv.Perm.sign (ε'.trans ε.symm) : ℤ) : K), ?_, ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (ε'.trans ε.symm)) with h | h <;> simp [h]
  · rw [hs, Matrix.det_permute, Matrix.det_submatrix_equiv_self, GlobalTheory.LogKSDiv.DetChange.det_kronBlocks,
      GlobalTheory.LogKSDiv.DetChange.prod_pairs]
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.BirModel

theorem exists_smooth_projective_model : GlobalTheory.Published.Principalisation → ∀ (k : Type) [Field k] [CharZero k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (s : Y ⟶ X) (_ : IsDominant s), SmoothOfRelativeDimension n (s ≫ p) ∧
      IsProjOver (s ≫ p) ∧ Function.Bijective (functionFieldMap s) := by
  intro hP k _ _ X _ p n hp hdim
  obtain ⟨Y, s, U, hY, hsm, hpr, hU, hiso⟩ := GlobalTheory.WeakRes.weak_resolution hP k X p n hp hdim
  have hdom : IsDominant s := GlobalTheory.T.isDominant_of_isIso_restrict' X Y s U hU hiso
  exact ⟨Y, hY, s, hdom, hsm, hpr, GlobalTheory.T.functionFieldMap_bijective_of_isIso_restrict' X Y s U hU hiso⟩

end GlobalTheory.BirModel
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

theorem _root_.GlobalTheory.T.exists_stalk_map_identity_mod_maximal_of_fixed_point : ∀ (X : Scheme.{0}) [IsIntegral X] (b : X ≅ X) (x : X), X.fromSpecResidueField x ≫ b.hom = X.fromSpecResidueField x → ∃ st : X.presheaf.stalk x →+* X.presheaf.stalk x, (show Sp (X.presheaf.stalk x) ⟶ X from X.fromSpecStalk x) ≫ b.hom = spMap st ≫ X.fromSpecStalk x ∧ (∀ a, IsLocalRing.residue (X.presheaf.stalk x) (st a) = IsLocalRing.residue (X.presheaf.stalk x) a) ∧ ∀ a, GlobalTheory.functionFieldMap b.hom (algebraMap (X.presheaf.stalk x) X.functionField a) = algebraMap (X.presheaf.stalk x) X.functionField (st a) := by
  first | exact @GlobalTheory.FixStalk.fixes_stalk | exact GlobalTheory.FixStalk.fixes_stalk | (intros; apply GlobalTheory.FixStalk.fixes_stalk <;> assumption)
end
