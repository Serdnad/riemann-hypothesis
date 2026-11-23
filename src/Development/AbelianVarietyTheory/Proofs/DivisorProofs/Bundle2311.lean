module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle077
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.ExtEmbEquivComp
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOMulSource
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointsGenerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
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
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle043
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.AllWt (Psi wtOf)

namespace GlobalTheory.ThetaWtGap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem wtOf_nonneg_antitone (la : AllWt.Weight Dw) (m : ℤ) (ha : ∀ τ, Antitone (la τ))
    (hb : ∀ τ (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p → m ≤ la τ k)
    (hs : ∀ τ (k : Fin (Dw.p + Dw.q)), Dw.p ≤ (k : ℕ) → la τ k ≤ -m) :
    (∀ x, 0 ≤ (wtOf Dw la m).1 x) ∧ ∀ τ, Antitone fun i => (wtOf Dw la m).1 (τ, i) := by
  have h0 : ∀ x, 0 ≤ (wtOf Dw la m).1 x := by
    intro x
    simp only [wtOf]
    split_ifs with h hi h' hi
    · have := hb ⟨x.1, h⟩ ⟨x.2, by omega⟩ hi
      omega
    · exact le_rfl
    · have := hs ⟨_, h'⟩ ⟨Dw.p + (Dw.q - 1 - x.2), by omega⟩ (Nat.le_add_right _ _)
      omega
    · exact le_rfl
    · exact le_rfl
  refine ⟨h0, fun τ i j hij => ?_⟩
  have hi0 := h0 (τ, i)
  simp only [wtOf] at hi0 ⊢
  by_cases h : τ (H.rt : E) = H.rt0
  · simp only [dif_pos h] at hi0 ⊢
    by_cases hj : j < Dw.p
    · have hi : i < Dw.p := by omega
      simp only [dif_pos hi, dif_pos hj]
      have := ha ⟨τ, h⟩ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨j, by omega⟩ from hij)
      omega
    · simpa only [dif_neg hj] using hi0
  · have h' := AllWt.conj_mem h
    simp only [dif_neg h, dif_pos h'] at hi0 ⊢
    by_cases hj : j < Dw.q
    · have hi : i < Dw.q := by omega
      simp only [dif_pos hi, dif_pos hj]
      have := ha ⟨_, h'⟩ (show (⟨Dw.p + (Dw.q - 1 - j), by omega⟩ : Fin (Dw.p + Dw.q)) ≤
        ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))
      omega
    · simpa only [dif_neg hj] using hi0

theorem exists_exponents (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (m : ℕ) (la : AllWt.Weight Dw) (hp : 1 ≤ Dw.p) (ha : ∀ τ, Antitone (la τ))
    (hg : ∀ τ, ((2 * m + 2 : ℕ) : ℤ) ≤ GlobalTheory.CompHS.gap (la τ) (Dw.p - 1)) :
    ∃ a : (E →+* ℂ) × ℕ → ℕ, Formalism.L2.Pj.Dom a (2 * m) ∧
      GlobalTheory.CovTop.laOf Dw a (2 * m) =
        la + GlobalTheory.FlatLine.parWt Dw (fun τ => 1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) ∧
      ∀ (τ : Psi H) (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p →
        (((2 * m) / 2 : ℕ) : ℤ) < GlobalTheory.CovTop.laOf Dw a (2 * m) τ k := by
  set lb : AllWt.Weight Dw := la + GlobalTheory.FlatLine.parWt Dw (fun τ => 1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) with hlb
  have e : ∀ τ k, lb τ k = la τ k + (1 + (m : ℤ) - la τ ⟨Dw.p - 1, by omega⟩) := fun _ _ => rfl
  have hb : ∀ τ (k : Fin (Dw.p + Dw.q)), (k : ℕ) < Dw.p → (m : ℤ) < lb τ k := by
    intro τ k hk
    have := ha τ (show k ≤ (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) from Fin.le_def.2 (by simp only; omega))
    rw [e]; omega
  have hs : ∀ τ (k : Fin (Dw.p + Dw.q)), Dw.p ≤ (k : ℕ) → lb τ k ≤ -(m : ℤ) := by
    intro τ k hk
    have hk2 := k.2
    have hlt : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega
    have h1 := hg τ
    rw [GlobalTheory.CompHS.gap, dif_pos hlt] at h1
    have h2 := ha τ (show (⟨Dw.p - 1 + 1, hlt⟩ : Fin (Dw.p + Dw.q)) ≤ k from Fin.le_def.2 (by simp only; omega))
    rw [e]; push_cast at h1; omega
  have hanti : ∀ τ, Antitone (lb τ) := fun τ i j hij => by
    have := ha τ hij
    rw [e, e]; omega
  obtain ⟨h0, h1⟩ := wtOf_nonneg_antitone lb m hanti (fun τ k hk => (hb τ k hk).le) hs
  have hm : 2 * m / 2 = m := by omega
  have hla : GlobalTheory.CovTop.laOf Dw (fun x => ((wtOf Dw lb m).1 x).toNat) (2 * m) = lb := by
    rw [GlobalTheory.CovTop.laOf, hm]
    simp only [Int.toNat_of_nonneg (h0 _)]
    exact AllWt.weightOf_wtOf lb m
  refine ⟨fun x => ((wtOf Dw lb m).1 x).toNat, ⟨fun τ i j hij => Int.toNat_le_toNat (h1 τ hij), even_two_mul m⟩, hla, ?_⟩
  intro τ k hk
  rw [hla, hm]
  exact hb τ k hk

end GlobalTheory.ThetaWtGap
end

section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC

namespace GlobalTheory.DeepLaws

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isGalois_of_aut (K L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] (j : K →+* L)
    (hj : ∀ a : K, ((j a : L) : ℂ) = a)
    (hs : ∀ s : ℂ ≃+* ℂ, (∀ a ∈ K, s a = a) → ∀ a ∈ L, s a ∈ L) :
    letI : Algebra K L := j.toAlgebra
    IsGalois K L := by
  letI : Algebra K L := j.toAlgebra
  haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq fun a => (hj a).symm
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun a => by simp
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  have : Normal K L := by
    refine normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, ?_⟩
    refine Polynomial.Splits.of_splits_map (algebraMap L ℂ) (IsAlgClosed.splits _) fun a ha => ?_
    have hroot : a ∈ (minpoly K x).rootSet ℂ := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at ha
      exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 ha)
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hroot
    obtain ⟨φ, rfl⟩ := hroot
    obtain ⟨s, hsφ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.extendEmb_holds L inferInstance (φ.restrictScalars ℚ)
    have hfix : ∀ a ∈ K, s a = a := by
      intro a ha
      have h1 := hsφ (j ⟨a, ha⟩)
      rw [hj] at h1
      refine h1.trans ?_
      exact φ.commutes (⟨a, ha⟩ : K)
    have hmem : s (x : ℂ) ∈ L := hs s hfix _ x.2
    refine ⟨⟨s (x : ℂ), hmem⟩, ?_⟩
    exact hsφ x
  exact IsGalois.mk

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}

theorem frPt_eq {S : Type} [CommRing S] [Algebra c.F S] {y z : FrPt Xo c S} (hx : y.x = z.x) (hu : y.u = z.u)
    (hs : HEq y.s z.s) : y = z := by
  obtain ⟨x, xo, u, t, e, b, s, g⟩ := y
  obtain ⟨x', xo', u', t', e', b', s', g'⟩ := z
  obtain rfl : x = x' := hx
  obtain rfl : u = u' := hu
  obtain rfl : s = s' := eq_of_heq hs
  rfl

theorem laws_galois_pull : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → Laws D j Y.d.Xo₂ Y.d.c₂ Y.U Y.dict ∧ (letI : Algebra T.Q.c.F Y.d.c₂.F := ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)).toAlgebra; IsGalois T.Q.c.F Y.d.c₂.F) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ g, Y.Pull f g ↔ Pull Y.d (rulBC Y.hle f) g := by
  intro D T j Y e o hJ hj hG hdm hmod
  refine ⟨?_, ?_, ?_⟩
  · exact
      { inR := hj
        host := hJ.pins.1
        dat := hJ.pins.2.2.2 j hj
        levA := hG.lev.2
        unf := hG.unf
        chiTriv := hG.chiTriv
        dictU := fun σ hσ => by
          obtain ⟨th, hr, h1, h2⟩ := hG.dictU σ hσ
          refine ⟨Y.Kf, th, hr, ?_, h1, h2, hdm σ hσ⟩
          have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by
            rw [hG.lev.1.2.1, hJ.pins.2.1.1]
          rw [hM]
          exact hG.levelK
        modelW := hmod }
  · haveI := Y.d.c₂.fin
    refine isGalois_of_aut T.Q.c.F Y.d.c₂.F _ (fun a => rfl) fun s hs a ha => ?_
    have hF := Y.d.hF
    rw [hF] at ha ⊢
    exact hG.normal s hs a ha
  · intro a n f hf g
    have hV := (rulBC_sec_val_linear D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c Y.c' Y.hle).1 a n f hf
    constructor
    · intro hP k _ _ _ _ hk y₂ y hO
      letI : Algebra T.Q.c.F k := resAlg Y.hle k
      have hA : AlgOver T.Q.c Y.c' Y.hle k := fun _ => rfl
      rw [hV.2 k hA y]
      exact hP k hA hk y₂ y (y.res Y.hle hA) hO rfl rfl HEq.rfl
    · intro hP k _ _ _ _ _ hA hk y₂ y' y hO hx hu hs
      have hy : y = y'.res Y.hle hA := frPt_eq hx hu hs
      rw [hy, ← hV.2 k hA y']
      exact hP k hk y₂ y' hO

end GlobalTheory.DeepLaws

end
end

section

open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Cx GlobalTheory.CovTop

noncomputable section

namespace GlobalTheory.FrameRead

theorem normAt_eq_sqrt {K : Type} [Field K] [NumberField K] {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (v : InfinitePlace K) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.cnorm
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show star (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v x i) = (starRingEnd ℂ) (Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin n)) X v x i) from rfl,
    Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem frames_read : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (b : Bool)
    (i : Fin D.R.m), (R.toCx3 F).KForm b →
    (∀ v, IsUnit ((R.toCx3 F).XW b i v).det) ∧
      ∀ v (c : Fin (Module.finrank D.what₂.LL (R.toRealDat.WL F.lv2 b i)) → D.what₂.LL),
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).XW b i) v c =
          (Real.sqrt (RealDat.nP F.lv2 b))⁻¹ * nrmR R.toRealDat i v.embedding (∑ k, c k • R.toRealDat.bL F.lv2 b i k) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F b i hK
  refine ⟨fun v => frame_gram_unit _ (hK i v).1, fun v c => ?_⟩
  have h1 := normAt_eq_sqrt (n := (R.toCx3 F).dW b i) ((R.toCx3 F).XW b i) v c
  have h2 := majAt_gram ((R.toCx3 F).XW b i) v ((R.toCx3 F).bW b i v) (hK i v).1 rfl c c
  refine h1.trans ?_
  have h3 : ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (z : E), Real.sqrt (inner ℂ z z).re = ‖z‖ := by
    intro E _ _ z
    rw [show (inner ℂ z z).re = ‖z‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) z, Real.sqrt_sq (norm_nonneg _)]
  rw [h2, h3]
  set s := twAt D.what₂.embLL v
  set σ := sgAt D.what₂.embLL v
  have hl : lin ((R.toCx3 F).bW b i v) (cpt v.embedding c) =
      Tw.mk s (∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ)) := by
    rw [lin_apply]
    have e : ∀ x : ↥(R.toRealDat.WS F.lv2 b i σ), Tw.mk s x = Tw.mkL s ↥(R.toRealDat.WS F.lv2 b i σ) x := fun _ => rfl

    rw [e, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ]
    show v.embedding (c k) • _ = _
    rw [emb_eq D.what₂.embLL v (c k)]
    rfl
  rw [hl]
  have hc : (((∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ)) : R.toRealDat.WS F.lv2 b i σ) : (R.HW i σ).H) =
      (((Real.sqrt (RealDat.nP F.lv2 b))⁻¹ : ℝ) : ℂ) • (R.FW i).j σ (∑ k, c k • R.toRealDat.bL F.lv2 b i k) := by
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul, RealDat.bC]

    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, smul_comm]
  calc ‖Tw.mk s (∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ))‖
      = ‖(((∑ k, σ (c k) • (⟨R.toRealDat.bC F.lv2 b i σ k, Submodule.subset_span ⟨k, rfl⟩⟩ :
        R.toRealDat.WS F.lv2 b i σ)) : R.toRealDat.WS F.lv2 b i σ) : (R.HW i σ).H)‖ := rfl
    _ = _ := by
      rw [hc, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
      unfold nrmR
      rw [InfinitePlace.mk_embedding]

end GlobalTheory.FrameRead
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.exists_quotient_nilCrystallineThickening_of_subDPIdeal : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (T : Thick κ t) (𝔟 : Ideal T.B), T.δ.IsSubDPIdeal 𝔟 → ∃ (G : Thick κ t) (q : T ⟶ G), Function.Surjective q.φ ∧ (∀ b, q.φ b = 0 ↔ b ∈ 𝔟) ∧ G.J = T.J.map (q.φ : T.B →+* G.B) ∧ (∀ n, IsLev T.δ n → IsLev G.δ n) ∧ ∀ (S : Thick κ t) (a : T ⟶ S), (∀ b ∈ 𝔟, a.φ b = 0) → ∃! g : G ⟶ S, q ≫ g = a := by
  first | exact @GlobalTheory.ThickQuot.exists_quotient | exact GlobalTheory.ThickQuot.exists_quotient | (intros; apply GlobalTheory.ThickQuot.exists_quotient <;> assumption)
end

section

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdTh.PhaseMapCore
open GlobalTheory.AdTh.PhaseMap


set_option maxHeartbeats 1600000 in
theorem io_eq_phase_smul_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank), (∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (t : T0) (v : VsV D i O.c'.F), R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' v)) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename lt (MvPolynomial.map (inC O.c') (O.io v))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR hT hE i Tp tup O hO
  have hstd := hO.lift.std
  have hθ : IsInfFam R.θ := hR.models.inf
  have hc : (R.cV i).Is := hR.models.cV i
  have hP := (GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A _ R F hR i A.μ0 hstd).1
  have hψ := hP.weil.std
  have hF := fun t => GlobalTheory.AdTh.VecFockCore.vec_fock_core D G Pl0 T0 A _ R F hR i t hstd
  obtain ⟨f1, f2, f3, f4, f5⟩ := hF A.μ0
  obtain ⟨n1, n2, n3, n4⟩ := GlobalTheory.AdTh.OverCore.coefMap_norm_equivariant_basis D G Pl0 T0 A T R F κ v₀ hR hT i Tp tup O hO
  obtain ⟨r1, r2, -⟩ := GlobalTheory.RatGen.rational_points_generate D (Vc D i) (R.cV i) (hR.models.vpos i) hP.sigV hc
  obtain ⟨-, -, w1, w2, w3⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hT.laws.pins _ (inR i) (κ i)
  have hty : IsTyp D T.Q.H := ⟨w1, w2⟩
  obtain ⟨d1, d2, -⟩ := hT.laws.pins.2.2.2 _ (inR i)
  have hsig : ∀ τ, (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) := fun τ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨-, cga, i1, i2, -, i3, -, -, i4, -⟩ := hO.io
  obtain ⟨u₀, w₀, hu₀, hw₀, hΔ⟩ : ExtremalVectorPairsToDelta R i (v₀ i (sg0 D A)) := (hT.hv₀ i (sg0 D A)).2 rfl (hE i)
  have hio := (hR.thP.ioP i A.μ0).1
  have hBV : ∀ τ, (R.BV i τ)ᴴ * R.BV i τ = 1 := fun τ => by
    obtain ⟨ε, hε, h1, -⟩ := hR.models.BV i τ
    rw [gramAt_one hP.std, Matrix.mul_one] at h1
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases hε a with h | h
    · rw [h.1]; rfl
    · exact absurd a.2 (not_lt.2 h.2)
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D i) τ) 1 1 (Vc D i).rank := fun τ =>
    ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, by simp [gramAt_one hP.std], by simp⟩
  let PT := fun t => pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1)
    (onb (R.MW i (sg0 D A))) (R.vP i t)
  have hsub : ∀ t (U : D.what₂.Tau → Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ), (∀ τ, (U τ)ᴴ * U τ = 1) → ∀ P,
      pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) U (onb (R.MW i (sg0 D A))) (R.vP i t) P =
        PT t (sub (fun τ => ((Wc D i).sig (tauE D τ)).1) U P) := fun t U hU P => by
    have h := GlobalTheory.AdTh.SourceBasis.pureTensorO_mul_source D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) U _ _ _ f5
      (fun τ => (trace_parity (f5 τ)).1) (fun τ => by simp) (fun τ => det_ne_zero (hU τ)) _ (hF t).1 P
    simp only [Matrix.one_mul] at h
    exact h
  have hinj : Function.Injective (PT A.μ0) :=
    GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ _ _ f4 f3 hon f5 hP.sigV hP.sigW _ f1 f2
      (GlobalTheory.AdTh.VecNeCore.thetaVector_ne_zero_core D G Pl0 T0 A _ R F hR i hstd)
  obtain ⟨g, hg, hgB⟩ : ∃ g ∈ GinfC (Vc D i), ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) g) = R.BV i τ :=
    (GlobalTheory.SmoothForms.RealPts.glue R.θ hθ (Vc D i)).2 (R.BV i) fun τ => by
      show (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = gramAt D (Vc D i) τ
      rw [gramAt_one hP.std, Matrix.mul_one, hBV]
  obtain ⟨χ, hχ, hχg⟩ := om_real hP f4 f3 f5 f1 f2 hg
  rw [funext hgB] at hχg
  have hχ0 : χ ≠ 0 := fun h => by simp [h] at hχ
  let A₀ : (R.cV i).W →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) :=
    pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i A.μ0) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u₀)
  have hA₀ : ∀ a ∈ GinfC (Vc D i), ∀ w, A₀ ((R.cV i).ρ a w) = R.ωP i A.μ0 (a, 1) (A₀ w) :=
    fun a ha w => (hio a ha _ w).symm
  have hw₁ : A₀ ((R.cV i).ρ g⁻¹ (χ • w₀)) = PT A.μ0 (RealDat.Delta i) := by
    have h1 : A₀ (χ • w₀) = R.ωP i A.μ0 (g, 1) (PT A.μ0 (RealDat.Delta i)) := by
      rw [map_smul, hχg, ← hΔ]
      rfl
    rw [hA₀ _ (inv_mem hg), h1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one]
    exact congrArg (fun T : Module.End ℂ _ => T _) (map_one (R.ωP i A.μ0))
  have hn₁ : ‖(R.cV i).ρ g⁻¹ (χ • w₀)‖ = 1 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hc.2.1, ← norm_eq_sqrt_re_inner, norm_smul, hχ, hw₀, mul_one]
  haveI := hc.2.2.2.1
  haveI : FiniteDimensional O.c'.F (VsV D i O.c'.F) := Module.Finite.of_basis (Formalism.L2.DIV.bVV O.c'.F (lamV D i))
  have main : ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank, IsLt lt →
      ∃ a : ℂ, a • (R.cV i).ρ g⁻¹ (χ • w₀) = O.c0' O.hw ∧ ∀ t v, R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u₀) (O.c0' v)) =
        a • PT t (toF O.c' lt (O.io v)) := fun lt hl => by
    have hsm : ∀ (a : O.c'.F) P, toF O.c' lt (a • P) = (a : ℂ) • toF O.c' lt P := fun a P => by
      rw [MvPolynomial.smul_eq_C_mul, map_mul, toF_C, MvPolynomial.smul_eq_C_mul]
    set_option synthInstance.maxHeartbeats 400000 in
      obtain ⟨B₀, hB₀⟩ := exists_ext O.c0' n4
        { toFun := fun v => toF O.c' lt (O.io v)
          map_add' := fun v w => by rw [map_add (f := _), map_add (f := _)]
          map_smul' := fun a v => by rw [map_smul, hsm]; rfl }
    replace hB₀ : ∀ v, B₀ (O.c0' v) = toF O.c' lt (O.io v) := hB₀
    have hpG : toF O.c' lt (O.io O.hw) = RealDat.Delta i := by
      rw [i4]
      refine toF_pG O.c' hl hty i1 _ _ _ _ _ (fun τ => by rw [hsig, d1]) (fun τ => by rw [hsig, d2]) (fun τ k hk => ?_)
        fun τ k hk => ?_
      · rw [d1] at hk
        exact (w3 τ k).1.trans ((dif_pos hk).trans ((hT.kap i τ).1 ⟨k, hk⟩))
      · rw [d2] at hk
        exact (w3 τ k).2.trans ((dif_pos hk).trans ((hT.kap i τ).2.1 ⟨k, hk⟩))
    obtain ⟨a, ha, ha'⟩ := proportional ((R.cV i).ρ.comp (GQ (Vc D i)).subtype) _ r1 (fun γ hγ => hγ) r2 A₀ (PT A.μ0 ∘ₗ B₀)
      (fun γ => by
        obtain ⟨γE, a, k, h1, h2, h3, h4, h5, h6⟩ := rat_parts hθ hP.std γ
        obtain ⟨x, hx, hxa⟩ := om_real hP f4 f3 f5 f1 f2 h2
        have hx0 : x ≠ 0 := fun h => by simp [h] at hx
        have h7 : (R.cV i).ρ γ = (R.cV i).ρ a := by rw [h4, map_mul, hc.1 k h3, mul_one]
        refine ⟨R.ωP i A.μ0 (a, 1), (cga γE.val : ℂ) * x⁻¹, fun w => ?_, fun w => ?_⟩
        · show A₀ ((R.cV i).ρ γ w) = _
          rw [h7, hA₀ a h2]
        · have h8 : (PT A.μ0 ∘ₗ B₀) ∘ₗ (R.cV i).ρ γ =
              ((cga γE.val : ℂ) * x⁻¹) • (R.ωP i A.μ0 (a, 1) ∘ₗ (PT A.μ0 ∘ₗ B₀)) := by
            refine LinearMap.ext_on_range n3 fun v => ?_
            simp only [LinearMap.comp_apply, LinearMap.smul_apply]
            rw [← n2 γ γE h1, hB₀, hB₀, i3 _ h5, hsm, hxa, hsub _ _ (compAt_unitary hθ hP.std a), smul_smul,
              inv_mul_cancel_right₀ hx0, map_smul,
              toF_gaStar O.c' hl hty (fun τ => ((Wc D i).sig (tauE D τ)).1) (fun τ => by rw [hsig, d1]) _ _ h6]
          exact LinearMap.congr_fun h8 w)
      ((R.cV i).ρ g⁻¹ (χ • w₀)) (O.c0' O.hw) (by rw [hw₁, LinearMap.comp_apply, hB₀, hpG])
      (fun h => by
        rw [LinearMap.comp_apply, hB₀, map_eq_zero_iff _ hinj, map_eq_zero_iff _ (toF_injective O.c' hl hty),
          map_eq_zero_iff _ i2] at h
        rw [h, map_zero, norm_zero] at n1
        exact zero_ne_one n1)
    refine ⟨a, ha', fun t v => ?_⟩
    have h9 : sub (fun τ => ((Wc D i).sig (tauE D τ)).1) (R.BV i) (R.ioP i (PiTensorProduct.tprod ℂ u₀) (O.c0' v)) =
        a • toF O.c' lt (O.io v) := hinj (by rw [← hsub _ _ hBV, map_smul, ← hB₀]; exact ha _)
    rw [← map_smul, ← h9, ← hsub _ _ hBV]
    rfl
  by_cases hex : ∃ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank, IsLt lt
  · obtain ⟨lt₀, hl₀⟩ := hex
    obtain ⟨a, ha, -⟩ := main lt₀ hl₀
    refine ⟨a, ?_, fun lt hl u hu t v => ?_⟩
    · rw [← n1, ← ha, norm_smul, hn₁, mul_one]
    · obtain rfl : u = u₀ := funext fun ρ => Subtype.ext ((hu ρ).trans (hu₀ ρ).symm)
      obtain ⟨b, hb, hb'⟩ := main lt hl
      obtain rfl : a = b := smul_left_injective ℂ (fun h => by simp [h] at hn₁) (ha.trans hb.symm)
      exact hb' t v
  · exact ⟨1, norm_one, fun lt hl => absurd ⟨lt, hl⟩ hex⟩

end GlobalTheory.AdTh.PhaseMapCore

end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.doubledWeilRepresentation_locality_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a'))) (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) →* Module.End ℂ (((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) B.ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ g : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J)), At (evFin F v) (GlobalTheory.InertDbl.matD g - 1) →
    ∀ φ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), ∃ φ₁ ∈ SB ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → Fv F v), Acts (evFin F v) (omd g) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityDbl.locality | exact GlobalTheory.WeilLocalityDbl.locality | (intros; apply GlobalTheory.WeilLocalityDbl.locality <;> assumption)
end
