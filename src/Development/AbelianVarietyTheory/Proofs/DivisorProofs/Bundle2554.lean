module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle038
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle039
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortGeneratorPlaceValuationBoundProof
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDegeneratePrincipalSeriesLaw
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormIntegralIffLatticeUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusOfNormEqAbs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle057
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfShortRule
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat GlobalTheory.ShortBound
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovInt



theorem smul_intZ_nonneg_away : ∀ (D : D7) (H : Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ)
    (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ →
    (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ = 1) →
    (∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) → d.l₂.M ≠ 0 →
    ∀ (Λ : GenLat D.host.E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M →
    ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w →
    ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g →
    ∀ la : HeightOneSpectrum (𝓞 c.F), (∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → ¬ ℓ ^ 2 ∣ d.l₂.M) →
    ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v ((betaH (Dw := Dw) c Λ * (intZ D Dw d.l₂ n w : c.F)) • g) := by
  intro D H Dw l Xo c n d _ hlev hnab hroot hwi hM0 Λ N hU hTM hN w P hP x0 g hsec hR la hla v hv
  have hroot1 : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k),
      evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1 := fun k _ _ y₂ => by rw [pow_one]; exact hroot k y₂
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    exacts [h.choose_spec.1, one_ne_zero]
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : ℕ, P₀ = (NumberField.discr D.host.E).natAbs := ⟨_, rfl⟩
  have hP0 : P₀ ≠ 0 := hP₀ ▸ Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero _)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = P₀ ^ Formalism.L2.Pj.DF Dw w * d.l₂.M ^ Formalism.L2.Pj.DF Dw w *
    Nat.card (Fin n → LevQ Dw d.l₂) := ⟨_, rfl⟩
  have hK0 : K ≠ 0 := hK ▸ mul_ne_zero (mul_ne_zero (pow_ne_zero _ hP0) (pow_ne_zero _ hM0)) hc0
  have hKZ : intZ D Dw d.l₂ n w = K := by rw [intZ, hK, hP₀]; ring
  rw [hKZ, mul_comm]
  obtain ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩ := hv
  show 0 ≤ nval Tc.V e (evI yI _)
  rw [evI_smul]
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot1 Λ N hU hTM hN w P hP x0 g hsec hR
      Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have heR : (0 : ℝ) < ((r * e : ℕ) : ℝ) := by exact_mod_cast he'
  rw [← nval_bc iT hr hiT e, map_mul, hval, ← hio]
  obtain ⟨ℓ, hℓ, hu⟩ := GlobalTheory.ShortBound.exists_resChar T' hfr
  have hmem : (ℓ : 𝓞 c.F) ∈ la.asIdeal := by
    by_contra hnm
    have h2 := ho'.2 (ℓ : c.F)
    have hv1 : la.valuation c.F (ℓ : c.F) = 1 := by
      rw [← map_natCast (algebraMap (𝓞 c.F) c.F)]
      exact la.valuation_eq_one_iff_notMem.2 hnm
    have hv0 : vLa la (ℓ : c.F) = 0 := by simp [vLa, hv1]
    rw [map_natCast, hv0, mul_zero] at h2
    have h0 : (ℓ : T'.V) ≠ 0 := fun h0 => by
      have : algebraMap T'.V T'.Fr (ℓ : T'.V) = 0 := by rw [h0, map_zero]
      rw [map_natCast] at this
      exact hℓ.ne_zero (by exact_mod_cast this)
    have h3 := GlobalTheory.PlaceExtField.vV_pos (K' := T'.Fr) h0 hu
    rw [map_natCast] at h3
    omega
  have hsq : ¬ ℓ ^ 2 ∣ d.l₂.M := hla ℓ hℓ hmem
  obtain ⟨α, hαM, hα⟩ : ∃ α : ℕ, α ∣ d.l₂.M ∧ ((¬ ℓ ∣ d.l₂.M ∧ (α : 𝓞 D.host.E) = 1) ∨
      (ℓ ∣ d.l₂.M ∧ (α : 𝓞 D.host.E) * H.bar α = (ℓ : 𝓞 D.host.E) ∧ d.l₂.Mb ≤ Ideal.span {H.bar α}) ∨
      (ℓ ∣ d.l₂.M ∧ (α : 𝓞 D.host.E) = (ℓ : 𝓞 D.host.E))) := by
    by_cases hd : ℓ ∣ d.l₂.M
    · exact ⟨ℓ, hd, Or.inr (Or.inr ⟨hd, rfl⟩)⟩
    · exact ⟨1, one_dvd _, Or.inl ⟨hd, Nat.cast_one⟩⟩
  obtain ⟨α', hα'⟩ := hαM
  have ha0 : α ≠ 0 := left_ne_zero_of_mul (hα' ▸ hM0)
  have ha0' : α' ≠ 0 := right_ne_zero_of_mul (hα' ▸ hM0)
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  haveI := Nat.finite_of_card_ne_zero hc0
  have hu0 : io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E)) ≠ 0 :=
    (map_ne_zero io₂).2 (nrm_ne_zero _ _ (Nat.cast_ne_zero.2 ha0))
  have key := le_nval_avg (V := T'.V) (r * e) (fun q => io₂ (d.w x0 q)) _ ζ _
    ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) _ 1 one_pos hζ hu0 (by exact_mod_cast hc0)
    (fun q => map_isIntegral_int io₂ (hwi x0 q)) _
    (fun q => GlobalTheory.SupFull.class_bound d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he' hch ℓ hℓ
      hu Λ N hU hTM hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi
      (fun b => levRep (q b)) (htp q) (hF q) hrat hsq α hα)
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hKv := add_le_add (le_refl (nval T'.V (r * e) (K : T'.Fr))) key
  rw [← nval_mul, nval_of_ne (Nat.cast_ne_zero.2 hK0), ← EReal.coe_add] at hKv
  refine le_trans (EReal.coe_nonneg.2 ?_) (hKv.trans (le_of_eq ?_))
  · have b0 : ∀ p : ℕ, (0 : ℝ) ≤ vV T'.V (p : T'.Fr) := fun p => by
      exact_mod_cast GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T' p
    have b1 : (vV T'.V (K : T'.Fr) : ℝ) = (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (P₀ : T'.Fr) : ℝ) +
        (Formalism.L2.Pj.DF Dw w : ℕ) * ((vV T'.V (α : T'.Fr) : ℝ) + vV T'.V (α' : T'.Fr)) +
        vV T'.V ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) := by
      rw [hK, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
        vV_mul (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hP0)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hM0)))
          (Nat.cast_ne_zero.2 hc0),
        vV_mul (pow_ne_zero _ (Nat.cast_ne_zero.2 hP0)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hM0)),
        vV_pow (Nat.cast_ne_zero.2 hP0), vV_pow (Nat.cast_ne_zero.2 hM0)]
      conv_lhs => rw [show ((d.l₂.M : ℕ) : T'.Fr) = (α : T'.Fr) * (α' : T'.Fr) by rw [hα', Nat.cast_mul],
        vV_mul (Nat.cast_ne_zero.2 ha0) (Nat.cast_ne_zero.2 ha0')]
      push_cast
      ring
    have b2 : (vV T'.V (io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E))) : ℝ) = (Formalism.L2.Pj.DF Dw w : ℕ) * vV T'.V (α : T'.Fr) := by
      rw [nrm_nat, map_pow, map_natCast, vV_pow (Nat.cast_ne_zero.2 ha0)]
      push_cast
      ring
    have b3 : ∑ p ∈ D.host.condN.primeFactors, (vV T'.V (p : T'.Fr) : ℝ) / (r * e : ℕ) *
        D.host.vdH p * (Formalism.L2.Pj.DF Dw w : ℝ) / 2 ≤ (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (P₀ : T'.Fr) : ℝ) / (r * e : ℕ) := by
      have h := ram_sum_le_vV_discr D.host.E T' _ (fun p (hp : p ∈ D.host.condN.primeFactors) => Nat.prime_of_mem_primeFactors hp)
        (r * e) (Formalism.L2.Pj.DF Dw w)
      rw [← hP₀, Nat.cast_pow, vV_pow (Nat.cast_ne_zero.2 hP0), Int.cast_mul, Int.cast_natCast] at h
      rw [hP₀] at h ⊢
      exact h
    have b4 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℕ) * (vV T'.V (α' : T'.Fr) : ℝ) / (r * e : ℕ) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (b0 _)) heR.le
    rw [b1, b2, add_div, add_div, mul_add, add_div]
    linarith
  · congr 1
    simp only [map_mul, map_inv₀, map_natCast]
    field_simp

end GlobalTheory.CovInt
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagThetaRule

open GlobalTheory.Doubling Formalism.IndefR.Datum

theorem ddr_rat : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ x : Matrix (Fin T.rank) (Fin (dblSp S).rank) D.host.E, ∃ y z : κ ⊕ κ → D.host.F,
      (GlobalTheory.DblSchr.ddr co).e (incM D.host.F x) =
        (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) := by
  intro D S T JA JB ξ κ _ co hco x
  obtain ⟨y₁, z₁, h₁⟩ := hco ((x.submatrix id finSumFinEquiv).toCols₁)
  obtain ⟨y₂, z₂, h₂⟩ := hco ((x.submatrix id finSumFinEquiv).toCols₂)
  refine ⟨Sum.elim y₁ y₂, Sum.elim z₁ (-z₂), ?_⟩
  have e : (GlobalTheory.DblSchr.ddr co).e (incM D.host.F x) =
      (Sum.elim (co.e (incM D.host.F (x.submatrix id finSumFinEquiv).toCols₁)).1
          (co.e (incM D.host.F (x.submatrix id finSumFinEquiv).toCols₂)).1,
        Sum.elim (co.e (incM D.host.F (x.submatrix id finSumFinEquiv).toCols₁)).2
          (-(co.e (incM D.host.F (x.submatrix id finSumFinEquiv).toCols₂)).2)) := rfl
  rw [e, h₁, h₂]
  ext (i | i) <;> simp

theorem actO_epsD_lagr : ∀ (D : D7) (S T : HSp D) (w : WO S T),
    actO (dblSp S) T (epsD S)⁻¹ 1 (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr S T w) = GlobalTheory.DiagSiegel.diagMat w := by
  intro D S T w
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr S T w = (Matrix.fromCols w (-w)).submatrix id finSumFinEquiv.symm := by
    ext i j
    rcases h : finSumFinEquiv.symm j with k | k <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, h]
  have h1 : Formalism.L2.Theta.mt T (1 : GA D T) = 1 := by simp [Formalism.L2.Theta.mt]
  unfold actO
  rw [inv_inv, h1, Matrix.one_mul, mt_epsD, hl, blkMat, Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]
  simp [GlobalTheory.DiagSiegel.diagMat]

theorem epsD_mem_GQ : ∀ (D : D7) (S : HSp D), epsD S ∈ GQ (dblSp S) := by
  intro D S
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2
    ⟨blkGL finSumFinEquiv ((1, -1) : GL (Fin S.rank) D.host.E × GL (Fin S.rank) D.host.E), ?_, ?_⟩)
  · rw [show (dblSp S).gram = blkMat finSumFinEquiv S.gram (-S.gram) from gram_hdbl S, blkGL_mem_UJ]
    exact ⟨one_mem _, neg_one_mem_UJ _ _⟩
  · rw [bc_blkGL]
    apply Units.ext
    show blkMat finSumFinEquiv _ _ = blkMat finSumFinEquiv (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) (-1)
    simp [Formalism.UG.bc]

theorem rat_act : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V T : HSp D) (χV χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D T →* Module.End ℂ (WO V T → ℂ)), IsWeilDatumO ψ V T χV χT ω →
    ∀ γ ∈ GQ V, ∀ f, IsThetaFunO ψ V T f → ∀ x, ω (γ, 1) f x = f (actO V T γ⁻¹ 1 x) := by
  intro D ψ V T χV χT ω hW γ hγ f hf x
  have hx : actO V T γ 1 (actO V T γ⁻¹ 1 x) = x := by
    simp only [actO, Formalism.L2.Theta.mt, map_one, Units.val_one, Matrix.one_mul, inv_inv, Matrix.mul_assoc,
      ← Units.val_mul, ← map_mul, mul_inv_cancel, Matrix.mul_one]
  have e1 : ∀ (g : WO V T → ℂ) (y : WO V T), heisO ψ V T y g 0 = g y := by
    intro g y
    have h0 : symplOH V T 0 y = 0 := by simp [symplOH, symplO, hO]
    simp only [heisO, zero_add, h0, AddChar.map_zero_eq_one, one_mul]
  calc ω (γ, 1) f x = heisO ψ V T x (ω (γ, 1) f) 0 := (e1 _ _).symm
    _ = heisO ψ V T (actO V T γ 1 (actO V T γ⁻¹ 1 x)) (ω (γ, 1) f) 0 := by rw [hx]
    _ = ω (γ, 1) (heisO ψ V T (actO V T γ⁻¹ 1 x) f) 0 := by rw [← hW.om_heis γ 1 _ f hf]
    _ = heisO ψ V T (actO V T γ⁻¹ 1 x) f 0 :=
      hW.om_aut γ hγ 1 (one_mem _) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf _)
    _ = f (actO V T γ⁻¹ 1 x) := e1 _ _

theorem exists_transpose_inv : ∀ (D : D7) (V : HSp D) (J : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), ξ • incM D.host.F J = incM D.host.F (D.host.xi0 • V.gram⁻¹) →
    ∀ b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F J),
      ∃ g : GA D V, Formalism.L2.Theta.mt V g = (b⁻¹).1.1ᵀ := GlobalTheory.T.exists_unitary_invTranspose_of_scaledInverseGram

theorem siegel_conj : ∀ (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
    (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)),
    p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1 →
    ∀ g : GA D (GlobalTheory.Doubling.dblSp S), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp S) g =
      ((GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)⁻¹).1.1ᵀ →
    ∃ h : GlobalTheory.Doubling.siegel S, GlobalTheory.DiagThetaRule.epsD S * g = (h : GA D (GlobalTheory.Doubling.dblSp S)) * GlobalTheory.DiagThetaRule.epsD S ∧
      GlobalTheory.Doubling.aP S h = GlobalTheory.Doubling.conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t) := GlobalTheory.T.exists_siegelParabolic_conj_invTranspose

theorem chi_conj : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ), ResEta D χ n → ∀ z : (AE D)ˣ,
    χ (conjUnit D.sp.cm.sig z) = (χ z)⁻¹ := by
  intro D χ n h z
  have := congrArg (fun m : (AE D)ˣ →* Circle => m z) (comp_conjUnit_eq_inv h)
  simpa using this

theorem absA_conj : ∀ (D : D7) (z : (AE D)ˣ), absA D (conjUnit D.sp.cm.sig z) = absA D z :=
  fun _ z => absE_conjUnit _ z

theorem absA_eq_modu : ∀ (D : D7) (z : (AE D)ˣ),
    absA D z = (GlobalTheory.WeilM.adeleClass D.host.F).modu (Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) z) :=
  fun D z => (GlobalTheory.ModuAdele.modu_norm_eq_absE D.host.F D.host.E z).symm

end GlobalTheory.DiagThetaRule

namespace GlobalTheory.DiagThetaRule

open GlobalTheory.Doubling Formalism.IndefR.Datum

theorem scalar_rule (D : D7) (S T : HSp D) (χT : (AE D)ˣ →* Circle) (hrT : ResEta D χT T.rank)
    (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    ((χT⁻¹ (conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t)) : Circle) : ℂ) *
        npow (absA D (conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det t))) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero S T + (S.rank : ℂ) / 2) =
      GlobalTheory.DiagSiegel.ruleFac (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) χT
        (Fintype.card (Fin T.rank)) t := by
  rw [MonoidHom.inv_apply, chi_conj D χT T.rank hrT, inv_inv, absA_conj, absA_eq_modu]
  unfold GlobalTheory.DiagSiegel.ruleFac GlobalTheory.Doubling.npow GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero
  rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  congr 2
  rw [Fintype.card_fin]
  push_cast
  ring

end GlobalTheory.DiagThetaRule

namespace GlobalTheory.DiagThetaRule


theorem thetaDiagInt_omdOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ (ν : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
            Formalism.IndefR.Datum.IsCovolOne (ratL T S) ν 𝓕 →
          ∀ (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
            ResEta D χS S.rank → ResEta D χT T.rank →
          ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
          ∀ omd₀ : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
              GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F (GlobalTheory.DblSchr.JBd S JB)) →*
              Module.End ℂ ((κ ⊕ κ → AF D.host.F) → ℂ),
            GlobalTheory.WeilSchrodinger.IsTransport ψ (GlobalTheory.DblSchr.ddr co) ωd omd₀ →
          ∀ (p : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.dbl (incM D.host.F JB)))
            (t : GL (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)),
            p.1.1 * GlobalTheory.WeilM.diagCols (Fin S.rank) = GlobalTheory.WeilM.diagCols (Fin S.rank) * t.1 →
          ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ),
            GlobalTheory.DblSchr.omdOf omd₀ p Φ ∈ GlobalTheory.WeilM.schA D.host.F (κ ⊕ κ) ∧
            GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ
                         (GlobalTheory.DblSchr.omdOf omd₀ p Φ)) =
              GlobalTheory.DiagSiegel.ruleFac (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) χT (Fintype.card (Fin T.rank)) t *
                GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hco ν 𝓕 hν χS χT hχS hχT hrS hrT ωd hW omd₀ hTr p t hpt Φ hΦ
  have hBd := GlobalTheory.DblSchr.dblGram_xi D S JB ξ hB
  obtain ⟨g', hg'⟩ := exists_transpose_inv D (GlobalTheory.Doubling.dblSp S) (GlobalTheory.DblSchr.JBd S JB) ξ hBd
    (GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm (GlobalTheory.DblSchr.incM_JBd S JB) p)
  have h1 : Formalism.L2.Theta.mt T (1 : GA D T) =
      (1 : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)).1.1 := by
    simp [Formalism.L2.Theta.mt]
  have key := hTr 1 _ g' 1 h1 hg' Φ hΦ
  refine ⟨key.1, ?_⟩
  rw [show GlobalTheory.DblSchr.omdOf omd₀ p = omd₀ (1, GlobalTheory.DblSchr.reG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) finSumFinEquiv.symm
    (GlobalTheory.DblSchr.incM_JBd S JB) p) from rfl, key.2]
  have hf : Formalism.IndefR.Datum.IsThetaFunO ψ (GlobalTheory.Doubling.dblSp S) T
      (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) :=
    GlobalTheory.T.isThetaFunction_thetaTransform_rationalDarboux D ψ hψ (GlobalTheory.Doubling.dblSp S) T JA (GlobalTheory.DblSchr.JBd S JB) ξ hA hBd (κ ⊕ κ) (GlobalTheory.DblSchr.ddr co)
      (ddr_rat D S T JA JB ξ κ co hco) Φ hΦ
  have hdiag : ∀ F, Formalism.IndefR.Datum.IsThetaFunO ψ (GlobalTheory.Doubling.dblSp S) T F →
      GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 F = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec S T ωd ν 𝓕 F (epsD S) := by
    intro F hF
    show ∫ w in 𝓕, F (GlobalTheory.DiagSiegel.diagMat w) ∂ν =
      ∫ w in 𝓕, ωd (epsD S, 1) F (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr S T w) ∂ν
    congr 1
    funext w
    rw [rat_act D ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd hW (epsD S) (epsD_mem_GQ D S) F hF, actO_epsD_lagr]
  obtain ⟨h, hεg, haP⟩ := siegel_conj D S JB p t hpt g' hg'
  have hlaw := GlobalTheory.Core.Rk.SWLaw.swSec_law GlobalTheory.weilRepresentationUnitaryPair D ψ S T χT ωd hW ν 𝓕 hν _ hf h (epsD S)
  have e1 : GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (ωd (g', 1) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ)) =
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec S T ωd ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ) (epsD S * g') := by
    rw [hdiag _ (hW.om_pres _ _ hf)]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e1, hεg, hlaw, ← hdiag _ hf, haP]
  exact congrArg (· * GlobalTheory.DiagSiegel.thetaDiagInt ν 𝓕 (GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ Φ))
    (scalar_rule D S T χT hrT t)
end GlobalTheory.DiagThetaRule

end
end
