module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle038
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvROfFrMapFromTest
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle039
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValuationLowerBoundHostFieldAllPlaces
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortGeneratorPlaceValuationBoundProof
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle041
public import Formalism.LocalRingCardinality.Bundle002
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



theorem smul_intZ_nonneg_coprime : ∀ (D : D7) (H : Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ)
    (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ →
    (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ = 1) →
    (∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) → d.l₂.M ≠ 0 →
    ∀ (Λ : GenLat D.host.E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M →
    ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w →
    ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g →
    ∀ la : HeightOneSpectrum (𝓞 c.F), (∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → ¬ ℓ ∣ d.l₂.M) →
    ∀ s : c.F, Submodule.span (𝓞 c.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤
      ∏ τ : D.host.E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ →
    ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v ((s * betaH (Dw := Dw) c Λ * (intZ D Dw d.l₂ n w : c.F)) • g) := by
  intro D H Dw l Xo c n d _ hlev hnab hroot hwi hM0 Λ N hU hTM hN w P hP x0 g hsec hR la hla s hs v hv
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
  have hd : ¬ ℓ ∣ d.l₂.M := hla ℓ hℓ hmem
  obtain ⟨α, hα1⟩ : ∃ α : ℕ, α = 1 := ⟨1, rfl⟩
  obtain ⟨α', hα'⟩ : ∃ α' : ℕ, d.l₂.M = α * α' := ⟨d.l₂.M, by rw [hα1, Nat.one_mul]⟩
  have ha0 : α ≠ 0 := by rw [hα1]; exact one_ne_zero
  have ha0' : α' ≠ 0 := right_ne_zero_of_mul (hα' ▸ hM0)
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  haveI := Nat.finite_of_card_ne_zero hc0
  have hu0 : io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E)) ≠ 0 :=
    (map_ne_zero io₂).2 (nrm_ne_zero _ _ (Nat.cast_ne_zero.2 ha0))
  have hsA : ∀ A : GlobalTheory.PlaceInt.Adapt Λ N ℓ, 0 ≤ nval T'.V (r * e)
      (io₂ (d.eF s * ∏ τ : D.host.E →+* ℂ, embK d.c₂ τ A.p.det ^ Dw.mult τ)) := by
    intro A
    have h := GlobalTheory.T.intersectedLattice_detIdeal_typeNorm_integral D.host.E H Dw l c n Λ N d.l₂.M ℓ hN hℓ A s hs T'
      (io₂.comp (d.eF : c.F →+* d.c₂.F)) hu (r * e)
    simpa [embK, map_prod, map_pow, GlobalTheory.PlaceInt.eF_embF] using h
  obtain ⟨t1, -⟩ := GlobalTheory.TorsFac.factorisation D.host.E H Dw d.l₂ d.Xo₂ N ℓ hN.1 hN.2.1 hℓ
  obtain ⟨n', j, -, -, h5⟩ := t1 hd
  have hcop : ∀ q, ∃ m : ℕ, Nat.Coprime m ℓ ∧ ∀ b, tp q b ^ m = 1 := fun q => by
    have hk : ∀ b, KilledBy d.Xo₂ d.l₂.Mb (tp q b ^ N) := fun b => by
      rw [(htp q b).1]; exact levPt_killed d.Xo₂ _ _
    choose i hi using fun b => (h5 _ _ (hk b) (htp q b).2).2.2
    refine ⟨d.l₂.M ^ (∑ b, i b), Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hd).symm, fun b => ?_⟩
    obtain ⟨m, hm⟩ : d.l₂.M ^ i b ∣ d.l₂.M ^ (∑ b, i b) :=
      pow_dvd_pow _ (Finset.single_le_sum (f := i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
    rw [hm, pow_mul, hi b, one_pow]
  have hN2 : ∀ q b, tp q b ^ (N ^ 2) = 1 := fun q b => by
    have hk : KilledBy d.Xo₂ d.l₂.Mb (tp q b ^ N) := by rw [(htp q b).1]; exact levPt_killed d.Xo₂ _ _
    exact (h5 _ _ hk (htp q b).2).1
  have hterm := fun q => GlobalTheory.T.shortSeries_bound_coprime_torsion_mul D.host.E H Dw d.l₂ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he'
    hch ℓ hℓ hu Λ N d.l₂.M hU hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi (hN2 q) (hF q) hrat (hcop q) (d.eF s) hsA
  have hX1 : ∀ {J : Type} (bb : T'.Fr) (X : J → T'.Fr) (ρ : ℝ),
      (∀ q, ((-ρ : ℝ) : EReal) ≤ nval T'.V (r * e) (bb * X q)) →
      ∀ q, ((-ρ : ℝ) : EReal) ≤ nval T'.V (r * e) (io₂ (nrm Dw d.c₂ w (α : 𝓞 D.host.E)) * bb * X q) := by
    intro J bb X ρ h q
    rw [hα1, Nat.cast_one, nrm_one, map_one, _root_.one_mul]
    exact h q
  have key := le_nval_avg (V := T'.V) (r * e) (fun q => io₂ (d.w x0 q)) _ ζ _
    ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) _ 1 one_pos hζ hu0 (by exact_mod_cast hc0)
    (fun q => map_isIntegral_int io₂ (hwi x0 q)) _ (hX1 _ _ _ hterm)
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
      rw [Nat.cast_pow, vV_pow (Nat.cast_ne_zero.2 (hP₀ ▸ hP0)), Int.cast_mul, Int.cast_natCast] at h
      rw [hP₀]
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovIntNum

section Size

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem sum_abs_laOf (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H) :
    ∑ k, |((laOf Dw a n τ k : ℤ) : ℝ)| =
      ((∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)) + ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ)) +
        ((Dw.p + Dw.q : ℕ) : ℝ) * ((n / 2 : ℕ) : ℝ) := by
  rw [Fin.sum_univ_add]
  have h1 : ∀ i : Fin Dw.p, |((laOf Dw a n τ (Fin.castAdd Dw.q i) : ℤ) : ℝ)| = (a (τ.1, i) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
    intro i
    have hi : ((Fin.castAdd Dw.q i : Fin (Dw.p + Dw.q)) : ℕ) < Dw.p := by simp
    unfold laOf GlobalTheory.AllWt.weightOf
    rw [if_pos hi, Fin.val_castAdd]
    simp only [Int.cast_add, Int.cast_natCast]
    exact abs_of_nonneg (by positivity)
  have h2 : ∀ i : Fin Dw.q, |((laOf Dw a n τ (Fin.natAdd Dw.p i) : ℤ) : ℝ)| =
      (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
    intro i
    have hi : ¬ ((Fin.natAdd Dw.p i : Fin (Dw.p + Dw.q)) : ℕ) < Dw.p := by simp
    have hidx : Dw.q - 1 - (((Fin.natAdd Dw.p i : Fin (Dw.p + Dw.q)) : ℕ) - Dw.p) = (Fin.rev i : ℕ) := by
      simp only [Fin.val_natAdd, Fin.val_rev]; omega
    unfold laOf GlobalTheory.AllWt.weightOf
    rw [if_neg hi, hidx]
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast]
    have h3 : (0 : ℝ) ≤ (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_of_nonpos (by linarith)]
    ring
  simp only [h1, h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hr : (∑ i : Fin Dw.q, (a (conjEmb τ.1, (Fin.rev i : ℕ)) : ℝ)) = ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ) :=
    Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)
  rw [hr]
  push_cast
  ring

theorem DF_eq_sum (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) :
    (DF Dw a : ℝ) = ∑ τ : Psi H, ((∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)) + ∑ i : Fin Dw.q, (a (conjEmb τ.1, i) : ℝ)) := by
  classical
  let P : (E →+* ℂ) → Prop := fun τ => τ (H.rt : E) = H.rt0
  have h := Fintype.sum_subtype_add_sum_subtype P (fun τ => ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ))
  beta_reduce at h
  have e1 : (∑ τ : {τ // P τ}, ∑ i : Fin (Dw.mult τ.1), (a (τ.1, i) : ℝ)) =
      ∑ τ : {τ // P τ}, ∑ i : Fin Dw.p, (a (τ.1, i) : ℝ) := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)), Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)),
      Datum.mult, if_pos τ.2]
  let e : {τ : E →+* ℂ // ¬ P τ} ≃ {τ // P τ} :=
    { toFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
      invFun := fun σ => ⟨conjEmb σ.1, GlobalTheory.AllWt.conj_not_mem (H := H) σ⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
      right_inv := fun σ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  have e2 : (∑ τ : {τ // ¬ P τ}, ∑ i : Fin (Dw.mult τ.1), (a (τ.1, i) : ℝ)) =
      ∑ σ : {τ // P τ}, ∑ i : Fin Dw.q, (a (conjEmb σ.1, i) : ℝ) := by
    refine Fintype.sum_equiv e _ _ fun τ => ?_
    show _ = ∑ i : Fin Dw.q, (a (conjEmb (conjEmb τ.1), i) : ℝ)
    rw [GlobalTheory.AllWt.conjEmb_conjEmb, Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)),
      Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)), Datum.mult, if_neg τ.2]
  unfold DF
  push_cast
  calc (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) = _ := h.symm
    _ = (∑ τ : {τ // P τ}, ∑ i : Fin Dw.p, (a (τ.1, i) : ℝ)) +
          ∑ σ : {τ // P τ}, ∑ i : Fin Dw.q, (a (conjEmb σ.1, i) : ℝ) := by
        convert congrArg₂ (· + ·) e1 e2 using 2 <;> first | rfl | exact Finset.sum_congr (congrArg _ (Subsingleton.elim _ _)) fun _ _ => rfl | congr 1
    _ = _ := by
        rw [← Finset.sum_add_distrib]

theorem sizeK_eq (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    sizeK Dw a n = (DF Dw a : ℝ) + (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) * ((n / 2 : ℕ) : ℝ) := by
  unfold sizeK
  simp only [sum_abs_laOf, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [DF_eq_sum, Finset.sum_add_distrib]
  ring

end Size

end GlobalTheory.CovIntNum

namespace GlobalTheory.CovIntNum

theorem intZ_log_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n →
    0 < intZ D (T.Q.Dw j) Y.d.l₂ n a ∧
    Real.log (intZ D (T.Q.Dw j) Y.d.l₂ n a) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n := by
  refine ⟨67, by norm_num, ?_⟩
  intro D T j Y e o Lb a n h
  obtain ⟨-, -, -, -, -, -, hLb, hM, hsz, -, -, -, hn, -, -, -⟩ := h
  obtain ⟨hqp, hdp, hq8, hd16, -⟩ := D.host.hyp
  have hM3 : 3 ≤ Y.d.l₂.M := Y.d.l₂.three_le
  have hZ : (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) =
      (Y.d.l₂.M : ℝ) ^ (Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n + DF (T.Q.Dw j) a) *
        ((NumberField.discr D.host.E).natAbs : ℝ) ^ DF (T.Q.Dw j) a := by
    rw [intZ_eq]
    push_cast [-Nat.cast_natAbs]
    ring
  have hD1 : (1 : ℝ) ≤ ((NumberField.discr D.host.E).natAbs : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero D.host.E))
  have hlD : Real.log ((NumberField.discr D.host.E).natAbs : ℝ) ≤ D.R.f * (7 * Lb) := by
    have h1 := log_discr_natAbs_le D.host.E
    have h2 : (Module.finrank ℚ D.host.E : ℝ) = 2 * D.R.f := by exact_mod_cast D.host.finrank_E'
    have h3 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    rw [h2] at h1
    nlinarith
  have hMpos : (0 : ℝ) < Y.d.l₂.M := by exact_mod_cast (by omega : 0 < Y.d.l₂.M)
  have hq0 : (0 : ℝ) < D.host.q := by exact_mod_cast hqp.pos
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast hdp.pos
  have hZpos : (0 : ℝ) < (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) := by rw [hZ]; positivity
  refine ⟨by exact_mod_cast hZpos, ?_⟩
  have hlogZ : Real.log (intZ D (T.Q.Dw j) Y.d.l₂ n a : ℝ) =
      ((Module.finrank ℚ D.host.E / 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) * n + DF (T.Q.Dw j) a : ℕ) : ℝ) *
          Real.log Y.d.l₂.M +
        (DF (T.Q.Dw j) a : ℝ) * Real.log ((NumberField.discr D.host.E).natAbs : ℝ) := by
    rw [hZ, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  rw [hlogZ]

  have hSe := sizeK_eq (T.Q.Dw j) a n
  have hcard : Fintype.card (Psi T.Q.H) = Module.finrank ℚ D.host.E / 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GlobalTheory.LamF.card_psiSet T.Q.H
  rw [hcard] at hSe
  have hlD0 := Real.log_nonneg hD1
  generalize Real.log ((NumberField.discr D.host.E).natAbs : ℝ) = lD at hlD hlD0 ⊢
  obtain ⟨t, rfl⟩ := hn
  have ht : (t + t) / 2 = t := by omega
  rw [ht] at hSe
  generalize Module.finrank ℚ D.host.E / 2 = m at hSe ⊢
  generalize sizeK (T.Q.Dw j) a (t + t) = S at hSe ⊢
  generalize DF (T.Q.Dw j) a = dF at hSe ⊢
  push_cast at hSe ⊢

  have hf : 1 ≤ D.R.f := by have : 0 < D.R.n := D.R.ord_pos; unfold Formalism.BasicNotions.Ranks.f; omega
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Formalism.BasicNotions.Ranks.r; omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hlM0 : 0 ≤ Real.log Y.d.l₂.M := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Y.d.l₂.M))
  have hdF0 : (0 : ℝ) ≤ dF := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ (m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * t := by positivity
  have hS0 : 0 ≤ S := by rw [hSe]; positivity
  have hX : (m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * ((t : ℝ) + t) + dF ≤ 2 * S := by rw [hSe]; linarith
  have hdFS : (dF : ℝ) ≤ S := by rw [hSe]; linarith
  have h1 : ((m : ℝ) * (((T.Q.Dw j).p : ℝ) + (T.Q.Dw j).q) * ((t : ℝ) + t) + dF) * Real.log Y.d.l₂.M ≤
      (2 * S) * (30 * Lb) := mul_le_mul hX hM hlM0 (by linarith)
  have h2 : (dF : ℝ) * lD ≤ (D.R.f * S) * (7 * Lb) :=
    (mul_le_mul hdFS hlD hlD0 hS0).trans (le_of_eq (by ring))
  have hLS : 0 ≤ Lb * S := mul_nonneg (by linarith) hS0
  have hA : Lb * S ≤ D.R.f * (Lb * S) := le_mul_of_one_le_left hLS hf1
  have h3 : (2 * S) * (30 * Lb) + (D.R.f * S) * (7 * Lb) ≤ 67 * ((D.R.f : ℝ) * Lb) * S := by linarith
  have hx1 : (1 : ℝ) ≤ D.R.f * D.R.r * Lb :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hr1) hLb
  have h5 : (D.R.f : ℝ) * Lb ≤ D.R.f * D.R.r * Lb :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hr1) (by linarith)
  have h4 : (D.R.f : ℝ) * Lb ≤ ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := h5.trans (le_self_pow₀ hx1 (by norm_num))
  have h6 : 67 * ((D.R.f : ℝ) * Lb) * S ≤ 67 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * S :=
    mul_le_mul_of_nonneg_right (by linarith) hS0
  linarith

end GlobalTheory.CovIntNum
end
end
