module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle354
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle188
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle371
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle177
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle373
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle365
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle368
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle342
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ReadsMove
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle422
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle364
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle374
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle325
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle321
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle361
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle552
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedOfCover
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle704
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle580
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle250
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle317
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle022
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Mathlib.Topology.Connected.Separation

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc.AwayId

theorem key {K : Type} [Field K] {P M C : K} (hP : P ≠ 0) (hM : M ≠ 0) (hC : C ≠ 0) (V A A' n n' : ℤ) :
    P ^ (V * (n - n')) * (M ^ n' * (M ^ n)⁻¹ * (C ^ n) ^ (-A) * (C ^ n') ^ A') * (P ^ (-V) * (M * C ^ A)) ^ n *
      (P ^ V * (M⁻¹ * C ^ (-A'))) ^ n' = 1 := by
  simp only [mul_zpow, ← zpow_mul, inv_zpow', mul_sub, zpow_sub₀ hP, neg_mul, zpow_neg]
  rw [mul_comm A n, mul_comm A' n', mul_comm V n, mul_comm V n']
  field_simp

theorem map_zpow_of {G M : Type*} [Group G] [DivisionMonoid M] (f : G → M) (U : Subgroup G) (h1 : f 1 = 1)
    (hm : ∀ x ∈ U, ∀ y ∈ U, f (x * y) = f x * f y) {x : G} (hx : x ∈ U) (n : ℤ) : f (x ^ n) = f x ^ n := by
  let φ : U →* M := { toFun := fun y => f y, map_one' := h1, map_mul' := fun y z => hm _ y.2 _ z.2 }
  have := map_zpow φ ⟨x, hx⟩ n
  simpa [φ] using this

theorem lamC_mul' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  rw [lamC_eq_of_mem lam hx, lamC_eq_of_mem lam hy, lamC_eq_of_mem lam (mul_mem hx hy), ← map_mul]
  rfl

theorem lamC_zpow' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (n : ℤ) :
    TaylorLogMetric.lamC lam (x ^ n) = TaylorLogMetric.lamC lam x ^ n := by
  rw [lamC_eq_of_mem lam hx, lamC_eq_of_mem lam (zpow_mem hx n), ← map_zpow₀]
  rfl

theorem lamC_inv' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x⁻¹ = (TaylorLogMetric.lamC lam x)⁻¹ := by
  rw [lamC_eq_of_mem lam hx, lamC_eq_of_mem lam (inv_mem hx), ← map_inv₀]
  rfl

theorem lamC_ne_zero' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (h0 : x ≠ 0) :
    TaylorLogMetric.lamC lam x ≠ 0 := by
  rw [lamC_eq_of_mem lam hx]
  exact (map_ne_zero lam).2 fun h => h0 (congrArg Subtype.val h)

theorem final {K : Type} [Field K] {P M C Q s : K} (hP : P ≠ 0) (hM : M ≠ 0) (hC : C ≠ 0) (V A A' la la' n n' : ℤ) :
    Q * P ^ (V * (n - n')) * (s * (M ^ n' * (M ^ n)⁻¹ * (C ^ n) ^ (-A) * (C ^ n') ^ A')) *
        ((P ^ (-V) * (M * C ^ A)) ^ (la + n) * (P ^ V * (M⁻¹ * C ^ (-A'))) ^ (la' + n')) =
      Q * s * ((P ^ (-V) * (M * C ^ A)) ^ la * (P ^ V * (M⁻¹ * C ^ (-A'))) ^ la') := by
  have hXa : P ^ (-V) * (M * C ^ A) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hP) (mul_ne_zero hM (zpow_ne_zero _ hC))
  have hXb : P ^ V * (M⁻¹ * C ^ (-A')) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hP) (mul_ne_zero (inv_ne_zero hM) (zpow_ne_zero _ hC))
  have hk := key hP hM hC V A A' n n'
  rw [zpow_add₀ hXa, zpow_add₀ hXb]
  calc _ = Q * s * ((P ^ (-V) * (M * C ^ A)) ^ la * (P ^ V * (M⁻¹ * C ^ (-A'))) ^ la') *
        (P ^ (V * (n - n')) * (M ^ n' * (M ^ n)⁻¹ * (C ^ n) ^ (-A) * (C ^ n') ^ A') * (P ^ (-V) * (M * C ^ A)) ^ n *
          (P ^ V * (M⁻¹ * C ^ (-A'))) ^ n') := by ring
    _ = _ := by rw [hk, mul_one]



theorem scal_away : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pair → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, ∀ a b : (sysS H X std).G.Kf, S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) → S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)))) → ∀ (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.pPow (sysS H X std) j La La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La') * S.E.iK (a ^ len (sysS H X std) v j Lb.2 * b ^ len (sysS H X std) v (j + 1) Lb'.2) = GlobalTheory.TwU.pPow (sysS H X std) j Lb Lb' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb') * S.E.iK (a ^ len (sysS H X std) v j La.2 * b ^ len (sysS H X std) v (j + 1) La'.2)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hSpl hP v π hπ j hj a b ha hb La Lb La' Lb' hab hab'
  have hR := GlobalTheory.TwV.DelB.sysS_ranks S
  have hjle : j ≤ D.R.m := hj.le
  have hj1 : j + 1 ≤ D.R.m := hj
  have hjm : j < (sysS H X std).mm := hR.1 ▸ hj
  have hPa := hP j hjm La La' hab.1 hab'.1
  have hPb := hP j hjm Lb Lb' hab.2.1 hab'.2.1
  obtain ⟨k, hkU, hkI, hkO, hk⟩ := GlobalTheory.T.det_latticeTuples_agreeing_away_from_place S hD hSpl v π hπ j hjle La Lb hab
  obtain ⟨k', hkU', hkI', hkO', hk'⟩ := GlobalTheory.T.det_latticeTuples_agreeing_away_from_place S hD hSpl v π hπ (j + 1) hj1 La' Lb' hab'
  obtain ⟨c0, hc0⟩ := GlobalTheory.T.kernelLattice_detIdeal_character_eq_const_mul_det S hD hSpl j hjle
  obtain ⟨c0', hc0'⟩ := GlobalTheory.T.kernelLattice_detIdeal_character_eq_const_mul_det S hD hSpl (j + 1) hj1
  obtain ⟨-, hsl⟩ := GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hSpl v j hjle La Lb hab
  obtain ⟨-, hsl'⟩ := GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hSpl v (j + 1) hj1 La' Lb' hab'
  obtain ⟨hχm, hχ1, -, hχN⟩ := GlobalTheory.T.charOnNormOneIdeles_mul_unramified_classValue S hD hSpl
  have hbad := (GlobalTheory.T.level_badPrimes_coprime_residueChar S hD hSpl).2.2.2
  have hdtb := (GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hSpl j hjle Lb hab.2.1).1
  have hdtb' := (GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hSpl (j + 1) hj1 Lb' hab'.2.1).1
  have law := S.law
  have hmuk : ∀ κ ∈ U1 (sigD D), κ ∈ intU D.host.F D.host.E → OneOff ((A0 J).pl v).1 κ → S.muT (j + 1) κ = 1 := by
    intro κ hκ hκI hκO
    refine law.mu_unr j hj κ hκ hκI fun v' hv' => hκO v' fun h => hbad v' hv' ?_
    rw [h]
    exact ((A0 J).pl v).2

  have hmuF : ∀ x ∈ U1 (sigD D), ∀ (e : ℤ) (κ : (AfE D.host.F D.host.E)ˣ), κ ∈ U1 (sigD D) → S.muT (j + 1) κ = 1 →
      S.muT (j + 1) (x * π ^ e * κ) = S.muT (j + 1) x * S.muT (j + 1) π ^ e := by
    intro x hx e κ hκ h1
    have hpe : π ^ e ∈ U1 (sigD D) := zpow_mem hπ.1 e
    rw [(law.mu_mul j hj).2 _ (mul_mem hx hpe) _ hκ, h1, mul_one, (law.mu_mul j hj).2 _ hx _ hpe,
      map_zpow_of (S.muT (j + 1)) (U1 (sigD D)) (law.mu_mul j hj).1 (law.mu_mul j hj).2 hπ.1 e]
  have hchi1 : chiI J 1 = 1 := hχ1 1 (one_mem _) (one_mem _)
  have hchF : ∀ x ∈ U1 (sigD D), ∀ (e : ℤ) (κ : (AfE D.host.F D.host.E)ˣ), κ ∈ U1 (sigD D) → κ ∈ intU D.host.F D.host.E →
      chiI J (x * π ^ e * κ) = chiI J x * chiI J π ^ e := by
    intro x hx e κ hκ hκI
    have hpe : π ^ e ∈ U1 (sigD D) := zpow_mem hπ.1 e
    rw [hχm _ (mul_mem hx hpe) _ hκ, hχ1 κ hκ hκI, mul_one, hχm _ hx _ hpe, map_zpow_of (chiI J) (U1 (sigD D)) hchi1 hχm hπ.1 e]
  have hscal : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' =
      GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb' *
        (S.muT (j + 1) π ^ (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2) *
          (S.muT (j + 1) π ^ (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2))⁻¹ *
          (chiI J π ^ (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2)) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
          (chiI J π ^ (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2)) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) := by
    unfold GlobalTheory.TwU.scal0
    rw [hc0 La hab.1 hPa.1.2.2.1, hc0 Lb hab.2.1 hPb.1.2.2.1, hc0' La' hab'.1 hPa.1.2.2.2, hc0' Lb' hab'.2.1 hPb.1.2.2.2, hk, hk',
      hmuF _ hdtb _ k hkU (hmuk k hkU hkI hkO), hmuF _ hdtb' _ k' hkU' (hmuk k' hkU' hkI' hkO'),
      hchF _ hdtb _ k hkU hkI, hchF _ hdtb' _ k' hkU' hkI']
    simp only [mul_zpow, mul_inv]
    ring

  have hp0 : ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hpp : GlobalTheory.TwU.pPow (sysS H X std) j La La' = GlobalTheory.TwU.pPow (sysS H X std) j Lb Lb' *
      ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1) *
        ((len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2) -
          (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2))) := by
    unfold GlobalTheory.TwU.pPow
    rw [← zpow_add₀ hp0]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    have he : ∀ v' ∈ Finset.univ.erase v, (sysS H X std).vm v' (j + 1) * (len (sysS H X std) v' (j + 1) La'.2 - len (sysS H X std) v' j La.2) =
        (sysS H X std).vm v' (j + 1) * (len (sysS H X std) v' (j + 1) Lb'.2 - len (sysS H X std) v' j Lb.2) := by
      intro v' hv'
      rw [hsl v' (Finset.ne_of_mem_erase hv'), hsl' v' (Finset.ne_of_mem_erase hv')]
    rw [Finset.sum_congr rfl he]
    ring

  have hm_alg : S.muT (j + 1) π ∈ TaylorLogMetric.Qbar := law.mu_alg j hj π hπ.1
  have hm_ne : S.muT (j + 1) π ≠ 0 := law.mu_ne hj hπ.1
  obtain ⟨𝔞, hN1, hc𝔞⟩ := hχN π hπ.1
  have hgx := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  have hcu := GlobalTheory.TwV.Xc.chi_alg_unit_inert D _ S.lam t.χ t.χ_ok (by omega) hgx.2.1 𝔞 hN1
  have hc_alg : chiI J π ∈ TaylorLogMetric.Qbar := hc𝔞 ▸ hcu.1
  have hc_ne : chiI J π ≠ 0 := hc𝔞 ▸ hcu.2.1
  have hsb : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb' ∈ TaylorLogMetric.Qbar := hPb.2.2.2.2.1
  have hLm := lamC_ne_zero' S.lam hm_alg hm_ne
  have hLc := lamC_ne_zero' S.lam hc_alg hc_ne
  have hma := fun (e : ℤ) => zpow_mem hm_alg e
  have hca := fun (e : ℤ) => zpow_mem hc_alg e
  rw [lamC_mul' S.lam hm_alg (hca _), lamC_zpow' S.lam hc_alg] at ha
  rw [lamC_mul' S.lam (inv_mem hm_alg) (hca _), lamC_inv' S.lam hm_alg, lamC_zpow' S.lam hc_alg] at hb
  rw [hpp, hscal, lamC_mul' S.lam hsb (mul_mem (mul_mem (mul_mem (hma _) (inv_mem (hma _))) (zpow_mem (hca _) _)) (zpow_mem (hca _) _)),
    lamC_mul' S.lam (mul_mem (mul_mem (hma _) (inv_mem (hma _))) (zpow_mem (hca _) _)) (zpow_mem (hca _) _),
    lamC_mul' S.lam (mul_mem (hma _) (inv_mem (hma _))) (zpow_mem (hca _) _),
    lamC_mul' S.lam (hma _) (inv_mem (hma _)), lamC_inv' S.lam (hma _),
    lamC_zpow' S.lam (hca _), lamC_zpow' S.lam (hca _), lamC_zpow' S.lam hm_alg, lamC_zpow' S.lam hm_alg,
    lamC_zpow' S.lam hc_alg, lamC_zpow' S.lam hc_alg,
    map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀, map_zpow₀, ha, hb]
  have e1 : len (sysS H X std) v j Lb.2 = len (sysS H X std) v j La.2 + (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2) := by ring
  have e2 : len (sysS H X std) v (j + 1) Lb'.2 = len (sysS H X std) v (j + 1) La'.2 +
      (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2) := by ring
  generalize len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2 = n at e1 ⊢
  generalize len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2 = n' at e2 ⊢
  rw [e1, e2]
  exact final hp0 hLm hLc _ _ _ _ _ _ _
end GlobalTheory.TwV.Xc.AwayId

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwU.AtTrue.StepZeroRead



theorem reads : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), ReadsOne I l Z u a 0 (Nat.zero_le _) (fun _ => ()) K0 ∧ (∀ β, (K0 β).lev.Lb = F.to0.cls0.lev.Lb ∧ (K0 β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ (K0 β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : (K0 β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → (K0 β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, ((K0 ((fun _ : (I.stp u a 0).Cl => ()) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  intro B X I hI hP l Z u Ch0 chOf0 F a Q hQ hF
  obtain ⟨k, hk⟩ := hF.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hk' : I.Reads u I.mu0 0 (fun _ => ()) (fun _ => F.to0.cls0.lev.Lb) (fun _ => F.to0.cls0.lev.U)
      (fun _ => F.to0.cls0.lev.chi) (fun c => (F.to0.cls0.y c).1) (fun c s => (F.to0.cls0.stabI c s).1) (fun _ => k ()) := hk
  choose κ hκ using GlobalTheory.T.memberRepresentative_moved_at_twist_eq_tupleFrames I hI hP l Z u F a Q hQ hF (k ()) hk'
  obtain ⟨K0, hLb, hUloc, hU, hchi, hy, hst⟩ :=
    GlobalTheory.T.stepZeroChart_of_memberLevel I hI hP l Z u a Q F.to0.cls0 κ (fun c s => hk'.stab c s)
  have nQ : ∀ v, ¬ I.UnderQ I.mu0 v := fun v ⟨P, hP', _⟩ => by
    rw [I.twistPrimes_reference_tuple_eq_empty] at hP'
    simp at hP'
  letI := StepZero.idxUnique (hI.idx_ok a)
  refine ⟨K0, ⟨fun _ => k (), ⟨?key, ?onto, ?lb, ?kstd, ?koff, ?kT, ?pt, ?lev, ?chr, ?stab⟩, ?off⟩, ?levs, ?ys⟩
  case key =>
    intro c c'
    exact ⟨fun _ => ⟨Subsingleton.elim _ _, Chart0.cos0 I _ _⟩, fun _ => rfl⟩
  case onto =>
    intro β
    obtain ⟨c0, -⟩ := hk'.onto ()
    exact ⟨I.eCls0 l u a c0, Subsingleton.elim _ _⟩
  case lb =>
    intro β x
    cases β
    rw [hLb]
    exact hk'.lb () x
  case kstd => exact fun _ => hk'.k_std ()
  case koff => exact fun _ v hT _ _ => hk'.k_off () v hT (nQ v) (Or.inl rfl)
  case kT => exact fun _ => hk'.k_T ()
  case pt =>
    intro c
    obtain ⟨c0, rfl⟩ := (I.eCls0 l u a).surjective c
    show PtOf ((show GA B (B.R.N 0) from ((K0 ()).y ⟨I.eCls0 l u a c0, rfl⟩).1) * k ()) _
    rw [hy c0]
    exact (hκ c0).2.2
  case lev =>
    intro c x q hq
    obtain ⟨c0, rfl⟩ := (I.eCls0 l u a).surjective c
    change PtOf ((show GA B (B.R.N 0) from ((K0 ()).y ⟨I.eCls0 l u a c0, rfl⟩).1) * x * k ()) q at hq
    rw [hy c0] at hq
    show x ∈ (K0 ()).lev.U ↔ _
    rw [hU]
    exact GlobalTheory.T.stepZero_level_readAsReference I hI hP l Z u a _ _ _ _ _ (k ()) hk' c0 (κ c0) _ rfl (hκ c0).2.2 x q hq
  case chr =>
    intro c x κ' hg hq
    obtain ⟨c0, rfl⟩ := (I.eCls0 l u a).surjective c
    change PtOf ((show GA B (B.R.N 0) from ((K0 ()).y ⟨I.eCls0 l u a c0, rfl⟩).1) * x.1 * k ()) _ at hq
    rw [hy c0] at hq
    let x' : F.to0.cls0.lev.U := ⟨x.1, hU ▸ x.2⟩
    show (((K0 ()).lev.chi x : ℂˣ) : ℂ) = _
    rw [hchi x x' rfl]
    exact GlobalTheory.T.stepZero_levelCharacter_eq_referenceTuple I hI hP l Z u a _ _ _ _ _ (k ()) hk' c0 (κ c0) _ rfl (hκ c0).2.2 (hκ c0).2.1 x' κ' hg hq
  case stab => exact fun c s => hst ⟨c, rfl⟩ s
  case off => exact fun _ v hT => hk'.k_off () v hT (nQ v) (Or.inl rfl)
  case levs => exact fun β => by cases β; exact ⟨hLb, hUloc, hU, hchi⟩
  case ys => exact fun c => ⟨κ c, hy c, (hκ c).2.1, (hκ c).1⟩

end GlobalTheory.TwU.AtTrue.StepZeroRead

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
namespace GlobalTheory.LocMod.SpanModels

theorem mem_iSup_range_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ f, Formalism.IndefR.Datum.IsThetaFunO ψ S T f → f ∈ ⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix Y Y' k) →ₗ[ℂ] (Formalism.IndefR.Datum.WO S T → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm := by
  intro D k _ _ _ _ p Y Y' _ _ _ _ S T FS FT ψ hψ f hf
  classical
  obtain ⟨U, hUo, hUf⟩ := hf.level
  obtain ⟨c, hc, L', K, hL, hL'e, hK, ⟨R, hR⟩, hL'K, hsep⟩ := GlobalTheory.T.exists_split_rescaled_lattice_and_dual D k p Y Y' S T FS FT ψ hψ U hUo
  have hinf : Formalism.L2.Theta.infPart D p.e = 0 := GlobalTheory.PlaceCoord.infPart_split p.split
  have hinf' : Formalism.L2.Theta.infPart D (Formalism.L2.Theta.cA D p.e) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hec : p.e * Formalism.L2.Theta.cA D p.e = 0 := p.split.2.1
  let I : AddSubgroup (Matrix Y Y' k) :=
    { carrier := {x | ∀ i j, x i j ∈ 𝒪[k]}
      add_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)
      zero_mem' := fun i j => zero_mem _
      neg_mem' := fun ha i j => neg_mem (ha i j) }
  let L : AddSubgroup (Formalism.IndefR.Datum.WO S T) :=
    I.map ((Witness.upH p FS FT).comp (DistribSMul.toAddMonoidHom (Matrix Y Y' k) c))
  have memL : ∀ t, t ∈ L ↔ ∃ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) ∧ p.up FS FT (c • x) = t := fun t => Iff.rfl
  let W : Submodule ℂ (Formalism.IndefR.Datum.WO S T → ℂ) :=
    { carrier := {g | Formalism.IndefR.Datum.IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.LocMod.LinSpace.isThetaFunO_add ha hb
      zero_mem' := GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T
      smul_mem' := fun c _ hg => GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c hg }
  have key := GlobalTheory.T.mem_span_translates_of_fixed_lattice (fun x y => ψ (Formalism.IndefR.Datum.symplO S T x y)) (isBichar_symplO S T ψ) (heisL S T ψ)
    (half S T p.e) (half S T (Formalism.L2.Theta.cA D p.e)) L L' K
    (by rintro _ ⟨x, hx, rfl⟩; exact (hL x hx).1)
    (fun t ht => (isHalf_iff S T).1 (hL'e t ht))
    (fun y hy => (isHalf_iff S T).1 (hK y hy).1)
    (fun v => by
      funext w
      change ψ (Formalism.IndefR.Datum.symplOH S T w 0) * v (w + 0) = v w
      simp [Formalism.IndefR.Datum.symplOH, symplO_zero_right])
    (fun x hx x' hx' v => heisL_half S T ψ (by rw [mul_comm]; exact hec) x hx x' hx' v)
    (fun y hy y' hy' v => heisL_half S T ψ (by rw [Formalism.L2.Theta.cA_cA, hec]) y hy y' hy' v)
    (fun x _ y _ v => heisL_comm S T ψ x y v)
    ⟨R, fun t ht => by
      obtain ⟨r, hr, x, hx, e⟩ := hR t ht
      exact ⟨r, hr, x, hx, e.symm⟩⟩
    hL'K (fun y hy h => hsep y ((isHalf_iff S T).2 hy) h) W
    (fun v hv x _ => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv x)
    (fun v hv y _ => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hv y)
    f hf
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact hUf _ (hL x hx).2 (GlobalTheory.PlaceDatum.infPart_of_half hinf (Witness.up_half p FS FT _)))
    (fun y hy => hUf y (hK y hy).2 (GlobalTheory.PlaceDatum.infPart_of_half hinf' (hK y hy).1))
  refine Submodule.span_le.2 ?_ key
  rintro _ ⟨r, hr, g, hg, hgL, hgY, rfl⟩
  exact GlobalTheory.T.heisenbergOperator_fixedVector_mem_localModelImage D k p Y Y' S T FS FT ψ hψ c hc g hg (fun x hx => hgL _ ⟨x, hx, rfl⟩)
    (fun y hy hyL => hgY y ((isHalf_iff S T).1 hy) (by rintro _ ⟨x, hx, rfl⟩; exact hyL x hx)) r ((isHalf_iff S T).2 hr)

end GlobalTheory.LocMod.SpanModels
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

noncomputable section

namespace GlobalTheory.LimitTop

open Matrix Formalism.WeaklyAdmissibleFiltrations

theorem closedAtL : ClosedAtL := by
  intro E Ω _ _ _ _ _ l _ a ha P AI hT w A hA O _ _ _ Bw hBw J r hr hss C hC hρ
  classical
  obtain ⟨T⟩ := hT

  let jl : ↥(GK Bw.Kw) →* Formalism.ConjugateSelfDual.G E Ω := (ReciprocityTheory.Gal.Dec (F := E) A).subtype.comp Bw.e.symm.toMonoidHom
  have hjl : Continuous jl := continuous_subtype_val.comp Bw.e_symm_cont

  let jE : E →+* ↥Bw.Kw.1 := (Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E
  let J' : (↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l) → Multiset ℤ := fun τ'' => J (τ''.toRingHom.comp jE)
  obtain ⟨Cv⟩ := GlobalTheory.TraceConjugationCover.cover_exists l (Formalism.ConjugateSelfDual.G E Ω) a Bw.LL r hr hss C (fun ρ hm => (hρ ρ hm).1) hC
  obtain ⟨Cv'⟩ := GlobalTheory.BKLim.cover_pull l (Formalism.ConjugateSelfDual.G E Ω) ↥(GK Bw.Kw) jl hjl a Bw.LL r C Cv

  have tr : ∀ (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)) (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)), Bw.LL.1 ≤ L.1 →
      (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = ((ρ.comp jl) g).val i k) →
      IsModel Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r'.comp Bw.e.toMonoidHom) ∧
        Bw.repE L (r'.comp Bw.e.toMonoidHom) = R := by
    intro ρ L r' R hle hR he
    refine ⟨⟨hle, ?_⟩, ?_⟩
    · ext g i k
      have := he (Bw.e g) i k
      simpa [jl, mapRep] using this
    · refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
      rw [hR]
      simp [LocBridge.repE, Matrix.toLin'_apply]

  have hCl : ∀ ρ₁ ∈ (fun ρ => ρ.comp jl) '' C, ∀ (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1)
      (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)), Bw.LL.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = (ρ₁ g).val i k) →
      IsSst P R ∧ ∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ), multV (P.PD Bw.Kw) R τ n = ((J' (L.1.val.comp τ)).count n : ℤ) := by
    rintro _ ⟨ρ, hm, rfl⟩ L r' R hle hR he
    obtain ⟨hmod, hrep⟩ := tr ρ L r' R hle hR he
    refine ⟨hrep ▸ GlobalTheory.SstModel.main l P AI ⟨T⟩ E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O Bw a _ L _ hmod (hρ ρ hm).2.1, fun τ n => ?_⟩
    have hi : IsInduced Bw ((L.1.val.comp τ).toRingHom.comp jE) τ := fun x => rfl
    have := IsJumpsAt.count_eq P hmod hi ((hρ ρ hm).2.2 _ L τ hi) n
    rw [← hrep]
    exact this.symm
  have hcr : (∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) → ∀ ρ₁ ∈ (fun ρ => ρ.comp jl) '' C,
      ∀ (L : FinExt l) (r' : ↥(GK Bw.Kw) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK Bw.Kw) (Fin a → ↥L.1)),
      Bw.LL.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) →
      (∀ g i k, (((r' g).val i k : ↥L.1) : Om l) = (ρ₁ g).val i k) → IsCrys (P.PD Bw.Kw) R := by
    intro hc
    rintro _ ⟨ρ, hm, rfl⟩ L r' R hle hR he
    obtain ⟨hmod, hrep⟩ := tr ρ L r' R hle hR he
    rw [← hrep]
    exact (hmod.isCrysAt_iff P).1 (hc ρ hm)

  have hcont : Continuous (fun g => (r g : Matrix (Fin a) (Fin a) (Om l))) := Units.continuous_val.comp hr
  have model : ∀ L₀ : FinExt l, ∃ (L : FinExt l) (r₁ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) ↥L.1), L₀.1 ≤ L.1 ∧ Bw.LL.1 ≤ L.1 ∧
      mapRep (algebraMap ↥L.1 (Om l)) r₁ = r := by
    intro L₀
    haveI := L₀.2
    haveI := Bw.LL.2
    obtain ⟨L, hL, hmem⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (Formalism.ConjugateSelfDual.G E Ω) a r hcont
      ⟨L₀.1 ⊔ Bw.LL.1, IntermediateField.finiteDimensional_sup _ _⟩
    obtain ⟨r₁, -, hr₁⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem r hcont L hmem
    exact ⟨L, r₁, le_sup_left.trans hL, le_sup_right.trans hL, hr₁⟩

  have top : ∀ (L : FinExt l) (r₁ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) ↥L.1), Bw.LL.1 ≤ L.1 → mapRep (algebraMap ↥L.1 (Om l)) r₁ = r →
      IsModel Bw (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
      Bw.IsdRE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) ∧
      (∀ (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (n : ℤ),
        Bw.multE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) τ n = ((J' (L.1.val.comp τ)).count n : ℤ)) ∧
      ((∀ ρ ∈ C, IsCrysAt P Bw (ρ.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) →
        Bw.IsCrysE P L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) := by
    intro L r₁ hle hr₁
    have hmod : IsModel Bw (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) :=
      ⟨hle, by rw [← hr₁]; rfl⟩
    obtain ⟨hdr, hmu, hcy⟩ := GlobalTheory.CovClose.closed_of_cover l Bw.Kw Bw.LL P AI T a ha Bw.LL_split (r.comp jl) _ Cv' J' hCl L
      (r₁.comp jl) (Bw.repE L (r₁.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype)) hle
      (fun g v => by simp [LocBridge.repE, jl, Matrix.toLin'_apply]) (fun g i k => by rw [← hr₁]; rfl)
    refine ⟨hmod, ?_, hmu, fun hc => hcy (hcr hc)⟩
    have h := hdr
    unfold Formalism.MainNotions.N.IsDR at h
    rw [Module.finrank_fin_fun] at h
    exact h
  refine ⟨⟨?_, fun τ LL' τ' hi => ?_⟩, fun hc => ?_⟩
  · obtain ⟨L, r₁, -, hle, hr₁⟩ := model Bw.LL
    obtain ⟨hmod, hdr, -, -⟩ := top L r₁ hle hr₁
    exact ⟨L, _, hmod, hdr⟩
  · obtain ⟨L, r₁, hL', hle, hr₁⟩ := model LL'
    obtain ⟨hmod, hdr, hmu, -⟩ := top L r₁ hle hr₁
    let τ'' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1 := (IntermediateField.inclusion hL').comp τ'
    have hi' : IsInduced Bw τ τ'' := fun x => hi x
    have hτ : (L.1.val.comp τ'').toRingHom.comp jE = τ := RingHom.ext fun x => (hi x).symm
    refine ⟨L, _, hmod, hdr, τ'', hi', fun n => ?_⟩
    rw [hmu τ'' n]
    show ((J τ).count n : ℤ) = ((J ((L.1.val.comp τ'').toRingHom.comp jE)).count n : ℤ)
    rw [hτ]
  · obtain ⟨L, r₁, -, hle, hr₁⟩ := model Bw.LL
    obtain ⟨hmod, -, -, hcy⟩ := top L r₁ hle hr₁
    exact ⟨L, _, hmod, hcy hc⟩

end GlobalTheory.LimitTop
end
end
