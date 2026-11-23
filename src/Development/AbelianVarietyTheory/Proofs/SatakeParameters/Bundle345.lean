module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle181
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle178
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle175
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle311
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle177
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle176
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle310
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle324
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle328
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle323
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle325
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.Bundle001
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.SharpRestriction.GrowthBounds.ChartComparison.Bundle002
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockRowSubstitutionPreservesComplexSpan
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.InertKernelTheory.SubBSplit

@[expose] public section

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc.MuLL

theorem hchar_eq_prod_val {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L)
    (T : Finset (HeightOneSpectrum (𝓞 L))) (b : Neutral.B1.Ideles L) (hb : Formalism.L2.Host.IsFinIdele b)
    (h1 : ∀ P, P ∉ T → (b : AdeleRing (𝓞 L) L).2 P = 1) (hu : ∀ P ∈ T, χ.UnrAt P) :
    ∃ n : HeightOneSpectrum (𝓞 L) → ℤ, χ.1 b = ∏ P ∈ T, χ.val P ^ n P :=
  GlobalTheory.T.heckeCharacter_finite_idele_eq_prod_values_zpow χ T b hb h1 hu

theorem transfer_eq_zero {F E F' E' : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E']
    (iE : E' ≃+* E) (iA : AfE F' E' ≃+* AfE F E) (hrat : ∀ x : E', iA (x ⊗ₜ[F'] 1) = iE x ⊗ₜ[F] 1)
    (hint : ∀ y, iA y ∈ RInt F E ↔ y ∈ RInt F' E')
    (ι : AfE F' E' ≃+* FiniteAdeleRing (𝓞 E') E') (hι : GlobalTheory.TwU.IsAdIso ι)
    (z : AfE F E) (ℓ D : ℕ) (hℓ : 0 < ℓ) (hD : 0 < D)
    (hz : ∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E)
    (P : HeightOneSpectrum (𝓞 E')) (hP : ((ℓ : ℕ) : 𝓞 E') ∈ P.asIdeal) :
    ι (iA.symm z) P = 0 :=
  GlobalTheory.T.finiteAdele_iso_component_zero_of_infinitely_divisible iE iA hrat hint ι hι z ℓ D hℓ hD hz P hP

theorem exists_div_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) (z : AfE F E) (hz : ∀ w', w' ≠ w → prV (E := E) w' z = 0)
    (ℓ : ℕ) (hℓ : ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal) :
    ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E :=
  GlobalTheory.T.exists_nat_mul_div_pow_mem_integral_finiteAdele w z hz ℓ hℓ

theorem exists_h90_oneOff_preimage_at_splitPlace {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F))
    (spl : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F)
    (hsig : ∀ x, spl (sigR σ (w.adicCompletion F) x) = swapR (w.adicCompletion F) (spl x))
    (π : (AfE F E)ˣ) (hπ : π ∈ U1 σ) (hoff : OneOff w π) :
    ∃ x : (AfE F E)ˣ, h90 σ x = π ∧ OneOff w x :=
  GlobalTheory.T.hilbert90_normOne_oneOff_at_split_place_forall σ w spl hsig π hπ hoff

theorem exists_nat_mem_coprime {E : Type} [Field E] [NumberField E] (p : ℕ) (hp : p.Prime)
    (P : HeightOneSpectrum (𝓞 E)) (hP : ((p : ℕ) : 𝓞 E) ∉ P.asIdeal) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ ((ℓ : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ Nat.Coprime ℓ p :=
  GlobalTheory.T.exists_natCast_coprime_mem_heightOneSpectrum p hp P hP

end GlobalTheory.TwV.Xc.MuLL

namespace GlobalTheory.TwV.Xc.MuLL

open GlobalTheory.TwU (IsAdIso exists_isAdIso)

theorem exists_unitaryOneFiniteAdelic_of_det_normOne (D : D7) (π : (AfE D.host.F D.host.E)ˣ) (hπ : π ∈ U1 (sigD D)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = π := by
  have hd' : (π : AfE D.host.F D.host.E) * sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) π = 1 := by
    have := congrArg Units.val hπ
    simpa [Formalism.L2.DIV.U1, Formalism.L2.DIV.conjId] using this
  refine ⟨⟨Units.map (Matrix.scalar (Fin 1) : AfE D.host.F D.host.E →+* _).toMonoidHom π, ?_⟩, ?_⟩
  · show cT _ _ * _ * _ = _
    ext a b
    fin_cases a; fin_cases b
    simp [cT, Matrix.mul_apply, sigD]
    rw [mul_comm]
    exact hd'
  · ext
    simp

end GlobalTheory.TwV.Xc.MuLL

namespace GlobalTheory.TwV.Xc.MuLL

open GlobalTheory.TwU (IsAdIso exists_isAdIso)

theorem natCast_not_mem_of_coprime {R : Type} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) (a b : ℕ) (hab : Nat.Coprime a b)
    (hb : ((b : ℕ) : R) ∈ I) : ((a : ℕ) : R) ∉ I := by
  intro ha
  obtain ⟨c, d, h⟩ := (Nat.isCoprime_iff_coprime.2 hab : IsCoprime (a : ℤ) (b : ℤ))
  have h' := congrArg (Int.cast : ℤ → R) h
  push_cast at h'
  apply hI
  rw [Ideal.eq_top_iff_one, ← h']
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)



theorem mu_mem_LL : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    KIn t → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, ∃ r : D.what₂.LL, D.what₂.embLL r = S.muT (j + 1) π) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hDict _hSpl hK v π hπ j hj
  have hpp : (D.what₂.places.resChar w).Prime := Fact.out
  have hpw0 : (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.F) ∈ ((A0 J).pl v).1.asIdeal := ((A0 J).pl v).2
  obtain ⟨x', hx'h, hx'off⟩ := exists_h90_oneOff_preimage_at_splitPlace (sigD D) ((A0 J).pl v).1 ((A0 J).spl v) (J.one.good.sig v) π hπ.1 hπ.2.1
  obtain ⟨y, hy⟩ := exists_unitaryOneFiniteAdelic_of_det_normOne D π hπ.1
  set x : (AfE t.X.F t.X.E)ˣ := Units.map J.A.iA.symm.toRingHom.toMonoidHom x' with hxdef
  have hxx : Units.map J.A.iA.toRingHom.toMonoidHom x = x' := by ext; simp [hxdef]
  have hq : J.A.q x = J.dtU y := J.pins.q_dt x y (by rw [hy, hxx, hx'h])
  have hmu : S.muT (j + 1) π = (((t.O u μ).mt (j + 1) (J.A.q x) : ℂˣ) : ℂ) := by
    rw [← hy, S.law.mu_read j hj y, hq]
  obtain ⟨ι, hι⟩ := exists_isAdIso t.X.F t.X.E
  set b : Neutral.B1.Ideles t.X.E := MulEquiv.prodUnits.symm (1, Units.map ι.toRingHom.toMonoidHom x) with hbdef
  have hb : Formalism.L2.Host.IsFinIdele b := fun _ => rfl
  have hmuTil := J.pins.muTil ι hι ⟨j, hj⟩ b x hb rfl

  have hfin : {P : HeightOneSpectrum (𝓞 t.X.E) | P.asIdeal ∣ Ideal.span {((D.what₂.places.resChar w : ℕ) : 𝓞 t.X.E)}}.Finite :=
    Ideal.finite_factors (by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hpp.ne_zero)
  set T := hfin.toFinset with hT
  have hmemT : ∀ P, P ∈ T ↔ ((D.what₂.places.resChar w : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
    intro P
    rw [hT, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have h1 : ∀ P, P ∉ T → (b : AdeleRing (𝓞 t.X.E) t.X.E).2 P = 1 := by
    intro P hP
    rw [hmemT] at hP
    obtain ⟨ℓ, hℓ0, hℓP, hcop⟩ := exists_nat_mem_coprime _ hpp P hP
    have hℓw : ((ℓ : ℕ) : 𝓞 D.host.F) ∉ ((A0 J).pl v).1.asIdeal :=
      natCast_not_mem_of_coprime _ ((A0 J).pl v).1.isPrime.ne_top ℓ _ hcop hpw0
    set z : AfE D.host.F D.host.E := (x' : AfE D.host.F D.host.E) - 1 with hzdef
    have hz : ∀ w', w' ≠ ((A0 J).pl v).1 → prV (E := D.host.E) w' z = 0 := by
      intro w' hw'
      rw [hzdef, map_sub, hx'off w' hw', map_one, sub_self]
    obtain ⟨Dd, hDd, hdiv⟩ := exists_div_int _ z hz ℓ hℓw
    have h0 := transfer_eq_zero t.seam.iE J.A.iA J.pins.iA_rat J.pins.iA_int ι hι z ℓ Dd hℓ0 hDd hdiv P hℓP
    have e1 : ((x : (AfE t.X.F t.X.E)ˣ) : AfE t.X.F t.X.E) = J.A.iA.symm z + 1 := by
      rw [hzdef, map_sub, map_one, sub_add_cancel]
      rfl
    have e2 : (b : AdeleRing (𝓞 t.X.E) t.X.E).2 = ι ((x : (AfE t.X.F t.X.E)ˣ) : AfE t.X.F t.X.E) := rfl
    rw [e2, e1, map_add (f := _), map_one]
    show ι (J.A.iA.symm z) P + 1 = 1
    rw [h0, zero_add]
  have hu : ∀ P ∈ T, (t.glob.mu0 ⟨j, hj⟩).UnrAt P := by
    intro P hP
    rw [hmemT] at hP
    refine (J.pins.mu0 ⟨j, hj⟩).unr P fun i hgi => ?_
    have hne : D.what₂.places.resChar w ≠ t.Pr.g i := by
      rw [t.g_rec i]
      exact (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.2 i
    have hcop : Nat.Coprime (t.Pr.g i) (D.what₂.places.resChar w) :=
      (Nat.coprime_primes (t.pr_ok.g_prime i) hpp).2 hne.symm
    exact natCast_not_mem_of_coprime _ P.isPrime.ne_top _ _ hcop hP hgi
  obtain ⟨n, hn⟩ := hchar_eq_prod_val (t.glob.mu0 ⟨j, hj⟩) T b hb h1 hu
  set kU : t.X.Kˣ := ∏ P ∈ T, t.Ch.muVal ⟨j, hj⟩ P ^ n P with hkU
  have hk : Units.map t.seam.σ₀.toMonoidHom kU = (t.glob.mu0 ⟨j, hj⟩).1 b := by
    rw [hn, hkU, map_prod]
    refine Finset.prod_congr rfl fun P hP => ?_
    rw [map_zpow]
    congr 1
    apply Units.ext
    rw [Units.coe_map, ← t.glob_σ]
    refine J.pins.ch.muVal ⟨j, hj⟩ P fun i hgi => ?_
    rw [hmemT] at hP
    have hne : D.what₂.places.resChar w ≠ t.Pr.g i := by
      rw [t.g_rec i]
      exact (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.2 i
    have hcop : Nat.Coprime (t.Pr.g i) (D.what₂.places.resChar w) :=
      (Nat.coprime_primes (t.pr_ok.g_prime i) hpp).2 hne.symm
    exact natCast_not_mem_of_coprime _ P.isPrime.ne_top _ _ hcop hP hgi
  rw [hmu]
  by_cases hμ : μ = D.what₂.mu0
  · obtain ⟨r, hr⟩ := hK (kU : t.X.K)
    refine ⟨r, ?_⟩
    rw [hr, (J.pins.ref hμ).2, hmuTil, ← hk]
    rfl
  · obtain ⟨ξ, hξ, hmt⟩ := J.pins.tw μ hμ rfl
    have e : (t.O u μ).mt (j + 1) = D.muTil (j + 1) * ξ := by
      rw [hmt u]
      exact if_pos (⟨by omega, by omega⟩ : 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m)
    obtain ⟨r, hr⟩ := hK ((kU : t.X.K) * ((t.tup μ : Chr t.X.F t.X.E t.X.K) x : t.X.K))
    refine ⟨r, ?_⟩
    rw [hr, e, MonoidHom.mul_apply, Units.val_mul, hmuTil, hξ x, ← hk, map_mul]
    rfl

end GlobalTheory.TwV.Xc.MuLL
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

open Matrix

section Gen

variable {E : Type} [Field E] {N : ℕ}

theorem toLE_eq_mulVec (γ : GL (Fin N) E) (x : Fin N → E) : toLE γ x = γ.1 *ᵥ x := rfl

theorem toStdCo_stdG_eq (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E) :
    ((toStdCo σ G co).trans (stdG σ G γ)).toLinearMap =
      ((toStdCo σ G co).trans (stdG σ G 1)).toLinearMap ∘ₗ Matrix.toLin' (co.1 * γ.1 * (co⁻¹).1) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (toLE co).surjective x
  have h1 : (co⁻¹ : GL (Fin N) E).1 * co.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (toLE (1 : GL (Fin N) E)) = LinearEquiv.refl E _ := by
    ext z : 1
    simp [toLE_eq_mulVec]
  have h3 : Matrix.toLin' (co.1 * γ.1 * (co⁻¹).1) (toLE co y) = toLE co (toLE γ y) := by
    rw [Matrix.toLin'_apply, toLE_eq_mulVec, toLE_eq_mulVec, toLE_eq_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc _ (co⁻¹).1, h1, Matrix.mul_one]
  rw [LinearMap.comp_apply, h3]
  simp [toStdCo, stdG, h2]

theorem det_toStdCo_stdG (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E) :
    (LinearMap.toMatrix' ((toStdCo σ G co).trans (stdG σ G γ)).toLinearMap).det =
      γ.1.det * (LinearMap.toMatrix' ((toStdCo σ G co).trans (stdG σ G 1)).toLinearMap).det := by
  rw [toStdCo_stdG_eq, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', Matrix.det_mul, Matrix.det_mul,
    Matrix.det_mul]
  have h : (co.1).det * ((co⁻¹ : GL (Fin N) E).1).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  calc _ = γ.1.det * ((co.1).det * ((co⁻¹ : GL (Fin N) E).1).det) *
        (LinearMap.toMatrix' ((toStdCo σ G co).trans (stdG σ G 1)).toLinearMap).det := by ring
    _ = _ := by rw [h, mul_one]

theorem det_cT (σ : E →+* E) (M : Matrix (Fin N) (Fin N) E) : (cT σ M).det = σ M.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]
  rfl

theorem det_norm_of_UJ (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E)
    (hco : cT σ co.1 * co.1 = G) (hγ : γ ∈ UJ σ G) : σ γ.1.det * γ.1.det = 1 := by
  have hγ' : cT σ γ.1 * G * γ.1 = G := hγ
  have hG : G.det ≠ 0 := by
    rw [← hco, Matrix.det_mul, det_cT]
    have hc : (co.1).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).mp co.isUnit |>.ne_zero
    exact mul_ne_zero ((map_ne_zero σ).mpr hc) hc
  have h := congrArg Matrix.det hγ'
  rw [Matrix.det_mul, Matrix.det_mul, det_cT] at h
  have h' : (σ γ.1.det * γ.1.det - 1) * G.det = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h0 | h0
  · exact sub_eq_zero.mp h0
  · exact absurd h0 hG

end Gen

end GlobalTheory.TwV.DelB

namespace GlobalTheory.TwV.DelB

theorem gMat_det : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ k (hk : k ≤ D.R.m), (gMat J k hk 1).det * D.host.conj (gMat J k hk 1).det = 1 ∧
      ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk),
        (gMat J k hk γ).det = γ.1.det * (gMat J k hk 1).det ∧ γ.1.det * D.host.conj γ.1.det = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S k hk
  have hs : ∀ y : D.host.E, (sigD D : D.host.E →+* D.host.E) y = D.host.conj y := fun y =>
    Formalism.BasicNotions.bridge_star_holds D.R D.host y
  have hco := J.pins.crd_orth k hk
  refine ⟨?_, fun γ hγ => ⟨?_, ?_⟩⟩
  · have h := GlobalTheory.TwV.cT_mul_self_toStdCo_stdG (sigD D : D.host.E →+* D.host.E) (gramN D k hk) (J.A.crd k hk) 1 hco
      (Subgroup.one_mem _)
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, det_cT, Matrix.det_one, hs] at h2
    rw [mul_comm]
    exact h2
  · exact det_toStdCo_stdG _ _ _ _
  · have h := det_norm_of_UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk) (J.A.crd k hk) γ hco hγ
    rw [hs, mul_comm] at h
    exact h

end GlobalTheory.TwV.DelB

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem pullbackScalar_ne_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std), ∀ j < D.R.m, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → d.sP S j La La' ≠ 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj La La' h1 h2
  have hj' : j + 1 ≤ D.R.m := hj
  have key := fun (i : ℕ) (hi : i ≤ D.R.m) (Lb : (sysS H X std).Lt i) (hLb : ((sysS H X std).Pj i).IsLatTup Lb.2) =>
    GlobalTheory.T.adelicCharacters_at_det_rational_isometry_rep_level J.A J.dtU J.a J.pins J.tie S.Xi S.muT S.law j hj i hi (clsAt X H i Lb.1 Lb.2) (J.pt std i hi Lb)
      (d.gam i hi Lb) (d.mem i hi Lb) (d.kap i hi Lb) (d.eq i hi Lb hLb)
  have n1 := (key j (Nat.le_of_succ_le hj') La h1).2.2
  have n2 := (key (j + 1) hj' La' h2).2.2
  simp only [Dec.sP, dif_pos hj', Dec.chi]
  exact div_ne_zero (mul_ne_zero n1 (Units.ne_zero _)) (mul_ne_zero n2 (Units.ne_zero _))

end GlobalTheory.TwV.DelB
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem Dec.eM_mul_star : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ (d : Dec J std) j La, d.eM j La * star (d.eM j La) = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j La
  unfold Dec.eM
  split_ifs with h
  · have hu := GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary J.A J.dtU J.a J.pins J.tie j h.1 (d.gam j h.1 La) (d.mem j h.1 La)
    have hc : (Fin.cast h.2 : Fin (((sysS H X std).Pj j).m + 1) → Fin (D.R.N j)) = ⇑(finCongr h.2) := rfl
    rw [hc, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose]
    have hu' : gMat J j h.1 (d.gam j h.1 La) * star (gMat J j h.1 (d.gam j h.1 La)) = 1 := hu
    rw [hu', Matrix.submatrix_one_equiv]
  · simp

end GlobalTheory.TwV.DelB
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem detId_stdL_heq (D : D7) {n n' : ℕ} (h : n = n') {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} (hL : HEq L L') :
    TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) L = TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n') L' := by
  subst h
  cases hL
  rfl

theorem chi_detId_kerN : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = (∏ τ, TaylorLogMetric.embT D τ (gMat J j hj (d.gam j hj La)).det)⁻¹ * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ∧ (∏ τ, TaylorLogMetric.embT D τ (gMat J j hj (d.gam j hj La)).det) ≠ 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d j hj La hLa
  obtain ⟨⟨hr, -⟩, -, hK, -⟩ := hD j hj La hLa
  have hlat := GlobalTheory.T.kernelLattice_translate_eq_image_classLattice J.A J.dtU J.a J.pins J.tie j hj (clsAt X H j La.1 La.2) (J.pt std j hj La)
    (d.gam j hj La) (d.mem j hj La) (d.kap j hj La) (d.eq j hj La hLa)
  have hU : gMat J j hj (d.gam j hj La) * star (gMat J j hj (d.gam j hj La)) = 1 :=
    GlobalTheory.T.rationalIsometry_orthonormal_matrix_unitary J.A J.dtU J.a J.pins J.tie j hj (d.gam j hj La) (d.mem j hj La)
  have hcl := GlobalTheory.T.determinantIdealCharacter_classLattice_eq J.A J.dtU J.a J.pins J.tie J.rel J.base j hj (clsAt X H j La.1 La.2)
  have hmv := GlobalTheory.T.char_determinantIdeal_unitary_smul_selfDual D t.χ t.χ_ok ((t.O u μ).lat j (clsAt X H j La.1 La.2)) (gMat J j hj (d.gam j hj La)) hU
  rw [t.O_lat] at hmv
  have h1 := detId_stdL_heq D hr hK
  refine ⟨?_, ?_⟩
  · rw [h1]
    have : latK D.sp (gramN D j hj) J.a (J.pt std j hj La).1 ((J.St j hj).K (J.chart std j hj La)).lev.Lb =
        SDLat.smulLat (gMat J j hj (d.gam j hj La)) (t.seam.lat ((t.rd u μ).N j (clsAt X H j La.1 La.2))) := hlat
    rw [this, hmv, hcl]
  · have hdet : (gMat J j hj (d.gam j hj La)).det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hU
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => (map_ne_zero (TaylorLogMetric.embT D τ)).mpr hdet

end GlobalTheory.TwV.DelB
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Proof.LocOfSite

section Step

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} {i : ℕ}
  {cmp : Type} [hcmp : Fintype cmp] {em : cmp → Lv.compS i}
  {Lb : Submodule (𝓞 D.host.E) (Fin (D.sp.X (i + 1)).rank → D.host.E)}
  {Uloc : ∀ v : HeightOneSpectrum (𝓞 D.host.F),
    Subgroup (GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F))}
  {ψ : awayG D.sp.cm.sig (D.sp.X (i + 1)).gram Uloc (D.what₂.places.resChar w) →* (D.gat u w hg).Oˣ}
  {eps : UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X (i + 1)).gram →* (D.gat u w hg).Oˣ}

theorem iw_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) (B0 : GL (Fin D.R.k) D.host.E) (v) :
    (locJ hi t B).iw v = (locAt X u w hg B0).iw v := rfl

theorem pl_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) (B0 : GL (Fin D.R.k) D.host.E) (v) :
    (locJ hi t B).pl v = (locAt X u w hg B0).pl v := rfl

theorem B_locJ (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) : (locJ hi t B).B = reGL (rankN D (i + 1) hi) _ B := rfl

theorem splAlg_locJ' (hi : i + 1 ≤ D.R.m) (t : GChartTie (X.g u w hg) Lv i em (D.sp.X (i + 1)).gram Lb Uloc ψ eps)
    (B : GL (Fin (D.sp.X (i + 1)).rank) D.host.E) : GlobalTheory.TwV.SplAlg (locJ hi t B) :=
  fun _ a => (X.g u w hg).spl_alg _ _ a

end Step

theorem splAlg_locAt {D : D7} (X : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (B0 : GL (Fin D.R.k) D.host.E) :
    GlobalTheory.TwV.SplAlg (locAt X u w hg B0) :=
  fun _ a => (X.g u w hg).spl_alg _ _ a



theorem loc_eq_step0 : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD g.herm u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t), (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).iw v = (lev0At g u w hg).A.iw v) ∧ (∀ j hj β v, (((Z.inTw Fl ht Gt).at' j hj).st.loc β).pl v = (lev0At g u w hg).A.pl v) ∧ (∀ j hj β β', (((Z.inTw Fl ht Gt).at' j hj).st.loc β).B = (((Z.inTw Fl ht Gt).at' j hj).st.loc β').B) ∧ (∀ j hj, ((Z.inTw Fl ht Gt).at' j hj).st.pos = Gt.gat_pos u w hg) ∧ (∀ j hj β, GlobalTheory.TwV.SplAlg (((Z.inTw Fl ht Gt).at' j hj).st.loc β)) ∧ GlobalTheory.TwV.SplAlg (lev0At g u w hg).A := by
  intro D Gt c g u w hg Tw μ Z Fl ht
  refine ⟨fun j hj β v => ?_, fun j hj β v => ?_, fun j hj β β' => ?_, fun j hj => rfl, fun j hj β => ?_,
    splAlg_locAt g.herm u w hg g.cmp.B⟩
  · exact iw_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B g.cmp.B v
  · exact pl_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B g.cmp.B v
  · exact (B_locJ (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B).trans
      (B_locJ (hcmp := (Z.loc Fl ht j hj).fin β') hj ((Z.loc Fl ht j hj).t β') (Z.loc Fl ht j hj).B).symm
  · exact splAlg_locJ' (hcmp := (Z.loc Fl ht j hj).fin β) hj ((Z.loc Fl ht j hj).t β) (Z.loc Fl ht j hj).B

end GlobalTheory.Proof.LocOfSite

end
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HP



theorem cmpJHyp_inTw_site : ∀ {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (Tw : TwForms D) (μ : D.what₂.Tup) (Z : SiteD X0 u w hg (Tw.fm u μ)) (Fl : Fills (D.gat u w hg)) (ht : Fl.t = D.R.t) (Gt : GatTies D) (T : ∀ u : D.what₂.Word, Forms0 D u) (c : LatCmp D), CmpTied D X0 T Gt c → FillTie Gt u w hg Fl → SiteGood Z → SiteRest Z c → CmpJHyp c (Z.inTw Fl ht Gt) := by
  intro D X0 u w hg Tw μ Z Fl ht Gt T c K hF G A
  refine HypTiesI.hyp (X0 := X0) ⟨ht, hF, fun j hj => ⟨Z.Fo j hj, Z.loc Fl ht j hj, rfl, ?_⟩⟩ K
  exact
    { frRat := Z.frRat Fl ht j hj
      sameU := Z.sameU Fl ht j hj
      hypT := hypTJ_site Z Fl ht G.siteGood_prime_torsion G.bad_p j hj
      bad_p := G.bad_p j hj
      std := A.std j hj
      psi := A.psi j hj
      chRat := A.chRat j hj
      hypC := hypTJC_site Z Fl ht G.siteGood_prime_torsion j hj
      ok := G.ok j hj
      siteGood_prime_torsion := G.siteGood_prime_torsion j hj
      Lb_eq := fun _ => (reL_symm (rankN D (j + 1) hj) _).symm }

end GlobalTheory.HP
end
end
