module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle023
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle718
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle186
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle024
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle662
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle722
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle719
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Mathlib.RingTheory.FiniteLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle720
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjDesc



theorem vals : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (x₀ : A.fam.amb.FL i (tup a)) (h : GA D (Vc D i)), ∃ x : VsV D i M.c'.F, (R.HV i (tup a)).e (jVx R i (tup a) x₀) (fin _ h) = M.c0' x := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC i Tp tup M hP a x₀ h
  obtain ⟨_, _, _, hT, hc⟩ := hP.lift.c0
  obtain ⟨x, hx⟩ := GlobalTheory.RationalValues.placeEx R i M.jL (inC M.c') (tup a) (fun _ : Unit => h) M.c0' hC.models.jV hT hc hC.lev
    hC.grp.chiW hC.fam.pl_onto hC.fam.muVal x₀
  exact ⟨x (), hx ()⟩



theorem c_inj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → Function.Injective c := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ i Tp tup M hP c hc
  obtain ⟨gramR, c0R, c0L, hFT, hC0⟩ := hP.lift.c0
  have hfield : (inC M.c').comp M.jL = D.what₂.embLL := hP.lift.field
  have hbas : ∀ j, c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) =
      c0L i (bVV D.what₂.LL (lamV D i) j) := fun j => by
    obtain ⟨v', hv', hcv'⟩ := hC0 (bVV D.what₂.LL (lamV D i) j)
    refine (hc v' _ ?_).trans hcv'
    rw [GlobalTheory.CoefModel.mapVV_coe, hv', MvPolynomial.map_map, hfield]
  have hli : LinearIndependent ℂ fun j => c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) := by
    have h := (hFT.mapL i).2.1
    simp only [← hbas] at h
    exact h
  have hli0 := GlobalTheory.CoefModel.linearIndependent_mapVV D.what₂.embLL (lamV D i)
  have hsp0 := GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (lamV D i)
  let B := Module.Basis.mk hli0 hsp0.ge
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hs := B.sum_repr z
  have h0 : ∑ j, B.repr z j • c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) = 0 := by
    calc _ = c (∑ j, B.repr z j • B j) := by

            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, Module.Basis.mk_apply]
      _ = 0 := by rw [hs, hz]
  have hc0 := Fintype.linearIndependent_iff.1 hli _ h0
  rw [← hs]
  exact Finset.sum_eq_zero fun j _ => by rw [hc0 j, zero_smul]



theorem conj_desc : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∀ a b : Tp, ConjTup R τ (tup a) (tup b) → ∀ (y : (R.HV i (tup a)).H) (y' : (R.HV i (tup b)).H), ConjForm R i τ c (tup a) (tup b) y y' → ∃ (n : ℕ) (α : Fin n → ℂ) (ys : Fin n → (R.HV i (tup a)).H) (ys' : Fin n → (R.HV i (tup b)).H), y = ∑ k, α k • ys k ∧ y' = ∑ k, τ (α k) • ys' k ∧ ∀ k (h : GA D (Vc D i)), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i (tup a)).e (ys k) (fin _ h) = M.c0' x ∧ (R.HV i (tup b)).e (ys' k) (fin _ h) = M.c0' x' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hFW i Tp tup M hP τ ta hta hFix c hc hxi a b hab y y' hy
  obtain ⟨φ, hφs, hφ⟩ := GlobalTheory.T.exists_galoisConj_definiteForms_semilinearEquiv D G Pl0 T0 A T R F κ v₀ hC hFW i Tp tup M hP c hc τ (tup a) (tup b) hFix hab
  have hy' : y' = φ y := (hφ y y').1 hy
  have hmem : y ∈ Submodule.span ℂ (Set.range (R.jV i (tup a))) := by
    rw [GlobalTheory.HeckeClassSums.span_jV hC.models.HV hC.models.jV i (tup a)]; exact Submodule.mem_top
  obtain ⟨n, α, g, hg⟩ := Submodule.mem_span_set'.1 hmem
  have hinj := c_inj D G Pl0 T0 A T R κ v₀ i Tp tup M hP c hc
  refine ⟨n, α, fun k => (g k : (R.HV i (tup a)).H), fun k => φ (g k : (R.HV i (tup a)).H), hg.symm, ?_, ?_⟩
  · subst hy' hg
    exact (map_sum φ _ _).trans (Finset.sum_congr rfl fun k _ => hφs _ _)
  · intro k h
    have hk : ∃ x₀ : A.fam.amb.FL i (tup a), R.jV i (tup a) x₀ = (g k : (R.HV i (tup a)).H) := (g k).2
    obtain ⟨x₀, hx₀⟩ := hk
    have hv := vals D G Pl0 T0 A T R F κ v₀ hC i Tp tup M hP
    have hv2 := hv a x₀ h
    let x := hv2.choose
    have hx : (R.HV i (tup a)).e (jVx R i (tup a) x₀) (fin _ h) = M.c0' x := hv2.choose_spec
    have hx' : ((g k : (R.HV i (tup a)).H)) = jVx R i (tup a) x₀ := hx₀.symm
    have hcf := (hφ (g k : (R.HV i (tup a)).H) (φ (g k))).2 rfl h
    let x1 := hcf.choose
    let x1' := hcf.choose_spec.choose
    have hcv : ConjVec i τ x1 x1' := hcf.choose_spec.choose_spec.1
    have h1 : (R.HV i (tup a)).e (g k : (R.HV i (tup a)).H) (fin _ h) = c x1 := hcf.choose_spec.choose_spec.2.1
    have h1' : (R.HV i (tup b)).e (φ (g k : (R.HV i (tup a)).H)) (fin _ h) = c x1' := hcf.choose_spec.choose_spec.2.2
    let xC : VsV D i ℂ := GlobalTheory.CoefModel.mapVV (inC M.c') (lamV D i) x
    have hxC : c xC = M.c0' x := hc x xC rfl
    have e0 : (R.HV i (tup a)).e (g k : (R.HV i (tup a)).H) (fin _ h) = M.c0' x := by rw [hx']; exact hx
    have e1 : c x1 = c xC := h1.symm.trans (e0.trans hxC.symm)
    have hx1 : x1 = xC := hinj e1
    let x' : VsV D i M.c'.F := ⟨MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank),
      GlobalTheory.Proof.TensorMapDescent.map_mem_VV (ta : M.c'.F →+* M.c'.F) (lamV D i) _ x.2⟩
    have hcomp : (τ : ℂ →+* ℂ).comp (inC M.c') = (inC M.c').comp (ta : M.c'.F →+* M.c'.F) := by
      ext z; exact (hta z).symm
    have hx1' : (x1' : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (inC M.c') (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) := by
      rw [hcv, hx1]
      show MvPolynomial.map (τ : ℂ →+* ℂ) (MvPolynomial.map (inC M.c') (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank)) =
        MvPolynomial.map (inC M.c') (MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank))
      rw [MvPolynomial.map_map, MvPolynomial.map_map, hcomp]
    exact ⟨x, x', rfl, e0, h1'.trans (hc x' x1' hx1')⟩

end GlobalTheory.ConjDesc
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem exists_gal_ev_E_unit {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (g : GQ l) :
    ∃ w : (Ainf l)ˣ, Per.σA g (bk.ev bk.E) = bk.ev bk.E * w := by
  have key : ∀ h : GQ l, bk.ev bk.E ∣ Per.σA h (bk.ev bk.E) := fun h => by
    rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
    have : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [this, map_zero]
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  have h2 : Per.σA g (bk.ev bk.E) ∣ bk.ev bk.E := by
    have := map_dvd (Per.σA g) (key g⁻¹)
    rwa [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one] at this
  obtain ⟨w, hw⟩ := associated_of_dvd_dvd (key g) h2
  exact ⟨w, hw.symm⟩

theorem WSeed.exists_disc_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsUnit Z → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA → ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∃ e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * e) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) ∧ bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (Y.map bk.iA * e) = bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA * (Y.map (Per.σA (g : GQ l))).map bk.iA) := by
  intro l _ K bk τ hτ d ρ s Y Z i hZ hi hWZ g G hG
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA :=
    (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hGA : ∀ y, G (bk.iA y) = bk.iA (Per.σA (g : GQ l) y) := hG.ext
  have hevE : bk.ev bk.E ≠ 0 := fun h => bk.frobenius_ev_E_ne_zero hτ (by rw [h, map_zero])
  have hE : bk.iS bk.E ≠ 0 := fun h => hevE (hinj (h.trans (map_zero _).symm))
  have hL0 : (l : bk.DA bk.ρ₀) ≠ 0 := fun h =>
    WittVector.p_nonzero l (OCb l) (hinj (by rw [map_natCast, map_zero]; exact h))
  obtain ⟨w, hw⟩ := exists_gal_ev_E_unit bk (g : GQ l)
  have hvu : bk.iA (w : Ainf l) * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hv0 : bk.iA (w : Ainf l) ≠ 0 := left_ne_zero_of_mul_eq_one hvu
  have hGE : G (bk.iS bk.E) = bk.iS bk.E * bk.iA (w : Ainf l) := by
    change G (bk.iA (bk.ev bk.E)) = _
    rw [hGA, hw, map_mul]
    rfl
  obtain ⟨li, hli⟩ : ∃ li : bk.DA bk.ρ₀, li * (l : bk.DA bk.ρ₀) = 1 := by
    obtain ⟨x, hx⟩ := (isUnit_l_disc l (bk.ev (PowerSeries.X : bk.S)) bk.ρ₀).exists_left_inv
    exact ⟨x, hx⟩
  have hnp : ∀ a b, ∃ c, (s.X'.map bk.iS * s.κ g * (s.X.map bk.iS).map G) a b = bk.iS bk.E ^ (2 * s.N) * c :=
    fun a b => s.nopole g G hG a b
  choose Q hQ using hnp
  have hQm : s.X'.map bk.iS * s.κ g * (s.X.map bk.iS).map G = bk.iS bk.E ^ (2 * s.N) • Matrix.of Q := by
    ext a b; rw [hQ a b]; rfl
  have hXX : s.X.map bk.iS * s.X'.map bk.iS =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [map_mul, map_pow, map_natCast]
  have hc : (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N) ≠ 0 := mul_ne_zero (pow_ne_zero _ hL0) (pow_ne_zero _ hE)
  have hX'X := GlobalTheory.BSP.mul_comm_of_mul_eq_smul_one _ _ _ hc hXX

  have hC1 : s.X.map bk.iS * Matrix.of Q = (l : bk.DA bk.ρ₀) ^ s.c₂ • (s.κ g * (s.X.map bk.iS).map G) := by
    refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (pow_ne_zero (2 * s.N) hE) ?_
    dsimp only
    rw [← Matrix.mul_smul, ← hQm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, smul_smul, mul_comm ((l : bk.DA bk.ρ₀) ^ s.c₂)]
  have hZi : IsUnit (Z.map i) := hZ.map (RingHom.mapMatrix i)
  have hZZ : Z.map i * (Z.map i)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hZi)
  refine ⟨(li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) • ((Z.map i)⁻¹ * Matrix.of Q * (Z.map i).map G), ?_, ?_⟩
  · have h3 : s.X.map bk.iS * Z.map i * ((li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) •
        ((Z.map i)⁻¹ * Matrix.of Q * (Z.map i).map G)) =
        (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) • (s.X.map bk.iS * Matrix.of Q * (Z.map i).map G) := by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (s.X.map bk.iS) (Z.map i), hZZ,
        Matrix.mul_one]
    have hs : G (bk.iS bk.E) ^ s.N * (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ =
        bk.iS bk.E ^ s.N := by
      rw [hGE]
      calc (bk.iS bk.E * bk.iA (w : Ainf l)) ^ s.N * (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) *
            (l : bk.DA bk.ρ₀) ^ s.c₂
          = bk.iS bk.E ^ s.N * (bk.iA (w : Ainf l) * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ s.N *
            (li * (l : bk.DA bk.ρ₀)) ^ s.c₂ := by ring
        _ = _ := by rw [hvu, hli, one_pow, one_pow, mul_one, mul_one]
    rw [h3, hC1, Matrix.smul_mul, smul_smul, smul_smul, hs, Matrix.map_mul, ← Matrix.mul_assoc]
  · have hGXX : (s.X'.map bk.iS).map G * (s.X.map bk.iS).map G =
        G ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
      rw [← Matrix.map_mul, hX'X, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    have hYG : (Y.map (Per.σA (g : GQ l))).map bk.iA = s.W.map G * (Z.map i).map G := by
      rw [← Matrix.map_mul, hWZ, Matrix.map_map, Matrix.map_map]
      congr 1
      funext y
      exact (hGA y).symm
    have hρ : (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) =
        ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA := by
      rw [Matrix.map_map]; rfl
    have hL : (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (s.W * s.X'.map bk.iS).map G *
        ((s.X.map bk.iS).map G * (Z.map i).map G) =
        G ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) •
          ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G * (Z.map i).map G) := by
      rw [Matrix.map_mul]
      calc _ = (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G *
            ((s.X'.map bk.iS).map G * (s.X.map bk.iS).map G) * (Z.map i).map G := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hGXX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    have hR : s.W * s.X'.map bk.iS * s.κ g * ((s.X.map bk.iS).map G * (Z.map i).map G) =
        bk.iS bk.E ^ (2 * s.N) • (s.W * Matrix.of Q * (Z.map i).map G) := by
      calc _ = s.W * (s.X'.map bk.iS * s.κ g * (s.X.map bk.iS).map G) * (Z.map i).map G := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hQm, Matrix.mul_smul, Matrix.smul_mul]
    have h5 := congrArg (· * ((s.X.map bk.iS).map G * (Z.map i).map G)) (s.gal g G hG)
    rw [Matrix.smul_mul, Matrix.smul_mul, hL, hR, smul_smul, smul_smul] at h5
    have h6 : s.W * Z.map i * ((li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) •
        ((Z.map i)⁻¹ * Matrix.of Q * (Z.map i).map G)) =
        (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) • (s.W * Matrix.of Q * (Z.map i).map G) := by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc s.W (Z.map i), hZZ, Matrix.mul_one]
    rw [hYG, ← hρ, ← hWZ, h6, smul_smul, ← Matrix.mul_assoc]
    have hk : bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ (2 * s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ hE) (pow_ne_zero _ hv0)) (pow_ne_zero _ hL0)
    refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) hk ?_
    dsimp only
    have hσE : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) =
        bk.iS bk.E * bk.iA (w : Ainf l) * bk.iA (Per.σA (g : GQ l) τ) := by
      rw [map_mul, hw, map_mul, map_mul]; rfl
    have hE2 : bk.iA (bk.ev bk.E * τ) = bk.iS bk.E * bk.iA τ := by rw [map_mul]; rfl
    have hGc : G ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) =
        (l : bk.DA bk.ρ₀) ^ s.c₂ * (bk.iS bk.E * bk.iA (w : Ainf l)) ^ (2 * s.N) := by
      rw [map_mul, map_pow, map_pow, map_natCast, hGE]
    rw [hσE, hE2, hGc] at h5
    rw [smul_smul, smul_smul]
    have hs1 : bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ (2 * s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ *
        (bk.iA (Per.σA (g : GQ l) τ) ^ s.N * (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N)) =
        (bk.iS bk.E * bk.iA (w : Ainf l) * bk.iA (Per.σA (g : GQ l) τ)) ^ s.N * bk.iS bk.E ^ (2 * s.N) := by
      calc _ = bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ s.N * bk.iA (Per.σA (g : GQ l) τ) ^ s.N *
            (bk.iA (w : Ainf l) * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ s.N * (li * (l : bk.DA bk.ρ₀)) ^ s.c₂ := by ring
        _ = _ := by rw [hvu, hli]; ring
    have hs2 : bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ (2 * s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA τ ^ s.N =
        (bk.iS bk.E * bk.iA τ) ^ s.N * ((l : bk.DA bk.ρ₀) ^ s.c₂ * (bk.iS bk.E * bk.iA (w : Ainf l)) ^ (2 * s.N)) := by
      ring
    rw [hs1, hs2]
    exact h5.symm

end GlobalTheory.BKLim
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem WSeed.crystallineDiscPeriods_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ),
    ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ →
      ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ =
        s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  intro l _ K bk τ hτ d ρ _ s Φ hΦ
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hΦS : ∀ x, Φ (bk.iS x) = bk.iS (frobS l bk.a x) := fun x => by
    change Φ (bk.iA (bk.ev x)) = bk.iA (bk.ev (frobS l bk.a x))
    rw [hΦ.ext, bk.ev_frob]
  have he : bk.iS (frobS l bk.a bk.E) ≠ 0 := by
    change bk.iA (bk.ev (frobS l bk.a bk.E)) ≠ 0
    rw [bk.ev_frob, ← map_zero bk.iA]
    exact fun h => bk.frobenius_ev_E_ne_zero hτ (hinj h)
  have hL0 : (l : bk.DA bk.ρ₀) ≠ 0 := fun h =>
    WittVector.p_nonzero l (OCb l) (hinj (by rw [map_natCast, map_zero]; exact h))
  have hQP : s.X.map (bk.iS.comp (frobS l bk.a)) * s.X'.map (bk.iS.comp (frobS l bk.a)) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast]
  have hc : (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hL0) (pow_ne_zero _ he)
  have hPQ := GlobalTheory.BSP.mul_comm_of_mul_eq_smul_one _ _ _ hc hQP
  have hA : (s.X'.map bk.iS).map Φ = s.X'.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; congr 1; funext x; exact hΦS x
  have hF : (s.F.map (C : Wq l bk.a →+* bk.S)).map bk.iS = s.F.map (bk.iS.comp C) := by
    rw [Matrix.map_map]; rfl
  have hX : (s.X.map (frobS l bk.a)).map bk.iS = s.X.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; rfl
  have h2 := congrArg (· * s.X.map (bk.iS.comp (frobS l bk.a))) (s.φ Φ hΦ)
  simp only [Matrix.map_mul, hA] at h2
  rw [Matrix.smul_mul, Matrix.mul_assoc (s.W.map Φ), hPQ, Matrix.mul_smul, Matrix.mul_one, smul_smul] at h2
  rw [Matrix.map_mul, Matrix.map_mul, hF, hX]
  refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (pow_ne_zero s.N he) ?_
  dsimp only
  calc bk.iS (frobS l bk.a bk.E) ^ s.N • (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
        s.W.map Φ)
      = ((l : bk.DA bk.ρ₀) ^ s.c₁ * ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N))) •
        s.W.map Φ := by rw [smul_smul]; congr 1; ring
    _ = _ := h2
    _ = _ := by rw [Matrix.smul_mul]; simp only [Matrix.mul_assoc]

end GlobalTheory.BKLim
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_smul_top_eq {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) :
    (I ^ n • (⊤ : Submodule A A)) = I ^ n := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

theorem mulVec_mem_of_mem {B : Type} [CommRing B] {d : ℕ} (E : Matrix (Fin d) (Fin d) B) (J : Ideal B)
    (v : Fin d → B) (hv : ∀ j, v j ∈ J) (i : Fin d) : E.mulVec v i ∈ J := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv j)

theorem lift_solution_of_step {A B : Type} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (hA : IsPrecomplete I A) (hB : IsHausdorff J B) {d : ℕ} (p q : A →+* B)
    (hp : ∀ m : ℕ, I ^ m ≤ (J ^ m).comap p) (hq : ∀ m : ℕ, I ^ m ≤ (J ^ m).comap q)
    (E : Matrix (Fin d) (Fin d) B)
    (step : ∀ (m : ℕ) (z : Fin d → A), (∀ i, p (z i) - E.mulVec (fun j => q (z j)) i ∈ J ^ m) →
      ∃ z' : Fin d → A, (∀ i, z' i - z i ∈ I ^ m) ∧
        ∀ i, p (z' i) - E.mulVec (fun j => q (z' j)) i ∈ J ^ (m + 1))
    (z : Fin d → A) (hz : ∀ i, p (z i) - E.mulVec (fun j => q (z j)) i ∈ J ^ 1) :
    ∃ z' : Fin d → A, (∀ i, z' i - z i ∈ I ^ 1) ∧
      (fun i => p (z' i)) = E.mulVec (fun j => q (z' j)) := by

  let res : (Fin d → A) → Fin d → B := fun w i => p (w i) - E.mulVec (fun j => q (w j)) i
  have hres_sub : ∀ (w w' : Fin d → A) (i : Fin d),
      res w i - res w' i = p (w i - w' i) - E.mulVec (fun j => q (w j - w' j)) i := by
    intro w w' i
    have : (fun j => q (w j - w' j)) = (fun j => q (w j)) - (fun j => q (w' j)) := by
      funext j; simp
    show p (w i) - E.mulVec (fun j => q (w j)) i - (p (w' i) - E.mulVec (fun j => q (w' j)) i) = _
    rw [this, Matrix.mulVec_sub, Pi.sub_apply, map_sub]
    ring

  have hseq : ∃ g : ℕ → (Fin d → A), g 0 = z ∧ (∀ k i, res (g k) i ∈ J ^ (k + 1)) ∧
      ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1) := by
    let G : (k : ℕ) → {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)} := fun k =>
      Nat.rec (motive := fun k => {w : Fin d → A // ∀ i, res w i ∈ J ^ (k + 1)}) ⟨z, hz⟩
        (fun k w => ⟨Classical.choose (step (k + 1) w.1 w.2),
          (Classical.choose_spec (step (k + 1) w.1 w.2)).2⟩) k
    refine ⟨fun k => (G k).1, rfl, fun k => (G k).2, fun k i => ?_⟩
    exact (Classical.choose_spec (step (k + 1) (G k).1 (G k).2)).1 i
  let g := Classical.choose hseq
  have hg0 : g 0 = z := (Classical.choose_spec hseq).1
  have hgres : ∀ k i, res (g k) i ∈ J ^ (k + 1) := (Classical.choose_spec hseq).2.1
  have hgd : ∀ k i, g (k + 1) i - g k i ∈ I ^ (k + 1) := (Classical.choose_spec hseq).2.2

  have hcau : ∀ i {m n : ℕ}, m ≤ n → g n i - g m i ∈ I ^ m := by
    intro i m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : g (n + 1) i - g n i ∈ I ^ m :=
        Ideal.pow_le_pow_right (by omega) (hgd n i)
      have := Ideal.add_mem _ h1 ih
      simpa using this

  have hlim : ∀ i, ∃ L : A, ∀ n, g n i - L ∈ I ^ n := by
    intro i
    have h := @IsPrecomplete.prec' A _ I A _ _ hA (fun k => g k i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, pow_smul_top_eq]
      have := hcau i hmn
      rw [← neg_mem_iff, neg_sub] at this
      exact this)
    refine ⟨Classical.choose h, fun n => ?_⟩
    have := Classical.choose_spec h n
    rw [SModEq.sub_mem, pow_smul_top_eq] at this
    exact this
  let z' : Fin d → A := fun i => Classical.choose (hlim i)
  have hz' : ∀ i n, g n i - z' i ∈ I ^ n := fun i => Classical.choose_spec (hlim i)
  refine ⟨z', fun i => ?_, ?_⟩
  · have h1 : g 1 i - z' i ∈ I ^ 1 := hz' i 1
    have h2 : g 1 i - g 0 i ∈ I ^ 1 := hgd 0 i
    rw [hg0] at h2
    have := Ideal.sub_mem _ h2 h1
    simpa using this
  · funext i
    rw [← sub_eq_zero]
    refine hB.haus' _ fun k => ?_
    rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq]
    have hd : res (g k) i - res z' i ∈ J ^ k := by
      rw [hres_sub]
      refine Ideal.sub_mem _ (hp k (hz' i k)) ?_
      exact mulVec_mem_of_mem E _ _ (fun j => hq k (hz' j k)) i
    have hr : res (g k) i ∈ J ^ k := Ideal.pow_le_pow_right (by omega) (hgres k i)
    have := Ideal.sub_mem _ hr hd
    simpa [res] using this

theorem lift_solution (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D) (hh : Cover h)
    (hpo : IsPO h h p q) (z : Fin d → C.A)
    (hz : ∀ i, p.f (z i) - (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z j)) i ∈ adI D ^ 1) :
    ∃ z' : Fin d → C.A, (∀ i, z' i - z i ∈ adI C ^ 1) ∧
      (fun i => p.f (z' i)) = (S.ε (p.comp f) (q.comp f)).mulVec (fun j => q.f (z' j)) :=
  lift_solution_of_step (adI C) (adI D) C.complete.toIsPrecomplete D.complete.toIsHausdorff p.f q.f
    (adI_pow_le p) (adI_pow_le q) _ (GlobalTheory.T.lift_stratifiedSolution_succ_of_cover l K bk d S B C D h f p q hh hpo) z hz

end GlobalTheory.BSP
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_isPrismLocalizationAway_of_generated : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (s d : B.A), GenAway B s d → ∃ (C : Obj l R) (h : Hom B C), IsLoc s h ∧ C.I = Ideal.span {h.f d} := by
  first | exact @GlobalTheory.BSP.exists_isLoc | exact GlobalTheory.BSP.exists_isLoc | (intros; apply GlobalTheory.BSP.exists_isLoc <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.finiteLength_coker_of_surjective_mod_uniformizer : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → IsFiniteLength (A O K) F.coker) ∧ ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM) := by
  first | exact @GlobalTheory.BK.Hom.finiteLength_coker_of_generic | exact GlobalTheory.BK.Hom.finiteLength_coker_of_generic | (intros; apply GlobalTheory.BK.Hom.finiteLength_coker_of_generic <;> assumption)
end
