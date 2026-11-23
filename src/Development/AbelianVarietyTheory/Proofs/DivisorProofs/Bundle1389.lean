module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle326
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle019
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle018
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open Formalism.L2.JoinChr
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramCharUnique

theorem eq_one_of_loc {D : D7} {χ : (AE D)ˣ →* Circle} (h : ChrEq χ 1) (x : (AE D)ˣ) : χ x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D χ h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) χ 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

theorem loc_parts {D : D7} {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) (k : D.host.E)
    (hk : P.valuation D.host.E k ≤ 1) : infPart D (locE D e k) = 1 ∧ finPart D (locE D e k) ∈ intAE D := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h1, h2, h3⟩ := HeckeTensorRead.isPlIdem_parts D ι hι hint he
  refine ⟨(HeckeTensorRead.map_loc (infPart D) e _).trans (by rw [h1, zero_mul, add_zero]), (hint _).2 fun Q => ?_⟩
  have h4 : ι (finPart D (incA D k)) = algebraMap D.host.E _ k := hι k
  have h5 : ι (finPart D (locE D e k)) = 1 + ι (finPart D e) * (algebraMap D.host.E _ k - 1) := by
    rw [← h4]
    exact HeckeTensorRead.map_loc (ι.toRingHom.comp (finPart D)) e _
  rw [h5]
  change Valued.v (1 + ι (finPart D e) Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) k - 1)) ≤ 1
  by_cases hQ : Q = P
  · subst hQ
    rw [h2, one_mul, add_sub_cancel, GlobalTheory.CharLocProd.val_algebraMap]
    exact hk
  · rw [h3 Q hQ, zero_mul, add_zero, map_one]

noncomputable def locHom {D : D7} {e : AE D} (he : e * e = e) : D.host.Eˣ →* (AE D)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun k => locE D e (k : D.host.E)
      map_one' := by simp [locE]
      map_mul' := fun k l => (locE_mul_locE he k l).symm }

theorem eq_one_of_unif {D : D7} {c : (AE D)ˣ →* Circle} (hc : IsHeckeChar D c) (hu : UnramEverywhere D c)
    (h : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ x : (AE D)ˣ,
      (x : AE D) = locE D e (Formalism.L2.Host.unif P : D.host.Eˣ) → c x = 1) (x : (AE D)ˣ) : c x = 1 := by
  refine eq_one_of_loc ⟨hc, fun P e he k y hy => ?_⟩ x
  obtain rfl : y = locHom he.1 k := Units.ext hy
  have hπ : P.valuation D.host.E ((Formalism.L2.Host.unif P : D.host.Eˣ) : D.host.E) = WithZero.exp (-1 : ℤ) :=
    (GlobalTheory.CharLocProd.val_algebraMap P _).symm.trans (Formalism.L2.Host.unif_spec P)
  have h0 : P.valuation D.host.E (k : D.host.E) ≠ 0 := by simp
  obtain ⟨n, hn⟩ : ∃ n : ℤ, P.valuation D.host.E (k : D.host.E) = WithZero.exp n := ⟨_, (WithZero.exp_log h0).symm⟩
  let u : D.host.Eˣ := k * Formalism.L2.Host.unif P ^ n
  have hv : P.valuation D.host.E (u : D.host.E) = 1 := by
    simp only [u, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hn, hπ]
    rw [← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hv' : P.valuation D.host.E ((u⁻¹ : D.host.Eˣ) : D.host.E) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  have h1 : c (locHom he.1 u) = 1 :=
    hu _ (loc_parts he _ hv.le).1 (loc_parts he _ hv.le).2 (by
      rw [← map_inv]
      exact (loc_parts he _ hv'.le).2)
  rw [map_mul, map_mul, map_zpow, map_zpow, h P e he (locHom he.1 (Formalism.L2.Host.unif P)) rfl, one_zpow, mul_one] at h1
  rw [h1]
  rfl

theorem isEtaConj_unique : ∀ (D : D7) (σ : D.what₂.LL →+* ℂ) (η η' η'' : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ η η' → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsEtaConj σ η η'' → η' = η'' := by
  rintro D σ η η' η'' ⟨h1, h2, h3⟩ ⟨g1, g2, g3⟩
  refine MonoidHom.ext fun x => mul_inv_eq_one.1 (eq_one_of_unif (c := η' * η''⁻¹)
    ⟨h1.1.mul g1.1.inv, fun k => mul_inv_eq_one.2 ((h1.2 k).trans (g1.2 k).symm)⟩
    (fun y a b c => mul_inv_eq_one.2 ((h2 y a b c).trans (g2 y a b c).symm))
    (fun P e he y hy => mul_inv_eq_one.2 ?_) x)
  obtain ⟨a, ha, ha'⟩ := h3 P e he y hy
  obtain ⟨b, hb, hb'⟩ := g3 P e he y hy
  obtain rfl : a = b := D.what₂.embLL.injective (ha.trans hb.symm)
  have : Finite (kP P) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  have hpos : (0 : ℝ) < (Nat.card (kP P) : ℝ) := Nat.cast_pos.2 Nat.card_pos
  exact Subtype.ext (mul_right_cancel₀ (Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 hpos).ne'))
    (ha'.symm.trans hb'))

end GlobalTheory.UnramCharUnique
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.GalLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Datum

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  (σ : D.what₂.LL →+* ℂ)

abbrev Comparison₂ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W)
    (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) : Prop :=
  Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L

abbrev ptAt (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) :
    PolF D (Wc D i).rank (Vc D i).rank → (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f

structure VecData (f₀ f : WO (Vc D i) (Wc D i) → ℂ)
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) : Prop where
  vec : IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg ∅ (fun _ => 1) f₀ f
  onb : ∀ ρ, IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (B ρ) (pW D i ρ)
  theta : ∀ P, IsThetaFunO R.ψ (Vc D i) (Wc D i) (ptAt R i σ B f P)

def LiftData (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (H : HMod (Bridge.Gf (Vc D i) → c.W))
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) : Prop :=
  IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω ∧ VecData R i σ f₀ f B ∧
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ B f) (deltaConj i σ) io ∧
    Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (ptAt R i σ B f) io
      (LinearMap.range (c.ext ∘ₗ H.e)) thP

def IsProjOf {c : CoefA (Vc D i)} {H : HMod (Bridge.Gf (Vc D i) → c.W)}
    (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ)))
    (th : H.H →ₗ[ℂ] (R.HW i σ).H) : Prop :=
  ∀ (x : H.H) (v : ∀ ρ, lowT (R.MW i σ) ρ),
    (R.HW i σ).e (th x) (fun ρ => v ρ) = R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict x) (PiTensorProduct.tprod ℂ v))

theorem isConjLift_iff (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (H : HMod (Bridge.Gf (Vc D i) → c.W))
    (th : H.H →ₗ[ℂ] (R.HW i σ).H) :
    IsConjLift R i σ μ' η' c H th ↔ ∃ ω f₀ f B io thP, LiftData R i σ μ' η' c H ω f₀ f B io thP ∧ IsProjOf R i σ thP th := by
  constructor
  · rintro ⟨ω, f₀, f, B, io, thP, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨ω, f₀, f, B, io, thP, ⟨h1, ⟨h2, h3, h4⟩, h5, h6⟩, h7⟩
  · rintro ⟨ω, f₀, f, B, io, thP, h, h7⟩
    exact ⟨ω, f₀, f, B, io, thP, h.1, h.2.1.vec, h.2.1.onb, h.2.1.theta, h.2.2.1, h.2.2.2, h7⟩

structure CoefAt (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) : Prop where
  coef : c.Is
  act : ∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE →
    ∀ v, c₁ (rhoVr (labLL D) (lamV D i) γE v) = c.ρ (γ : GA D (Vc D i)) (c₁ v)
  indep : LinearIndependent ℂ fun a => c₁ (bVV D.what₂.LL (lamV D i) a)
  span : Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL (lamV D i) a)) = ⊤
  pair : ∀ a b, inner ℂ (c₁ (bVV D.what₂.LL (lamV D i) a)) (c₁ (bVV D.what₂.LL (lamV D i) b)) =
    σ (pairVr (labLL D) (lamV D i) (gramV D i) (bVV D.what₂.LL (lamV D i) a) (bVV D.what₂.LL (lamV D i) b))

def PhaseFun (u : GA D (Wc D i) → ℂ) : Prop :=
  (∀ h, ‖u h‖ = 1) ∧ (∀ γ ∈ GQ (Wc D i), ∀ h, u (γ * h) = u h) ∧ (∀ g ∈ GinfC (Wc D i), ∀ h, u (h * g) = u h) ∧
    ∀ k ∈ levW R i, ∀ h, u (h * k) = u h

abbrev IsLiftW (g : G) (k : GA D (Wc D i)) : Prop := Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k

def EtaVals : Prop :=
  ∀ (P : Pl D.host.E) (e : AE D), Formalism.L2.JoinChr.IsPlIdem D e P → ∀ x : (AE D)ˣ,
    (x : AE D) = Formalism.L2.JoinChr.locE D e (Formalism.L2.Host.unif P : D.host.Eˣ) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = ((R.eta x : Circle) : ℂ) * (((Real.sqrt (Nat.card (kP P) : ℝ))⁻¹ : ℝ) : ℂ)

end Datum

section Geo

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  (O : OMDat T.toCore R i Unit (fun _ => A.μ0))

def RepsAt (v₀ : (R.MW i (sg0 D A)).Vec) (h : O.Cl' () → GA D (Vc D i)) : Prop :=
  ∃ J' : Subgroup (Bridge.Gf (Vc D i)), RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) ∧
    PlaceEx R i A.μ0 h O.c0' ∧ ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ()) ∧
      ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x

abbrev actG (g : G) : T.R ((i : ℕ) + 1) →ₗ[T.Q.c.F] T.R ((i : ℕ) + 1) := actLev T.Q.c O.lev2 g

variable (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))

def IsClassSum (h : O.Cl' () → GA D (Vc D i)) (x₀ : A.fam.amb.FL i A.μ0) {n : ℕ} (a : Fin n → D.what₂.LL)
    (f : Fin n → Cu T κ i) : Prop :=
  ∃ (x : O.Cl' () → VsV D i O.c'.F) (f' : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c'),
    Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x ∧ f' ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA (κ i)) (Vc D i).rank ∧
    IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ ()) (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ()) O.io x f' ∧
    IsBC O.hle f' (fun k => O.jL (a k)) (fun k => (f k : T.R ((i : ℕ) + 1)))

def EquivBy (σ : D.what₂.LL →+* ℂ) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (u : GA D (Wc D i) → ℂ) : Prop :=
  ∀ g k, IsLiftW R i g k → ∀ (f : Cu T κ i) (h : GA D (Wc D i)),
    u h * phiC T hV (wtA (κ i)) (actG O g (f : T.R ((i : ℕ) + 1))) h =
      σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) * (u (h * k) * phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) (h * k))

end Geo

end GlobalTheory.GalLift

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
namespace GlobalTheory.AdeleCocompactExt

theorem exists_compact_adeleE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ K : Set (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), IsCompact K ∧ ∀ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  intro F E _ _ _ _ _
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K₀, hK₀, hK⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  haveI : IsModuleTopology (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := ⟨rfl⟩
  haveI : IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := IsModuleTopology.isTopologicalRing (AF F) _
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hφ : Continuous B.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap
  refine ⟨B.equivFun.symm '' Set.pi Set.univ (fun _ => K₀),
    (isCompact_univ_pi fun _ => hK₀).image hφ, ?_⟩
  intro a
  choose x hx using fun k => hK (B.equivFun a k)
  refine ⟨∑ k, x k • b k, fun k => B.equivFun a k - algebraMap F (AF F) (x k), fun k _ => hx k, ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  funext k
  have h1 : B.equivFun (inclR (F := F) (AF F) (∑ k, x k • b k)) k = algebraMap F (AF F) (x k) := by
    rw [Module.Basis.equivFun_apply]
    show (B.repr ((1 : AF F) ⊗ₜ[F] (∑ k, x k • b k))) k = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp [b, Module.Basis.repr_sum_self]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Finsupp.single_apply, hj]) (by simp)]
    simp
  simp only [map_sub, Pi.sub_apply, h1]

end GlobalTheory.AdeleCocompactExt
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.AdeleCocompactExt

theorem exists_compact_adele_ext : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ C : Set (AE F E), IsCompact C ∧ ∀ a : AE F E, ∃ α : E, a - inclR (F := F) (AF F) α ∈ C := by
  intro F E _ _ _ _ _
  classical
  haveI : IsModuleTopology (AF F) (AE F E) := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.modTop
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  obtain ⟨K, hK, hK'⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  let b := Module.finBasis F E
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  let φ : (Fin (Module.finrank F E) → AF F) → AE F E := fun c => ∑ i, c i • B i
  have hφ : Continuous φ := continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  refine ⟨φ '' Set.univ.pi (fun _ => K), (isCompact_univ_pi fun _ => hK).image hφ, fun a => ?_⟩
  choose x hx using fun i => hK' (B.repr a i)
  refine ⟨∑ i, x i • b i, fun i => B.repr a i - algebraMap F (AF F) (x i), fun i _ => hx i, ?_⟩
  have hB : ∀ i, B i = (1 : AF F) ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply _ _
  have hincl : inclR (F := F) (AF F) (∑ i, x i • b i) = ∑ i, algebraMap F (AF F) (x i) • B i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_smul,
      Algebra.TensorProduct.includeRight_apply, hB, algebraMap_smul]
  simp only [φ, sub_smul, Finset.sum_sub_distrib, hincl]
  rw [B.sum_repr a]

end GlobalTheory.AdeleCocompactExt
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.AdelicUnitaryTop

theorem lcsc_UA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  intro F E _ _ _ _ _ σ n J
  haveI := locallyCompact_adele F
  haveI := secondCountable_adele F
  haveI := t2Space_adeleRing_numberField F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hσ : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul
      (hv.matrix_map hσ)) continuous_const
  exact ⟨hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology,
    inferInstanceAs (T2Space (UG (cA σ) (incM F J)))⟩

end GlobalTheory.AdelicUnitaryTop
end

section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.ThK.EvAt0

noncomputable section

open scoped Classical

namespace GlobalTheory.ThK.EvAt0.PolD

variable {F : Type} [Field F] [NumberField F]

def linL {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ
      ∑ i, (LinearMap.mulRight ℝ (b i)) ∘ₗ LinearMap.proj i)

theorem linL_apply {κ : Type} [Fintype κ] (b x : κ → mixedEmbedding.mixedSpace F) :
    linL b x = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * b i) := by
  simp [linL]

def lin {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) (x : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * b i) : ℝ) : ℂ)

theorem lin_hasTemperateGrowth {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) :
    (lin b).HasTemperateGrowth := by
  have e : lin b = ⇑(Complex.ofRealCLM.comp (linL b)) := by
    funext x; simp [lin, linL_apply]
  rw [e]
  exact (Complex.ofRealCLM.comp (linL b)).hasTemperateGrowth

def mulOp {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) : SInf F κ →L[ℂ] SInf F κ :=
  SchwartzMap.smulLeftCLM ℂ (lin b)

theorem mulOp_apply {κ : Type} [Fintype κ] (b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ)
    (x : κ → mixedEmbedding.mixedSpace F) : mulOp b f x = lin b x * f x := by
  simp [mulOp, SchwartzMap.smulLeftCLM_apply_apply (lin_hasTemperateGrowth b)]

def dOp {κ : Type} [Fintype κ] (a b : κ → mixedEmbedding.mixedSpace F) : SInf F κ →L[ℂ] SInf F κ :=
  LineDeriv.lineDerivOpCLM ℂ (SInf F κ) a - ((2 * Real.pi * Complex.I : ℂ)) • mulOp b

theorem dOp_apply {κ : Type} [Fintype κ] (a b : κ → mixedEmbedding.mixedSpace F) (f : SInf F κ)
    (x : κ → mixedEmbedding.mixedSpace F) :
    dOp a b f x = fderiv ℝ f x a - 2 * Real.pi * Complex.I * lin b x * f x := by
  simp [dOp, mulOp_apply, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  ring

def arc {κ : Type} (c : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (c i)

def liftA (v : mixedEmbedding.mixedSpace F) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm v)

theorem evI_liftA (v : mixedEmbedding.mixedSpace F) : evI F (liftA v) = v := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm v) = v
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply v

theorem smul_liftA {c : AF F} (hc : evI F c = 0) (v : mixedEmbedding.mixedSpace F) : c • liftA v = 0 := by
  have h1 : c.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hc)
  have key : ∀ x y : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F, x.1 = 0 → y.2 = 0 → x * y = 0 :=
    fun x y hx hy => Prod.ext (by simp [hx]) (by simp [hy])
  exact key c (liftA v) h1 rfl

variable {n d d₁ : ℕ}

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def GaussD {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (g : SInf F (Fin n × Fin d)) : Prop :=
  ∃ ε : InfinitePlace F → ℤˣ, ∀ u u' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → At (evI F) u' →
    (∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (τ w)) * (W.θ w)ᵀ)) →
    dOp (arc (M.co.e u').1) (arc (M.co.e u').2) g = Complex.I • dOp (arc (M.co.e u).1) (arc (M.co.e u).2) g

end GlobalTheory.ThK.EvAt0.PolD
end
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.NormAtPlace

theorem evFin_norm_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (x : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    evFin F v (Algebra.norm (AF F) x) = Algebra.norm (Fv F v) (compFin F E v x) := by
  intro F E _ _ _ _ _ v x
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let e := Module.finBasis F E
  let b := Algebra.TensorProduct.basis (AF F) e
  let b' := Algebra.TensorProduct.basis (Fv F v) e
  have hrepr : ∀ (z : AF F ⊗[F] E) i, b'.repr (compFin F E v z) i = evFin F v (b.repr z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a y =>
      simp only [compFin, b, b', AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul, AlgHom.commutes]
    | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz]
  have hb : ∀ j, compFin F E v (b j) = b' j := by
    intro j
    simp [compFin, b, b', Algebra.TensorProduct.basis_apply]
  have hmat : Algebra.leftMulMatrix b' (compFin F E v x) = (Algebra.leftMulMatrix b x).map (evFin F v) := by
    ext i j
    rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      ← hb j, ← map_mul, hrepr]
  rw [Algebra.norm_eq_matrix_det b', Algebra.norm_eq_matrix_det b, hmat]
  exact AlgHom.map_det (evFin F v) (Algebra.leftMulMatrix b x)

end GlobalTheory.NormAtPlace
end
