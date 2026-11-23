module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3393
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3433
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3387
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle779
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2740
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle676
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartDer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartConst

theorem exists_derivation_top {R : Type} [CommRing R] [Algebra ℤ R] (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ Γ(Sp R, ⊤) Γ(Sp R, ⊤), ⇑D' = fun r =>
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)) := by
  have e : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
    fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply r
  refine ⟨Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))
      map_zero' := by rw [map_zero, map_zero, map_zero]
      map_add' := fun x y => by rw [map_add (f := _), map_add (f := _), map_add (f := _)] }) fun a b => ?_, rfl⟩
  change (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (a * b))) =
    a • (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)) +
      b • (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a))
  rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, e, e, smul_eq_mul, smul_eq_mul]

theorem valR_mem_maximalIdeal {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (g : Sp R ⟶ X) (U : X.Opens)
    (hU : ⊤ ≤ g ⁻¹ᵁ U) (f : Γ(X, U)) (hf : g (closedPoint R) ∉ X.basicOpen f) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U ⊤ hU).hom f) ∈ maximalIdeal R := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 := hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have e : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
    fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply r
  rw [e] at h1
  have h2 := (Sp R).basicOpen_of_isUnit h1
  have h3 := Scheme.basicOpen_appLE g ⊤ U hU f
  have h4 : closedPoint R ∈ (⊤ : (Sp R).Opens) ⊓ g ⁻¹ᵁ X.basicOpen f := by
    rw [← h3]
    exact h2.ge trivial
  exact hf h4.2

theorem isConstAlong_of_ks_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)) (m : Ideal Γ(Y.X, U.1)), m.IsMaximal → ∀ x : Y.X, x ∉ interior Y → x ∈ U.1 → (∀ f ∈ m, x ∉ Y.X.basicOpen f) → IsKS Y.t (interior Y) U v D.1 Θ → (∀ a b, Θ a b ∈ m) → ∀ (k : Type) [Field k] (m' d : ℕ) (ξ : Sp (ChartRing k m' d) ⟶ gen Y) (x' : gen Y), ξ (closedPoint _) = x' → genι Y x' = x → ∀ (t : SAB H (Sp (ChartRing k m' d))) (P : PELUnif (maximalIdeal (ChartRing k m' d)) t) (gam : Fin m' → levelForms H l.M' P.D.toPre.X), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m' d i} → (∀ p : Sp (ChartRing k m' d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m' d i ∈ p.asIdeal) → Nonempty (SABMap t Y.t (ξ ≫ genι Y)) → IsMonomial P.D.toPre (bdParam k m' d) (fun i => gam i) → IsPartOfBasis gam → ∀ (hU : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1) (DR : Derivation ℤ (ChartRing k m' d) (ChartRing k m' d)) (a : Fin m' → (ChartRing k m' d)), (∀ r, DR (valR (ξ ≫ genι Y) U.1 r) = valR (ξ ≫ genι Y) U.1 (D.1 r)) → (∀ i, DR (bdParam k m' d i) = a i * bdParam k m' d i) → ∀ ρ : ChartRing k m' d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (DR r))) → ∃ c₀ : ℚ, c₀ ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m' d) (fun i => gam i) ρ (fun i => (c₀ : k) * MvPowerSeries.constantCoeff (a i)) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm hsnc U n v A hv hb hA D Θ m hm x hxi hxU hxm hKS hΘ k _ m' d ξ x' hξ hx'x t P gam
    hEt hId hBd ⟨φ⟩ hMon hPart hU DR a hDR ha ρ hρ
  subst hξ hx'x
  have hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1 := hxU
  have : CharZero k := GlobalTheory.LocReg.charZero_of_chart E H Dw l Xo c Y k m' d ξ
  have hfac := GlobalTheory.LocReg.comp_genι_eq_spMap_chartHom E H Dw l Xo c Y U k m' d ξ hx
  obtain ⟨vR, hvR, hbR, hcomp⟩ := GlobalTheory.LocReg.BasisPull.exists_basis_pull E H Y.X Y.t U _ (GlobalTheory.LocReg.chartHom Y U ξ hx) t _ hfac φ n v hv hb
  have hab := GlobalTheory.ChartAbLocus.mem_abLocus_iff E H Dw l Xo c Y k m' d ξ t φ hBd
  have hlin : LinearIndependent ℤ (fun i => (gam i : LinearMap.BilinForm ℤ P.D.toPre.X)) :=
    hPart.linearIndependent.map' (Submodule.subtype _) (by simp)
  have e : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom.hom r) = r :=
    fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom_inv_id_apply r
  have hval : ∀ r, valR (ξ ≫ genι Y) U.1 r = (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom.hom
      (((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom r) := fun r => dif_pos hU
  have hch : ∀ r, valR (ξ ≫ genι Y) U.1 r = GlobalTheory.LocReg.chartHom Y U ξ hx r := fun r => by
    have h := GlobalTheory.CechKSSmul.valR_spMap_chart U (GlobalTheory.LocReg.chartHom Y U ξ hx) r
    rwa [← hfac] at h
  have happ : (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx) =
      ((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom := RingHom.ext fun r => by
    rw [RingHom.comp_apply, ← hch, hval, e]
  obtain ⟨D', hD'⟩ := exists_derivation_top DR
  have hV : (⊤ : (Sp (ChartRing k m' d)).Opens) ⊓ (Sp (ChartRing k m' d)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom (∏ i, bdParam k m' d i)) ≤
      (ξ ≫ genι Y) ⁻¹ᵁ interior Y := by
    intro p hp
    have h1 : p ∈ (Sp (ChartRing k m' d)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom (∏ i, bdParam k m' d i)) := hp.2
    have h2 := basicOpen_eq_of_affine (R := CommRingCat.of (ChartRing k m' d)) (∏ i, bdParam k m' d i)
    have h3 : p ∈ PrimeSpectrum.basicOpen (∏ i, bdParam k m' d i) := h2.le h1
    have h4 : ξ p ∉ genBd Y := fun h => h3 ((hBd p).1 h)
    rw [mem_genBd_iff, not_not, ← coe_interior] at h4
    exact h4
  have hK := GlobalTheory.T.cechKodairaSpencer_pullback_semiAbelianMap E H Y.X (Sp (ChartRing k m' d)) Y.t t (ξ ≫ genι Y) φ (interior Y) _ U
    (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m' d)).affineOpens) hU hV n v vR hv hvR
    (fun i => by rw [hcomp i, happ]) D.1 D' (fun r => by
      rw [hD']
      show (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).inv.hom (DR
        ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m' d))).hom.hom (((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom r))) =
        ((ξ ≫ genι Y).appLE U.1 ⊤ hU).hom (D.1 r)
      rw [← hval, hDR, hval, e]) Θ hKS
  rw [hD'] at hK
  exact GlobalTheory.T.isConstAlong_of_kodairaSpencer_zero_chart E H k m' d t P (fun i => gam i) hMon hlin hab n vR hvR hbR DR a ha _ hK
    (fun a b => valR_mem_maximalIdeal (ξ ≫ genι Y) U.1 hU (Θ a b) (hxm _ (hΘ a b))) ρ hρ

end GlobalTheory.ChartConst
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTCount

theorem sub_smul_mul_sub_smul_eq_zero_of_quadratic {k E : Type*} [Field k] [Ring E] [Algebra k E] (X : E) (tr nm : ℤ) (r r' : k)
    (hX : X * X = (tr : E) * X - (nm : E)) (hs : r + r' = tr) (hp : r * r' = nm) :
    (X - r • (1 : E)) * (X - r' • (1 : E)) = 0 := by
  have htr : (tr : E) = algebraMap k E r + algebraMap k E r' := by rw [← map_add (f := _), hs, map_intCast]
  have hnm : (nm : E) = algebraMap k E r * algebraMap k E r' := by rw [← map_mul, hp, map_intCast]
  rw [Algebra.smul_def, Algebra.smul_def, _root_.mul_one, _root_.mul_one, sub_mul, mul_sub, mul_sub, hX, htr, hnm,
    ← Algebra.commutes r' X]
  noncomm_ring

end GlobalTheory.HTCount

namespace GlobalTheory.HTCount

theorem ksDim_at_point : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → KSDim (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β ht φ hφ
  obtain ⟨hfd, hdim, hskew, hiso⟩ := GlobalTheory.T.harrisTaylor_pairing_skew_hodge_lagrangian p D R b N hN hNp k t o₀ β ht φ hφ
  have hnd := GlobalTheory.T.harrisTaylor_polarisation_pairing_nondegenerate p D R b N hN hNp k t o₀ β ht φ hφ
  have hadj := GlobalTheory.T.harrisTaylor_crystal_action_adjoint p D R b N hN hNp k t o₀ β ht φ hφ
  have hcount := GlobalTheory.T.harrisTaylor_rho_part_deformation_dim p D R b N hN hNp k t o₀ β ht
  haveI := hfd
  have hstab : ∀ a, ∀ x ∈ Fil o₀.A, crysAct o₀ a x ∈ Fil o₀.A := fun a x hx => by
    haveI := o₀.act.hom a
    rw [crysAct_apply]; exact push_mem_Fil _ hx
  have hcomm : ∀ a, crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) * crysAct o₀ a = crysAct o₀ a * crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) := fun a => by
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hsurj : Function.Surjective (fun c : D.O => (D.star c).unop) := fun a => ⟨(D.star a).unop, D.star_star a⟩

  have hbar : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
  have hωsq : D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hw2 : algebraMap (𝓞 D.F) D.O D.ω * algebraMap (𝓞 D.F) D.O D.ω =
      (D.tr : D.O) * algebraMap (𝓞 D.F) D.O D.ω - (D.nm : D.O) := by
    rw [← map_mul, hωsq, map_sub, map_mul, map_intCast, map_intCast]
  have hstw : (D.star (algebraMap (𝓞 D.F) D.O D.ω)).unop = (D.tr : D.O) - algebraMap (𝓞 D.F) D.O D.ω := by
    rw [D.star_F, MulOpposite.unop_op, hbar, map_sub, map_intCast]
  have hrr : β b.ρ * ((D.tr : k) - β b.ρ) = (D.nm : k) := by
    have := congrArg β b.ρ_root
    simp only [map_add (f := _), map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    linear_combination -this
  have hsum : β b.ρ + ((D.tr : k) - β b.ρ) = (D.tr : k) := by ring
  have hdisc : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) ≠ 0 := by
    have hp : p.Prime := Fact.out
    have hnd : ¬ p ∣ (D.tr ^ 2 - 4 * D.nm).natAbs := fun h => D.disc_p (Int.ofNat_dvd_left.2 h)
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    have hu := (b.unit _ hcop).map β
    rw [map_natCast] at hu
    intro h0
    rcases Int.natAbs_eq (D.tr ^ 2 - 4 * D.nm) with e | e
    · rw [e, Int.cast_natCast] at h0; exact hu.ne_zero h0
    · rw [e, Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h0; exact hu.ne_zero h0
  have hne : β b.ρ ≠ (D.tr : k) - β b.ρ := by
    intro h
    apply hdisc
    push_cast
    linear_combination (2 * β b.ρ - (D.tr : k)) * h + 4 * hrr
  have hZ : lieZ o₀ β ≤ LinearMap.range (crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨n, lam, c, y, ⟨y₀, rfl⟩, -, rfl⟩
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ⟨crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y₀, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply]
    congr 1
    rw [sub_mul, mul_sub, hcomm, smul_mul_assoc, mul_smul_comm, _root_.one_mul, _root_.mul_one]
  generalize lieZ o₀ β = Z at hZ hcount ⊢
  generalize crysAct o₀ = ρ at hstab hcomm hadj hcount hZ ⊢
  generalize algebraMap (𝓞 D.F) D.O D.ω = w at hw2 hstw hcomm hcount hZ
  have hq := sub_smul_mul_sub_smul_eq_zero_of_quadratic (ρ w) D.tr D.nm (β b.ρ) ((D.tr : k) - β b.ρ)
    (by rw [← map_mul, hw2, map_sub, map_mul, map_intCast, map_intCast]) hsum hrr
  have hwadj : ∀ x y, φ (ρ w x) y = φ x ((β b.ρ + ((D.tr : k) - β b.ρ)) • y - ρ w y) := fun x y => by
    rw [hadj, hstw, map_sub, map_intCast, hsum, LinearMap.sub_apply, Module.End.intCast_apply,
      Int.cast_smul_eq_zsmul]
  exact GlobalTheory.T.kodairaSpencer_skew_dim_semisimple_two_roots k (HdR o₀.A) D.O ρ (fun c => (D.star c).unop) φ (Fil o₀.A) Z w (β b.ρ) ((D.tr : k) - β b.ρ) _ hsurj
    hadj hskew hnd hiso hdim hstab hcomm hq hne hwadj hZ hcount

end GlobalTheory.HTCount
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.principal_siegel_object_exists_charZero_lift : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : cycAway n →+* K) (c : SiegPre g n (zetaAway n) (spMap β)), c.Principal → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (βV : cycAway n →+* V) (π : V →+* K) (cV : SiegPre g n (zetaAway n) (spMap βV)), Function.Injective βV ∧ π.comp βV = β ∧ cV.Principal ∧ SiegPB c cV (spMap π) := by
  first | exact @GlobalTheory.SiegLift0.exists_lift_domain | exact GlobalTheory.SiegLift0.exists_lift_domain | (intros; apply GlobalTheory.SiegLift0.exists_lift_domain <;> assumption)
end

section

namespace GlobalTheory

theorem arithHilbertSamuel_of_principalisation :
    GlobalTheory.Published.Principalisation → GlobalTheory.Published.ArithHilbertSamuel :=
  fun h => GlobalTheory.T.arithHilbertSamuel_nef_of_ample (GlobalTheory.MixHt.arCalc_of_principalisation h) (GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation h)
    (GlobalTheory.SemiPullAll.semiPull_of_principalisation h)

end GlobalTheory
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylorModuliObject_potentiallyGoodReduction : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* K) (o : Obj b N (spMap β)), (2 * D.a < Module.finrank ℚ D.F ∨ (D.IsDivision ∧ D.n < 2 * D.m)) → GlobalTheory.SS.PotModel V K o.A (fun _ _ _ G _ => IsAbelianScheme G) := by
  first | exact @GlobalTheory.HTPotGood.potGood | exact GlobalTheory.HTPotGood.potGood | (intros; apply GlobalTheory.HTPotGood.potGood <;> assumption)
end
