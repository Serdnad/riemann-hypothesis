module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle115
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle001
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TestGroupPointExists
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle278
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle244
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeValuationAgree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle195
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSncCoordsOfLocal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle209
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

attribute [-instance] GlobalTheory.CompHt.fintypePsi in
theorem _root_.GlobalTheory.T.intersection_system_weight_right : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Sp ℂ ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Nonempty (MuFrameAt Hd w) ∧ ∀ d : MuFrameAt Hd w, (∃ s, Or.IsSmallPart d s) ∧ ∀ s, Or.IsSmallPart d s → (∀ τ (h : genPt Or.𝔐.ξ ⤳ centre z), (Or.𝔐.V (Or.sm τ)).IsFrameAt (s τ) ⟨centre z, h⟩) ∧ valAt Dc.y d.u w ≠ 0 ∧ (Or.𝔐.Interior z → ∀ Γ : CMType H → Matrix (Fin (Dc.N - Dc.j)) (Fin (Dc.N - Dc.j)) ℂ, (∀ τ, Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (s τ) (Γ τ)) → phMu Hd w = Real.log (‖valAt Dc.y d.u w‖ * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ Hd.aMu k) + (∑ τ, Real.log (Γ τ).det.re) / 2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.phMu_eq_log_small_blocks_abelian | exact GlobalTheory.CompanionTheory.Ar.Cusp.phMu_eq_log_small_blocks_abelian | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.phMu_eq_log_small_blocks_abelian <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT


theorem _root_.GlobalTheory.CompanionTheory.Relay.ordinary_curve_model_relay : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → GlobalTheory.CompanionTheory.Ar.GR.HodgeTateDatumStatement → GlobalTheory.CompanionTheory.Ar.GR.OrdinaryCurveStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (t₀ : CMType H ⊕ CMType H) (Sg : Type) [Fintype Sg] (e : Sg → CMType H ⊕ CMType H) (φ' : Equiv.Perm Sg) (F : Type) [Field F] [Fintype F] [CharP F p] (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) (w : O) (σ : Sg → F →+* IsLocalRing.ResidueField O), IsOrbit O 𝔐 p φ t₀ e φ' pq w σ → IsSec pq sc → ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (i : ∀ τ, (Fin (labelRk D (e τ)) → Ω) →ₗ[Ω] (Fin (D.p + D.q) → Ω)), (∀ τ : Sg, SeqHyp (CR O y c') (algebraMap O Ω w) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (dotDual (CR O y c') (coordLat O y (𝔐.HT p (e τ).swap) (b (e τ).swap) c')) (i τ) (qMap P (b (e τ).swap)) ∧ ∀ σE : E →+* Ω, (∀ a : 𝓞 E, σE (a : E) = 𝔐.emb (e τ) a) → DualSeq P σE (𝔐.R p - 2) (coordLat O y (𝔐.HT p (e τ)) (b (e τ)) c') (b (e τ)) (i τ)) → (chartD e b pq sc w P i).Base (CR O y c') p (algebraMap O Ω w) → ∀ (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C), IsTestPt p (CR O y c') RC → ∀ χ : Sg → F →*₀ C, (∀ τ a (o : O), IsLocalRing.residue O o = σ τ a → χ τ a - algebraMap O C o ∈ RC ∧ ∀ u ∈ RC, u * (χ τ a - algebraMap O C o) ≠ 1) → ∀ [DecidableEq F] [Fintype (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)] [DecidableEq (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.NAdd E (D.p + D.q) p)], ∀ (v : Valuation C NNReal), (∀ c, c ∈ RC ↔ v c ≤ 1) → v (p : C) < 1 → ∀ τ (hb : ((Fin (labelRk D (e τ)) → C) →ₗ[C] (Fin (D.p + D.q) → C))), Function.Injective hb → LinearMap.range hb = LinearMap.ker (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))) → (stdLat RC _).comap hb.toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).W τ → (∀ a ∈ ((chartD e b pq sc w P i).bc RC).W τ, hb a - GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (i τ) a ∈ mulLat (algebraMap O C w) (stdLat RC _)) → (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).map (GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt.bcLin C (qMap P (b (e τ).swap))).toAddMonoidHom = ((chartD e b pq sc w P i).bc RC).om τ ∧ (((chartD e b pq sc w P i).bc RC).hh RC p (fun a => χ τ a)).comap hb.toAddMonoidHom = divLat (algebraMap O C w) (((chartD e b pq sc w P i).bc RC).lie τ) := by
  first | exact @PositivityTheory.Xgn.test_group_point_exists | exact PositivityTheory.Xgn.test_group_point_exists
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FinAll

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem iotaMulti_coe_eq_det_smul {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {r : ℕ}
    {S : Submodule R M} (c : Module.Basis (Fin r) R S) (v : Fin r → S) :
    exteriorPower.ιMulti R r (fun i => (v i : M)) =
      c.det v • exteriorPower.ιMulti R r (fun i => (c i : M)) := by
  have h : (exteriorPower.ιMulti R r (M := M)).compLinearMap S.subtype =
      c.det.smulRight (exteriorPower.ιMulti R r (fun i => (c i : M))) := by
    refine Module.Basis.ext_alternating c fun i hi => ?_
    let σ : Equiv.Perm (Fin r) := Equiv.ofBijective i (Finite.injective_iff_bijective.1 hi)
    change ((exteriorPower.ιMulti R r (M := M)).compLinearMap S.subtype) (c ∘ σ) =
      c.det (c ∘ σ) • exteriorPower.ιMulti R r (fun i => (c i : M))
    rw [AlternatingMap.map_perm, AlternatingMap.map_perm, Module.Basis.det_self, smul_assoc, one_smul]
    rfl
  exact DFunLike.congr_fun h v

theorem exists_smul_iotaMulti {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {V : Type} [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (S : Submodule Ω V) {n : ℕ} (v : Fin n → V)
    (a : ⋀[Ω]^n V) (x : Cpt ξ) (α : Ω) (hα : α ≠ 0) (hv : LinearIndependent Ω v)
    (hS : Submodule.span Ω (Set.range v) = S)
    (h : (L.inter S).wedge n x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ c : Ω, a = c • exteriorPower.ιMulti Ω n v := by
  have hmem : α • a ∈ (L.inter S).wedge n x := by rw [h]; exact Submodule.mem_span_singleton_self _
  have key : ∀ y ∈ (L.inter S).wedge n x, ∃ c : Ω, y = c • exteriorPower.ιMulti Ω n v := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      let e : Module.Basis (Fin n) Ω (Submodule.span Ω (Set.range v)) := Module.Basis.span hv
      let b' : Fin n → Submodule.span Ω (Set.range v) := fun i => ⟨b i, by rw [hS]; exact (hb i).2⟩
      refine ⟨e.det b', ?_⟩
      have h1 := iotaMulti_coe_eq_det_smul e b'
      have h2 : (fun i => ((e i : Submodule.span Ω (Set.range v)) : V)) = v := by
        funext i; show ((Module.Basis.span hv i : Submodule.span Ω (Set.range v)) : V) = v i
        rw [Module.Basis.span_apply]
      rw [h2] at h1
      exact h1
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨d, rfl⟩ := hz
      exact ⟨c + d, by rw [add_smul]⟩
    | smul r y _ hy =>
      obtain ⟨c, rfl⟩ := hy
      exact ⟨(r : Ω) * c, by rw [Subring.smul_def, smul_smul]⟩
  obtain ⟨c, hc⟩ := key _ hmem
  refine ⟨α⁻¹ * c, ?_⟩
  rw [mul_smul, ← hc, smul_smul, inv_mul_cancel₀ hα, one_smul]

theorem norm_le_one_of_isIntegral (p : Nat.Primes) (R : Type) [CommRing R] (κ : R →+* ℂ_[p]) (x : R)
    (hx : IsIntegral ℤ x) : ‖κ x‖ ≤ 1 := by
  have hy : IsIntegral ℤ (κ x) := by
    convert map_isIntegral_int κ hx using 1 <;> first | exact Subsingleton.elim _ _ | rfl
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer (κ x) := hy.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖κ x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem mem_or_inv_mem {F : Type} [Field F] {O : Type} [CommRing O] (β : O →+* F) {p : Nat.Primes}
    (κ : F →+* ℂ_[p]) (h : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) (x : F) : x ∈ β.range ∨ x⁻¹ ∈ β.range := by
  by_cases hx : ‖κ x‖ ≤ 1
  · exact Or.inl ((h x).1 hx)
  · right
    apply (h _).1
    rw [map_inv₀, norm_inv]
    push_neg at hx
    exact inv_le_one_of_one_le₀ hx.le

theorem exists_frac {F : Type} [Field F] {O : Type} [CommRing O] [IsDomain O] (β : O →+* F)
    (hr : ∀ x : F, x ∈ β.range ∨ x⁻¹ ∈ β.range) (x : F) : ∃ a b : O, b ≠ 0 ∧ x * β b = β a := by
  rcases hr x with ⟨a, rfl⟩ | ⟨b, hb⟩
  · exact ⟨a, 1, one_ne_zero, by simp⟩
  · by_cases hx : x = 0
    · exact ⟨0, 1, one_ne_zero, by simp [hx]⟩
    · refine ⟨1, b, ?_, ?_⟩
      · rintro rfl; simp at hb; exact hx hb.symm
      · rw [hb, mul_inv_cancel₀ hx, map_one]

theorem norm_natCast_prime (p : Nat.Primes) : ‖(((p : ℕ) : ℂ_[p]))‖ = ((p : ℕ) : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[(p : ℕ)] ℂ_[(p : ℕ)]) (p : ℕ), norm_algebraMap', Padic.norm_p]

theorem dvd_prime {F : Type} [Field F] [CharZero F] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (β : O →+* F) {p : Nat.Primes}
    (κ : F →+* ℂ_[p]) (h : ∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) {ϖ : O} (hϖ : Irreducible ϖ) :
    ϖ ∣ ((p : ℕ) : O) := by
  have hnu : ¬ IsUnit ((p : ℕ) : O) := by
    rintro ⟨u, hu⟩
    have hmem : ((p : ℕ) : F)⁻¹ ∈ β.range := by
      refine ⟨(u⁻¹ : Oˣ), ?_⟩
      have h1 : β (u : O) * β ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      rw [hu, map_natCast] at h1
      exact (eq_inv_of_mul_eq_one_right h1)
    have hle := (h _).2 hmem
    rw [map_inv₀, map_natCast, norm_inv, norm_natCast_prime, inv_inv] at hle
    have h1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
    linarith
  have hm : ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact hm

theorem constClosed_of_isGeom {F : Type} [Field F] {Ω : Type} [Field Ω] {O : Type} [CommRing O]
    (β : O →+* F) (inc : F →+* Ω) (hβ : Function.Injective β)
    (hfr : ∀ x : F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a)
    (hg : ∀ x : Ω, (∃ f : Polynomial F, f ≠ 0 ∧ f.eval₂ inc x = 0) → x ∈ Set.range inc) :
    @ConstClosed O Ω _ _ (inc.comp β).toAlgebra := by
  letI : Algebra O Ω := (inc.comp β).toAlgebra
  intro a ha
  obtain ⟨f, hf0, hfa⟩ := ha
  obtain ⟨y, rfl⟩ := hg a ⟨f.map β, (Polynomial.map_ne_zero_iff hβ).2 hf0, by
    rw [Polynomial.eval₂_map]; exact hfa⟩
  obtain ⟨x', y', hy', e⟩ := hfr y
  refine ⟨x', y', hy', ?_⟩
  show inc y * inc (β y') = inc (β x')
  rw [← map_mul, e]

theorem exists_basis_of_finrank {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (S : Submodule K V) {n : ℕ} (h : Module.finrank K S = n) :
    ∃ v : Fin n → V, LinearIndependent K v ∧ Submodule.span K (Set.range v) = S := by
  let b := Module.finBasisOfFinrankEq K S h
  have hli : LinearIndependent K (S.subtype ∘ b) := b.linearIndependent.map' S.subtype S.ker_subtype
  refine ⟨S.subtype ∘ b, hli, ?_⟩
  rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem finConstAll : FinConstAll := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ p κ φ hτ hβ hnorm hsplit hN3 hgeom hflat hline
  have hr := mem_or_inv_mem β κ hnorm
  have hfr := exists_frac β hr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd : ϖ ∣ ((p : ℕ) : O) := dvd_prime β κ hnorm hϖ
  obtain ⟨hprop, hnormal, hover, hgf, hfd, hrk, hrk'⟩ :=
    GlobalTheory.T.proper_normal_compactification E H D l Xo c O β Y U Z τ hβ hfr hτ
  letI : Algebra O Z.Ω := (Z.inc.comp β).toAlgebra
  haveI := hfd
  haveI := hprop
  haveI : CharZero Z.Ω := (RingHom.charZero_iff Z.inc.injective).1 inferInstance
  let σ : E →+* Z.Ω := Z.inc.comp (τ.codRestrict c.F.toSubfield (c.conj τ) : E →+* c.F)
  let σ' : E →+* Z.Ω := Z.inc.comp
    ((ComplexEmbedding.conjugate τ).codRestrict c.F.toSubfield (c.conj _) : E →+* c.F)
  have hσ : ∀ b : 𝓞 E, σ (b : E) = Z.inc (tauIn c τ b) := fun b => rfl
  have hbar : ∀ a : 𝓞 E, σ' (a : E) = σ (H.bar a : 𝓞 E) := by
    intro a
    show Z.inc _ = Z.inc _
    congr 1
    apply Subtype.ext
    show (ComplexEmbedding.conjugate τ) (a : E) = τ ((H.bar a : 𝓞 E) : E)
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
  have hinv : ∀ a, H.bar (H.bar a) = a := by
    intro a
    apply RingOfIntegers.ext
    apply τ.injective
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, H.bar_eq, IsCMField.complexEmbedding_complexConj,
      Complex.conj_conj]
  have heig : HT.eigSp Z.ρ σ = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) := rfl
  have heig' : HT.eigSp Z.ρ σ' = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) := rfl
  obtain ⟨v, hvli, hvsp⟩ := exists_basis_of_finrank (HT.eigSp Z.ρ σ) (heig ▸ hrk)
  obtain ⟨w, hwli, hwsp⟩ := exists_basis_of_finrank (HT.eigSp Z.ρ σ') (heig' ▸ hrk')
  obtain ⟨𝓗, hdeg⟩ := GlobalTheory.T.eigen_line_p_adic_bound E H D l Xo c O β Y U Z τ ϖ (p : ℕ) hϖ p.2 hdvd hβ hr hsplit hN3
  obtain ⟨u, hu, -, -⟩ := GlobalTheory.T.hermitian_signature_basis E Z.Ω Z.V Z.ρ 𝓗.ρH H.bar σ σ' D.p D.q v w 𝓗.act_fst 𝓗.act_inr
    hbar hinv hvli hvsp hwli hwsp
  obtain ⟨-, a, b, ⟨ha0, hb0, hco⟩, hrep⟩ := hflat
  let x₀ : Cpt (Z.ξ₀ ≫ Y.j) := ⟨genPt (Z.ξ₀ ≫ Y.j), specializes_rfl⟩
  have hx₀ : x₀ ∈ Z.genFib := ⟨Y.jQ (genPt Z.ξ₀), rfl⟩
  obtain ⟨α₁, β₁, hα₁, hβ₁, hA, hB, -⟩ := hco x₀ hx₀
  obtain ⟨α, rfl⟩ := exists_smul_iotaMulti Z.M.lat (HT.eigSp Z.ρ σ) v a x₀ α₁ hα₁ hvli hvsp hA
  obtain ⟨κ', rfl⟩ := exists_smul_iotaMulti Z.M.lat (HT.eigSp Z.ρ σ') w b x₀ β₁ hβ₁ hwli hwsp hB
  have hκ' : κ' ≠ 0 := fun h => hb0 (by rw [h, zero_smul])
  have hgfe : Z.genFib = genFibre O (Z.ξ₀ ≫ Y.j) := Set.ext fun x => hgf x
  have hline' : IsLineGenOn (Z.M.lat.inter (HT.eigSp Z.ρ σ)) (Z.M.lat.inter (HT.eigSp Z.ρ σ')) D.p D.q
      (α • exteriorPower.ιMulti Z.Ω D.p v) (κ' • exteriorPower.ιMulti Z.Ω D.q w)
      (genFibre O (Z.ξ₀ ≫ Y.j)) := by
    rw [← hgfe]; exact ⟨ha0, hb0, hco⟩
  have hinjO : Function.Injective (algebraMap O Z.Ω) := Z.inc.injective.comp hβ
  have hσrange : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O Z.Ω).range := by
    intro a
    obtain ⟨o, ho⟩ := (hnorm (tauIn c τ a)).1
      (norm_le_one_of_isIntegral p (𝓞 E) (κ.comp (tauIn c τ)) a (RingOfIntegers.isIntegral a))
    exact ⟨o, by show Z.inc (β o) = Z.inc (tauIn c τ a); rw [ho]⟩
  have hcc : ConstClosed O Z.Ω := constClosed_of_isGeom β Z.inc hβ hfr hgeom
  obtain ⟨M, k, hM, hord⟩ := GlobalTheory.T.hodge_lattice_valuation_agree Y.X Z.Ω (Z.ξ₀ ≫ Y.j) E Z.V Z.M.lat Z.ρ H.bar D.p D.q 𝓗 σ σ'
    v w u α κ' O Y.s ϖ hϖ hinjO hover Z.gen hnormal hcc hσrange hbar hinv hvli hvsp hwli hwsp hu (hdeg σ) hline'
  exact GlobalTheory.T.eigen_line_p_adic_frame E H D l Xo c O β Y U Z τ ϖ p κ φ 𝓗 σ v w u α κ' M k hτ hϖ hβ hnorm hσ hvli hvsp hwli
    (hwsp.trans heig') hu hM hord hκ' hrep hline

end GlobalTheory.CompanionTheory.Ar.Flat.FinAll
end
end

section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.Geo.SncCoordsSide

theorem coordsStatement_side : ReciprocityTheory.ChartRestriction.G.Geo.ResK.CoordsStatement :=
  GlobalTheory.CompanionTheory.Geo.SncCoords.coordsStatement

end GlobalTheory.CompanionTheory.Geo.SncCoordsSide
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem moduli_schemes_exist : N1ab := GlobalTheory.Moduli.moduli_scheme_exists

end GlobalTheory.CompanionTheory.Ar.Top
end
