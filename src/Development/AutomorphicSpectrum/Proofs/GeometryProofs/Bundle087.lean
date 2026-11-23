module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle076
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductConjugate
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle078
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
import Mathlib.Tactic.TypeStar
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {K : Type} {ι : K → Type} {R : Type} [CommRing R]

def dualRev {r : ℕ} (Q : LocPair ι R (Fin r)) : LocPair ι R (Fin r) :=
  ⟨fun i => -Q.x (Fin.rev i), fun i => -Q.x' (Fin.rev i), fun i => Q.g (Fin.rev i), fun i => Q.f (Fin.rev i)⟩

def labelPair (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (labelRk D s))
  | .inl τ => T.comp fun i => (τ, Fin.castAdd D.q i)
  | .inr τ => dualRev (T.comp fun i => (τ, Fin.natAdd D.p i))

def omPair (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (labelRk D s.swap)) :=
  fun s => dualRev (labelPair D T s.swap)

def omPairM (D : Datum H) (T : LocPair ι R (CMType H × Fin (D.p + D.q))) :
    ∀ s : CMType H ⊕ CMType H, LocPair ι R (Fin (Sum.elim (fun _ : CMType H => D.q) (fun _ : CMType H => D.p) s))
  | .inl τ => omPair D T (.inl τ)
  | .inr τ => omPair D T (.inr τ)

theorem dualRev_dualRev {r : ℕ} (Q : LocPair ι R (Fin r)) : dualRev (dualRev Q) = Q := by
  obtain ⟨x, x', f, g⟩ := Q
  simp [dualRev, Fin.rev_rev]

theorem map_map {R' R'' : Type} [CommRing R'] [CommRing R''] {σ : Type} (T : LocPair ι R σ) (ψ : R →+* R')
    (ψ' : R' →+* R'') : (T.map ψ).map ψ' = T.map (ψ'.comp ψ) := by
  obtain ⟨x, x', f, g⟩ := T
  simp [LocPair.map, MvPolynomial.map_map]

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

abbrev XQ (X : Scheme.{0}) : Scheme.{0} := pullback (toZ X) (toZ (Sp ℚ))

abbrev XQ.fst (X : Scheme.{0}) : XQ X ⟶ X := pullback.fst _ _

abbrev XQ.snd (X : Scheme.{0}) : XQ X ⟶ Sp ℚ := pullback.snd _ _

def toXQ {X : Scheme.{0}} {F : Type} [Field F] [CharZero F] (x : Sp F ⟶ X) : Sp F ⟶ XQ X :=
  pullback.lift x (spMap (algebraMap ℚ F)) (specULiftZIsTerminal.hom_ext _ _)

@[simp] theorem toXQ_fst {X : Scheme.{0}} {F : Type} [Field F] [CharZero F] (x : Sp F ⟶ X) :
    toXQ x ≫ XQ.fst X = x := pullback.lift_fst _ _ _

def evalAt {S : Scheme.{0}} (U : S.Opens) (f : Γ(S, U)) (z : Sp ℂ ⟶ S) (hz : centre z ∈ U) : ℂ :=
  (Scheme.stalkClosedPointTo z).hom (S.presheaf.germ U (centre z) hz f)

def anTop (S : Scheme.{0}) : TopologicalSpace (Sp ℂ ⟶ S) :=
  TopologicalSpace.generateFrom
    {A | ∃ (U : S.Opens) (f : Γ(S, U)) (V : Set ℂ), IsOpen V ∧ A = {z | ∃ hz : centre z ∈ U, evalAt U f z hz ∈ V}}

section Good

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω} {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  {M : LieModel G ξ Li}

def GoodAt (h : LieMetric M y) (C : ℝ) {L : Type} [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) {GK : Over (Sp L)}
    [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK) : Prop :=
  letI := τ.addCommGroup
  ∃ (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)),
    ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT →
    ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier),
      IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ ε : Fin r → B.carrier,
      (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt (ε a)).left)) →
      ∀ (σ : L →+* ℂ) (w : Fin r → ℂ),
        C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ∧
        sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2

end Good

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

theorem rootLine_unitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (r : CMType H × Fin (D.p + D.q)) (q : Cpt 𝔐.ξ) (cc : (k : K) → J k) (b : Fin (labelRk D (HodgeCpt.rootIdx D r).1) → 𝔐.Li) (t : Ω), Fl.RootLines xdeg e → InChart 𝔐.ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) cc q → (∀ j, flagStep Ω b j = flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) j) → (𝔐.V (HodgeCpt.rootIdx D r).1).IsFrameAt b q → b (HodgeCpt.rootIdx D r).2 - t • Fl.b (HodgeCpt.rootIdx D r).1 (HodgeCpt.rootIdx D r).2 ∈ flagStep Ω (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2 → unitAt 𝔐.ξ q ((∏ k, y ⟨k, cc k⟩ ^ xdeg r k) * e r / t ^ HodgeCpt.rootSgn D r) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 Fl xdeg e r q cc b t hd hq hF hL hc
  have ht := FlagModel.gr_isGenAt _ b (Fl.b (HodgeCpt.rootIdx D r).1) q hL hF _ t hc
  have hT : (Fl.rootLat r).IsGenAt q (t ^ HodgeCpt.rootSgn D r) := by
    simpa [HodgeCpt.Flag.rootLat] using FlagModel.tens_isGenAt
      (fun _ : Unit => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
      (fun _ => HodgeCpt.rootSgn D r) q (fun _ => t) fun _ => ht
  obtain ⟨he, h⟩ := hd r
  have h1 := h q (Set.mem_univ _) cc hq
  have hy : (∏ k, y ⟨k, cc k⟩ ^ xdeg r k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k hk => zpow_ne_zero _ (Finset.prod_ne_zero_iff.1 hq.1 k hk)
  have hW : (Fl.rootLat r).IsGenAt q ((∏ k, y ⟨k, cc k⟩ ^ xdeg r k) * e r) := ⟨mul_ne_zero hy he, h1⟩
  have hw0 := hW.1
  have ht0 := hT.1
  refine ⟨div_ne_zero hw0 ht0, ?_, ?_⟩
  · simpa using FlagModel.zpow_ratio _ q _ _ hT hW 1
  · simpa using FlagModel.zpow_ratio _ q _ _ hW hT 1

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace GlobalTheory.CompanionTheory.Ar.Br.FinPlace

section Valued

variable {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {N : Type*} [NormedField N]

theorem val_lt_one_iff (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) (a : F) :
    v a < 1 ↔ ‖κ a‖ < 1 := by
  by_cases ha : a = 0
  · simp [ha]
  have hv : 0 < v a := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr ha)
  have hn : 0 < ‖κ a‖ := norm_pos_iff.mpr ((map_ne_zero κ).mpr ha)
  have e := h a⁻¹
  rw [map_inv₀, map_inv₀, norm_inv, inv_le_one₀ hv, inv_le_one₀ hn] at e
  rw [← not_le, ← not_le, e]

theorem norm_le_of_val_le (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) {a b : F} (hb : b ≠ 0)
    (hab : v a ≤ v b) : ‖κ a‖ ≤ ‖κ b‖ := by
  have hv : 0 < v b := zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr hb)
  have hn : 0 < ‖κ b‖ := norm_pos_iff.mpr ((map_ne_zero κ).mpr hb)
  have e := (h (a / b)).mp (by rw [map_div₀]; exact div_le_one_of_le₀ hab zero_le)
  rw [map_div₀, norm_div] at e
  exact (div_le_one hn).mp e

theorem norm_eq_of_val_eq (v : Valuation F Γ) (κ : F →+* N) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1) {a b : F} (hb : b ≠ 0)
    (hab : v a = v b) : ‖κ a‖ = ‖κ b‖ := by
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact (Valuation.ne_zero_iff v).mpr hb hab.symm
  exact le_antisymm (norm_le_of_val_le v κ h hb hab.le) (norm_le_of_val_le v κ h ha hab.ge)

end Valued

theorem norm_natCast_lt_one_iff (q : Nat.Primes) (n : ℕ) : ‖(n : ℂ_[q])‖ < 1 ↔ (q : ℕ) ∣ n := by
  have e : ‖(n : ℂ_[q])‖ = ‖(n : ℚ_[q])‖ := by
    have h1 := PadicComplex.norm_extends (q : ℕ) ((n : ℚ_[q]) : PadicAlgCl q)
    have h2 := PadicAlgCl.norm_extends (q : ℕ) (n : ℚ_[q])
    simpa using h1.trans h2
  rw [e]
  exact Padic.norm_natCast_lt_one_iff

theorem prime_eq {F : Type*} [Field F] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    {p q : Nat.Primes} (κ : F →+* ℂ_[p]) (κ₀ : F →+* ℂ_[q]) (h : ∀ a, v a ≤ 1 ↔ ‖κ a‖ ≤ 1)
    (h₀ : ∀ a, v a ≤ 1 ↔ ‖κ₀ a‖ ≤ 1) : p = q := by
  have h1 : ‖κ ((p : ℕ) : F)‖ < 1 := by
    rw [map_natCast, norm_natCast_lt_one_iff]
  have h2 : ‖κ₀ ((p : ℕ) : F)‖ < 1 := (val_lt_one_iff v κ₀ h₀ _).mp ((val_lt_one_iff v κ h _).mpr h1)
  rw [map_natCast, norm_natCast_lt_one_iff] at h2
  exact Subtype.ext (((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp h2).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem hasFinNorm_of_isometry {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ : FrameFn Xo c} {p : Nat.Primes}
    {κ κ' : c.F →+* ℂ_[p]} {t : ℝ} (g : ℂ_[p] ≃+* ℂ_[p]) (hg : ∀ z, ‖g z‖ = ‖z‖) (hκ : ∀ a, g (κ a) = κ' a)
    (h : HasFinNorm U τ φ p κ t) : HasFinNorm U τ φ p κ' t := by
  have hs : ∀ z, ‖g.symm z‖ = ‖z‖ := fun z => by
    rw [← hg (g.symm z), RingEquiv.apply_symm_apply]
  intro V K _ _ _ _ _ _ j β y v w T tK m m' hj hjβ hF hv hw
  have e := h V K ((g.symm : ℂ_[p] →+* ℂ_[p]).comp j) β y v w T tK m m'
    (fun a => by
      rw [← hj a]
      simp only [RingHom.comp_apply, RingHom.coe_coe, hs])
    (by
      ext a
      have h1 : j (β a) = κ' a := by rw [← hjβ]; rfl
      simp only [RingHom.comp_apply, RingHom.coe_coe, h1, ← hκ, RingEquiv.symm_apply_apply]) hF hv hw
  simpa only [RingHom.comp_apply, RingHom.coe_coe, hs] using e

theorem exists_rho_at (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) [NumberField c.F]
    (hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t)
    (la : HeightOneSpectrum (𝓞 c.F)) :
    ∃ r : ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (π : c.F),
      (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) →
      HasFinNorm U τ φ p κ (r * Real.log ‖κ π‖) := by
  by_cases hex : ∃ (p₀ : Nat.Primes) (κ₀ : c.F →+* ℂ_[p₀]) (π₀ : c.F),
      (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ₀ a‖ ≤ 1) ∧ la.valuation c.F π₀ = WithZero.exp (-1 : ℤ)
  · obtain ⟨p₀, κ₀, π₀, hκ₀, hπ₀⟩ := hex
    obtain ⟨t₀, ht₀⟩ := hfin p₀ κ₀
    have hne : π₀ ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ₀
      exact WithZero.exp_ne_zero hπ₀.symm
    have hlt : ‖κ₀ π₀‖ < 1 := (val_lt_one_iff _ κ₀ hκ₀ π₀).mp (by
      rw [hπ₀, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num)
    have hpos : 0 < ‖κ₀ π₀‖ := norm_pos_iff.mpr ((map_ne_zero κ₀).mpr hne)
    have hlog : Real.log ‖κ₀ π₀‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos hlt.ne
    refine ⟨t₀ / Real.log ‖κ₀ π₀‖, fun p κ π hκ hπ => ?_⟩
    have hp : p = p₀ := prime_eq (la.valuation c.F) κ κ₀ hκ hκ₀
    subst hp
    obtain ⟨g, hg, hgκ⟩ := GlobalTheory.T.padic_embeddings_conjugate_of_units c.F p κ₀ κ (fun a => (hκ₀ a).symm.trans (hκ a))
    have e : ‖κ π‖ = ‖κ₀ π₀‖ := by
      rw [norm_eq_of_val_eq _ κ hκ hne (hπ.trans hπ₀.symm), ← hgκ, hg]
    rw [e, div_mul_cancel₀ _ hlog]
    exact hasFinNorm_of_isometry g hg hgκ ht₀
  · exact ⟨0, fun p κ π h1 h2 => (hex ⟨p, κ, π, h1, h2⟩).elim⟩

theorem exists_rho : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c), (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t) → ∃ ρ : HeightOneSpectrum (𝓞 c.F) → ℝ, ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm U τ φ p κ (ρ la * Real.log ‖κ π‖) := by
  intro E _ _ _ H D l Xo c _ U τ φ hfin
  choose ρ hρ using exists_rho_at U τ φ hfin
  exact ⟨ρ, fun p κ la π h1 h2 => hρ la p κ π h1 h2⟩

end GlobalTheory.CompanionTheory.Ar.Br.FinPlace
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.IntOpen

theorem epi_of_mono_spMap {O F : Type} [CommRing O] [CommRing F] (β : O →+* F) (h : Mono (spMap β))
    {T : Type} [CommRing T] (g₁ g₂ : F →+* T) (e : g₁.comp β = g₂.comp β) : g₁ = g₂ := by
  have h1 : spMap g₁ ≫ spMap β = spMap g₂ ≫ spMap β := by
    rw [← spMap_comp, ← spMap_comp, e]
  have h2 := Spec.map_injective ((cancel_mono (spMap β)).1 h1)
  exact congrArg CommRingCat.Hom.hom h2

theorem lift_local {R : CommRingCat} [IsLocalRing R] {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (g : Spec R ⟶ X) (h : g (IsLocalRing.closedPoint R) ∈ Set.range j) : ∃ u, u ≫ j = g := by
  have hr : Set.range g ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    have hs : p ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint p
    exact (hs.map g.continuous).mem_open j.isOpenEmbedding.isOpen_range h
  exact ⟨IsOpenImmersion.lift j g hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem interior_iff_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (z : Sp ℂ ⟶ A.X), Mono (spMap β) → Mono Y.j ∧ (A.Interior z ↔ ∃ u : Spec (A.X.presheaf.stalk (centre z)) ⟶ Xo.XF c, u ≫ Y.j = A.X.fromSpecStalk (centre z) ≫ A.f) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A z hβ
  have hab : ∀ x : A.X, A.f x ∈ abLocus Y.t.G ↔ x ∈ abLocus A.t.G :=
    abLocus_pullback abLocusOne Y.t.semi A.m.cart.1
  refine ⟨?_, ?_⟩
  · have : IsOpenImmersion Y.jQ := Y.jQ_open
    unfold Model.j; infer_instance
  constructor
  · intro hx
    have hx' : A.f (centre z) ∈ abLocus Y.t.G := (hab _).2 hx
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : NumberField c.F := {}
    haveI : IsReduced A.X := by
      have : ∀ x : A.X, _root_.IsReduced (A.X.presheaf.stalk x) := fun x => by
        have := (A.normal x).1
        infer_instance
      exact isReduced_of_isReduced_stalk A.X
    let g : Spec (A.X.presheaf.stalk (centre z)) ⟶ Sp O := A.X.fromSpecStalk (centre z) ≫ A.f ≫ Y.s
    let θ : O →+* A.X.presheaf.stalk (centre z) := (Spec.preimage g).hom
    have hk : ∀ a, β a = 0 → θ a = 0 := fun a ha =>
      GlobalTheory.T.generic_vanishing_stalk_vanishing A.X Ω O A.ξ A.all (A.f ≫ Y.s) (A.cst.comp β) A.cst_over (centre z) a (by simp [ha])
    have hu : ∀ b, β b ≠ 0 → IsUnit (θ b) := fun b hb =>
      GlobalTheory.T.local_hom_char_zero_units O c.F _ ℂ β θ (Scheme.stalkClosedPointTo z).hom (Scheme.isLocalHom_stalkClosedPointTo' z) hk b hb
    obtain ⟨χ, hχ⟩ := GlobalTheory.T.extend_to_fraction_field O c.F _ β θ (GlobalTheory.T.epi_ring_hom_field_closure O c.F β (fun T _ g₁ g₂ e => epi_of_mono_spMap β hβ g₁ g₂ e)) hu hk
    have w : (A.X.fromSpecStalk (centre z) ≫ A.f) ≫ Y.s = spMap χ ≫ spMap β := by
      rw [← spMap_comp, hχ, Category.assoc]
      change g = _
      rw [← Spec.map_preimage g]
      rfl
    haveI : IsOpenImmersion Y.jQ := Y.jQ_open
    obtain ⟨u, hu⟩ := lift_local Y.jQ (pullback.lift _ _ w) (by
      rw [← Y.ab_gen]
      show (pullback.lift _ _ w ≫ pullback.fst _ _) _ ∈ abLocus _
      rw [pullback.lift_fst]
      have e1 : (A.X.fromSpecStalk (centre z) ≫ A.f) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z))) = A.f (centre z) := by
        show A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = _
        rw [Scheme.fromSpecStalk_closedPoint]
      exact e1 ▸ hx')
    refine ⟨u, ?_⟩
    rw [Model.j, ← Category.assoc, hu, pullback.lift_fst]
  · rintro ⟨u, hu⟩
    show centre z ∈ abLocus A.t.G
    rw [← hab]
    have h1 : A.f (centre z) = Y.j (u (IsLocalRing.closedPoint _)) := by
      have e1 := congrArg (fun φ : Spec (A.X.presheaf.stalk (centre z)) ⟶ Y.X => φ (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) hu
      change Y.j (u (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) at e1
      rw [Scheme.fromSpecStalk_closedPoint] at e1
      exact e1.symm
    rw [h1]
    have h2 : Y.jQ (u (IsLocalRing.closedPoint _)) ∈ Set.range Y.jQ := ⟨_, rfl⟩
    rw [← Y.ab_gen] at h2
    exact h2

end GlobalTheory.CompanionTheory.Ar.IntOpen
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Flat.KonstReg

theorem exists_const_stalk : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : Cpt 𝔐.ξ), (∀ n : ℕ, n ≠ 0 → IsUnit ((n : 𝔐.X.presheaf.stalk p.1))) → ∃ g₀ : c.F →+* 𝔐.X.presheaf.stalk p.1, (genMap 𝔐.ξ p).comp g₀ = 𝔐.cst := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 p hunit
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := ⟨⟩
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have hs : 𝔐.ξ ≫ (𝔐.f ≫ Y.s) = Spec.map (CommRingCat.ofHom (algebraMap (𝓞 c.F) Ω)) := 𝔐.cst_over
  let h : 𝓞 c.F →+* 𝔐.X.presheaf.stalk p.1 :=
    (𝔐.X.presheaf.germ ⊤ p.1 trivial).hom.comp
      ((𝔐.f ≫ Y.s).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (𝓞 c.F))).inv.hom)
  have hgen : ∀ o : 𝓞 c.F, genMap 𝔐.ξ p (h o) = 𝔐.cst (algebraMap (𝓞 c.F) c.F o) :=
    fun o => Flat.ConstReg.genMap_germ_const 𝔐.ξ (𝔐.f ≫ Y.s) hs p o
  have hu : ∀ o : 𝓞 c.F, o ≠ 0 → IsUnit (h o) := by
    intro o ho
    have hI : (Ideal.span {o}).comap (algebraMap ℤ (𝓞 c.F)) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ho (Ideal.mem_span_singleton_self o) (Algebra.IsIntegral.isIntegral o)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hn
    have hnat : IsUnit ((n.natAbs : ℕ) : 𝔐.X.presheaf.stalk p.1) := hunit _ (Int.natAbs_ne_zero.mpr hn0)
    have hint : IsUnit (h (algebraMap ℤ (𝓞 c.F) n)) := by
      rw [eq_intCast (algebraMap ℤ (𝓞 c.F)), map_intCast]
      rcases Int.natAbs_eq n with hn' | hn'
      · rw [hn']
        simpa using hnat
      · rw [hn']
        simpa using hnat
    exact isUnit_of_dvd_unit (map_dvd h hn) hint
  refine ⟨IsLocalization.lift (M := nonZeroDivisors (𝓞 c.F)) (S := c.F)
    (fun z => hu z.1 (nonZeroDivisors.ne_zero z.2)), ?_⟩
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F))
  ext o
  simp only [RingHom.comp_apply, IsLocalization.lift_eq]
  exact hgen o

end GlobalTheory.CompanionTheory.Ar.Flat.KonstReg
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar


open LieTangent in
theorem valAt_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] (zL : Sp L ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre zL) (g₀ : c.F →+* 𝔐.X.presheaf.stalk (centre zL)), (genMap 𝔐.ξ ⟨centre zL, h⟩).comp g₀ = 𝔐.cst → ∀ (s : CMType H ⊕ CMType H) (e : 𝔐.Li) (v : epsAt zL ⟶ 𝔐.t.G) (a : 𝓞 E), e ∈ 𝔐.Vgen s → 𝔐.M.ValAt zL e v → (v ≫ 𝔐.t.act.act a).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul ((Scheme.stalkClosedPointTo zL).hom (g₀ (labelEmb c s a))))) ≫ v.left := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 L _ zL h g₀ hg s e v a he hv
  obtain ⟨h', v₀, hext, rfl⟩ := (𝔐.M.valAt_iff zL e v).1 hv
  have hgen : genMap 𝔐.ξ ⟨centre zL, h⟩ (g₀ (labelEmb c s a)) = 𝔐.emb s a :=
    DFunLike.congr_fun hg (labelEmb c s a)
  have hρ : 𝔐.ρ a e = 𝔐.emb s a • e := by
    have h1 : e ∈ LinearMap.ker (𝔐.ρ a - 𝔐.emb s a • LinearMap.id) :=
      (Submodule.mem_iInf _).1 he a
    rw [LinearMap.mem_ker] at h1
    simpa [sub_eq_zero] using h1
  have hext' := (𝔐.M.extends_iff _ _ _).1 hext
  have h1 : 𝔐.M.Extends ⟨centre zL, h⟩ (𝔐.emb s a • e) (v₀ ≫ 𝔐.t.act.act a) := by
    rw [LieModel.extends_iff]
    refine ⟨?_, ?_⟩
    · rw [isTanAt_iff, ← Category.assoc, (isTanAt_iff _).1 hext'.1]
      haveI := 𝔐.t.act.hom a
      exact one_comp _
    · rw [← hρ, 𝔐.act a e, hext'.2, Category.assoc]
  have h2 := hext.smul (g₀ (labelEmb c s a))
  rw [hgen] at h2
  have key := h1.unique (𝔐.tie.gen.inj _) h2
  have e1 : epsBase _ (spec_centre zL) ≫ v₀ ≫ 𝔐.t.act.act a =
      epsScale zL ((Scheme.stalkClosedPointTo zL).hom (g₀ (labelEmb c s a))) ≫ epsBase _ (spec_centre zL) ≫ v₀ := by
    rw [key, ← Category.assoc, base_scale, Category.assoc]
    rfl
  exact congrArg (fun q => q.left) ((Category.assoc _ _ _).trans e1)

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

theorem _root_.GlobalTheory.T.coherent_lattice_chart_span : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat M.ξ E), L.IsCohOn Set.univ → ∃ (d n : ℕ) (z : Fin n → E), ∀ c (p : Cpt M.ξ), InChart M.ξ x c p → L p = Submodule.span (regAt M.ξ p) (Set.range fun k => (x c ^ d)⁻¹ • z k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lat_twist_globally_generated | exact GlobalTheory.CompanionTheory.Ar.lat_twist_globally_generated | (intros; apply GlobalTheory.CompanionTheory.Ar.lat_twist_globally_generated <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hodge_inner_product_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (v w : epsAt z ⟶ t.G) (v' w' : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ t.G) (c : ℂ), v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left → w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left → HodgeIP t.G t.PP.L z v w c → HodgeIP t.G t.PP.L (spMap (starRingEnd ℂ) ≫ z) v' w' (starRingEnd ℂ c) := by
  exact @GlobalTheory.CompanionTheory.Ar.HodgeConj.hodgeInnerProduct_conj_abelianScheme
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.hodge_lattice_span_independent : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r) (σ : E →+* Ω) (u : Fin r → V × Module.Dual Ω V), (∀ (p : Cpt ξ) (a : 𝓞 E), σ (a : E) ∈ regAt ξ p) → LinearIndependent Ω u → Submodule.span Ω (Set.range u) = HT.eigSp 𝓗.ρH σ → (𝓗.quot σ).IsVB r (HT.eigSp 𝓗.ρH σ) ∧ (detLat (𝓗.quot σ) u).IsVB 1 ⊤ ∧ ∀ (p : Cpt ξ) (A : Matrix (Fin r) (Fin r) Ω), (𝓗.quot σ).IsFrameAt (fun i => ∑ j, A i j • u j) p → (detLat (𝓗.quot σ) u).IsGenAt p A.det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.HodgeLat.quot_det_bundle | exact GlobalTheory.CompanionTheory.Ar.Flat.HodgeLat.quot_det_bundle | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.HodgeLat.quot_det_bundle <;> assumption)
end
