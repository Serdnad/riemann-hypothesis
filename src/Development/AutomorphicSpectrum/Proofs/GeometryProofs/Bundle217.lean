module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle214
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle138
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle122
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle213
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle177
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle108
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle187
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle146
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle191
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle212
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle114
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle149
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle154
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle010
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.isConnected_zeroSet_uniformizer : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ConstClosed O Ω → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isConnected_zeroSet_of_isProper | exact GlobalTheory.CompanionTheory.Ar.Flat.isConnected_zeroSet_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isConnected_zeroSet_of_isProper <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem unitAt_of_pow_eq_one {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} (hN : Flat.NormalCpt ξ)
    {N : ℕ} (hN0 : N ≠ 0) {a : Ω} (ha : a ^ N = 1) (q : Cpt ξ) : unitAt ξ q a :=
  Flat.ZUnit.of_pow_of_normal hN hN0 (by rw [ha]; exact Flat.ZUnit.one)

theorem exists_full_level_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (K Ω : Type) [Field K] [Field Ω] [CharZero Ω] (i : K →+* Ω) (y : Sp K ⟶ Xo.XF c) (N : ℕ) (z : Ωˣ) (ev : D.La → (Over.mk (spMap i ≫ y ≫ Y.j) ⟶ Y.t.G)), 1 ≤ N → IsFullLevelAt D Y.t (spMap i ≫ y ≫ Y.j) N z ev → ∀ (X : Scheme.{0}) (ξ : Sp Ω ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ f : X ⟶ Y.X, ξ ≫ f = spMap i ≫ y ≫ Y.j → ∃ (t : SAB H X) (_ : SABMap t Y.t f) (ev' : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev' ∧ FullTorsion t.G ξ N ∧ ∀ q : Cpt ξ, unitAt ξ q (z : Ω) := by
  intro E _ _ _ H D l Xo c Y K Ω _ _ _ i y N z ev hN hlev X ξ _ hnorm f hf
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull f Y.t
  have hid : ξ ≫ f = spMap (RingHom.id Ω) ≫ spMap i ≫ y ≫ Y.j := by
    rw [hf]
    have : spMap (RingHom.id Ω) = 𝟙 _ := by simp [spMap]
    rw [this, Category.id_comp]
  obtain ⟨ev', hev', -⟩ := GlobalTheory.T.full_level_structure_pullback E H D Y.X X Y.t t f m Ω Ω (RingHom.id Ω) (spMap i ≫ y ≫ Y.j) ξ hid N z ev hlev
  have hz : Units.map (RingHom.id Ω).toMonoidHom z = z := by ext; rfl
  rw [hz] at hev'
  obtain ⟨hprim, -, -, -, -, hfull, -⟩ := GlobalTheory.T.full_level_structure_properties E H D X t Ω ξ N hN z ev' hev'
  refine ⟨t, m, ev', hev', hfull, fun q => ?_⟩
  have hpow : (z : Ω) ^ N = 1 := by
    have := congrArg Units.val hprim.pow_eq_one
    simpa using this
  exact unitAt_of_pow_eq_one hnorm (by omega) hpow q

end GlobalTheory.CompanionTheory.Ar.XR
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_flatHerm_hodgeCpt_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ) (e : CMType H × Fin (D.p + D.q) → Ω) (τ : CMType H) (F' : Type) [Field F'] [NumberField F'] (ψ : F' →+* Ω) (A : HermLine J) (c₀ : Ω) (r : HeightOneSpectrum (𝓞 F') →₀ ℚ) (cinf : (F' →+* ℂ) → ℝ), Fl.RootLines xdeg e → A.a = ∑ i, xdeg (τ, i) → Birational y → IsConjInvariantH A → c₀ ≠ 0 → (∀ p ∈ genFibre ℤ 𝔐.ξ, (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))).IsGenAt p (c₀ * ∏ i, e (τ, i))) → (∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt 𝔐.ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt 𝔐.ξ p) → OrderAt (lineLat (𝔐.V (.inl τ)) (𝔐.V (.inr τ)) (labelRk D (.inl τ)) (labelRk D (.inr τ)) (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ)))) (c₀ * ∏ i, e (τ, i)) (ψ π) m k p) → (∀ σ, 0 < cinf σ) → (∀ (σ : F' →+* ℂ) z (g h : MRing J) (dg dh : K → ℕ), PtOver y ψ σ z → IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) - dh k = A.a k) → aeval y g = c₀ * aeval y h → ‖evC z g‖ = cinf σ * A.h z * ‖evC z h‖) → OverInt y ψ ∧ ∃ Sf : FlatHerm y ψ A, Sf.ht = ((r.sum fun v q => (q : ℝ) * Real.log (Ideal.absNorm v.asIdeal)) - ∑ σ : F' →+* ℂ, Real.log (cinf σ)) / (Module.finrank ℚ F' : ℝ) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl xdeg e τ F' _ _ ψ A c₀ r cinf hR hA hB hC hc₀ hgen hZ hcinf hnorm
  have hN : NormalCpt 𝔐.ξ := XR.normalCpt_of_isCptGen 𝔐.tie.gen 𝔐.normal
  have hO : OverInt y ψ := overInt_of_normalCpt 𝔐.tie hN ψ
  have hD := GlobalTheory.T.hodge_cpt_flag_degree E H D l Xo c O β Y S Ω K J y 𝔐 Fl xdeg e τ hR
  rw [← hA] at hD
  refine ⟨hO, GlobalTheory.T.birational_lattice_height_formula K J Ω F' y ψ 𝔐.X 𝔐.ξ Ω _ (∏ i, e (τ, i)) c₀ A r cinf hO hB hC 𝔐.tie hN hD hc₀
    (fun p => ?_) hcinf hnorm⟩
  by_cases hp : p ∈ genFibre ℤ 𝔐.ξ
  · exact Or.inl ⟨cst_mem_regAt_of_genFibre hN ψ hp, orderAt_one_zero.2 (hgen p hp)⟩
  · obtain ⟨v, hv⟩ := exists_place_of_notMem_genFibre hN ψ hp
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F'
    obtain ⟨m, n, hm, hn, h⟩ := hZ v π hπ
    exact Or.inr ⟨v, π, m, n, hv, hπ, hm, hn, h p hv⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Coef

section General

variable {X : Scheme.{0}} {K R : Type} [CommRing K] [CommRing R] [IsLocalRing R]

def cst (g : X ⟶ Sp K) (x : X) : K →+* X.presheaf.stalk x :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp g.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem stalkClosedPointTo_germ_top (z : Sp R ⟶ X) (t : Γ(X, ⊤)) :
    (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom t) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom t) := by
  have h : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  exact congrArg (fun q => q.hom t) h

theorem val_cst (z : Sp R ⟶ X) (g : X ⟶ Sp K) (φ : K →+* R) (h : z ≫ g = spMap φ) (k : K) :
    (Scheme.stalkClosedPointTo z).hom (cst g (centre z) k) = φ k := by
  show (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom
    (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k))) = φ k
  rw [stalkClosedPointTo_germ_top]
  have h2 : z.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k)) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := by
    have h' : z ≫ g = Spec.map (CommRingCat.ofHom φ) := h
    rw [← h']; simp only [Scheme.Hom.comp_appTop]; rfl
  rw [h2]
  have h3 := congrArg (fun q => q.hom k) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ k) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := h3
  rw [← h3']
  simp

variable {Ω : Type} [Field Ω]

theorem genMap_cst (ξ : Sp Ω ⟶ X) (g : X ⟶ Sp K) (φ : K →+* Ω) (h : ξ ≫ g = spMap φ) (p : Cpt ξ) (k : K) :
    genMap ξ p (cst g p.1 k) = φ k := by
  have h1 : genMap ξ p (cst g p.1 k) = (Scheme.stalkClosedPointTo ξ).hom (cst g (centre ξ) k) :=
    congrArg (Scheme.stalkClosedPointTo ξ).hom
      (X.presheaf.germ_stalkSpecializes_apply (show p.1 ∈ (⊤ : X.Opens) from trivial) p.2 _)
  rw [h1, val_cst ξ g φ h]

theorem exists_lift {ξ : Sp Ω ⟶ X} {F : Type} [Field F] [NumberField F] (hξ : IsCptGen ξ) (hN : NormalCpt ξ)
    (p : Cpt ξ) (inc : F →+* Ω) (hq : ∀ n : ℕ, 0 < n → IsUnit (n : X.presheaf.stalk p.1)) :
    ∃ κ : F →+* X.presheaf.stalk p.1, (genMap ξ p).comp κ = inc := by
  haveI : CharZero Ω := charZero_of_injective_ringHom inc.injective
  have hinv : ∀ n : ℕ, 0 < n → ((n : Ω))⁻¹ ∈ regAt ξ p := by
    intro n hn
    obtain ⟨u, hu⟩ := hq n hn
    refine ⟨(u⁻¹ : _ˣ), ?_⟩
    have h1 : genMap ξ p u = (n : Ω) := by rw [hu, map_natCast]
    have h2 : genMap ξ p (u⁻¹ : _ˣ) * genMap ξ p u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [h1] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hmem : ∀ r : ℚ, Rat.castHom Ω r ∈ regAt ξ p := by
    intro r
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
    exact mul_mem (intCast_mem _ _) (hinv r.den r.den_pos)
  let ψ : ℚ →+* regAt ξ p := (Rat.castHom Ω).codRestrict _ hmem
  have hint : ∀ a : F, inc a ∈ regAt ξ p := by
    intro a
    refine hN p _ ⟨(minpoly ℚ a).map ψ, (minpoly.monic (Algebra.IsIntegral.isIntegral a)).map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (regAt ξ p) Ω).comp ψ = inc.comp (algebraMap ℚ F) := Subsingleton.elim _ _
    rw [e, ← Polynomial.hom_eval₂]
    have := minpoly.aeval ℚ a
    rw [Polynomial.aeval_def] at this
    rw [this, map_zero]
  have hb : Function.Bijective (genMap ξ p).rangeRestrict :=
    ⟨fun a b hab => hξ.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩
  refine ⟨(RingEquiv.ofBijective _ hb).symm.toRingHom.comp (inc.codRestrict (genMap ξ p).range hint), ?_⟩
  ext a
  exact congrArg Subtype.val ((RingEquiv.ofBijective _ hb).apply_symm_apply (inc.codRestrict (genMap ξ p).range hint a))

end General

theorem exists_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (T : Type) [CommRing T] [IsLocalRing T] (y : Sp T ⟶ Xo.XF c) (c₀ : c.F →+* T), y ≫ pullback.snd _ _ = spMap c₀ → centre y ∈ U → ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))), (genMap (Z.ξ₀ ≫ Y.j) ⟨_, h⟩).comp κ = Z.inc ∧ (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = c₀ := by
  intro E _ _ _ H D l Xo c U O _ β Y Z T _ _ y c₀ hy hU
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have h0 : genPt Z.ξ₀ ⤳ centre y := (Z.closure _).1 hU
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := h0.map Y.j.continuous
  refine ⟨h, ?_⟩
  have hN : NormalCpt (Z.ξ₀ ≫ Y.j) := XR.normalCpt_of_isCptGen Z.gen Y.normal
  have hq : ∀ n : ℕ, 0 < n → IsUnit (n : Y.X.presheaf.stalk (centre (y ≫ Y.j))) := by
    intro n hn
    haveI : IsLocalHom (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom := Scheme.isLocalHom_stalkClosedPointTo _
    have e : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom (n : Y.X.presheaf.stalk (centre (y ≫ Y.j))) =
        c₀ (n : c.F) := (map_natCast _ n).trans (map_natCast c₀ n).symm
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom _
      ((congrArg IsUnit e).mpr ((IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')).map c₀))
  obtain ⟨κ, hκ⟩ := exists_lift Z.gen hN ⟨centre (y ≫ Y.j), h⟩ Z.inc hq
  refine ⟨κ, hκ, ?_⟩
  let π := genMap Z.ξ₀ ⟨centre y, h0⟩
  let s : c.F →+* (Xo.XF c).presheaf.stalk (centre y) := (Y.j.stalkMap (centre y)).hom.comp κ
  let t : c.F →+* (Xo.XF c).presheaf.stalk (centre y) := cst (pullback.snd _ _) (centre y)
  have hD : GlobalTheory.CompanionTheory.Ar.Dominates Z.ξ₀ (Z.ξ₀ ≫ Y.j) Y.j (RingHom.id Z.Ω) := by
    show Z.ξ₀ ≫ Y.j = Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) ≫ Z.ξ₀ ≫ Y.j
    have e : CommRingCat.ofHom (RingHom.id Z.Ω) = 𝟙 _ := rfl
    rw [e, Spec.map_id, Category.id_comp]
  have hs : π.comp s = Z.inc := by
    ext a
    exact (PullReg.stalkMap_comp_genMap hD ⟨centre y, h0⟩ h (κ a)).trans (congrArg (fun f => f a) hκ)
  have ht : π.comp t = Z.inc := by
    ext a
    exact genMap_cst Z.ξ₀ (pullback.snd _ _) Z.inc Z.over_inc ⟨centre y, h0⟩ a
  have est : s = t := GlobalTheory.T.number_field_maps_local_ring_unique c.F _ Z.Ω π s t (hs.trans ht.symm)
  have e1 : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = (Scheme.stalkClosedPointTo y).hom.comp s := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  rw [e1, est]
  ext a
  exact val_cst y (pullback.snd _ _) c₀ hy a

end GlobalTheory.CompanionTheory.Ar.LocFn.Coef
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl GlobalTheory.CompanionTheory.Ar.Sl.Transl

theorem _root_.GlobalTheory.T.torsion_value_line_bundle_section : ∀ {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F] {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) (N : ℕ) (T : F), TorsVal P s y N T → ∀ (z : Sp F) (J : (Sp F ⟶ G.left) → P.L.ι), Good P.L z J → ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]), w.IsGen ∧ toStk z T * ((val (Z := Sp F) w (1 : Over.mk b ⟶ G).left z J).val * (val (Z := Sp F) P.rig b z J).val ^ (N ^ 2)) ^ n = sval (Z := Sp F) s y.left z J ^ (N ^ 2) * (val (Z := Sp F) w y.left z J).val ^ n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.torsVal_charts | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.torsVal_charts | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.torsVal_charts <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.CoordPart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

section Comb

variable {S : Scheme.{0}} {K C : Type} [CommRing K] [CommRing C]

theorem dualMap_comp_algebraMap' (φ : K →+* C) :
    (GlobalTheory.CompanionTheory.Ar.dualMap φ).comp (algebraMap K (DualNumber K)) = (algebraMap C (DualNumber C)).comp φ := by
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

def bcHom (φ : K →+* C) (x : Sp K ⟶ S) : epsAt (spMap φ ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ)) (by
    show spMap _ ≫ spMap _ ≫ x = spMap _ ≫ spMap _ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, dualMap_comp_algebraMap'])

theorem dual_epsMul (φ : K →+* C) (a : K) :
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ spMap (GlobalTheory.CompanionTheory.Ar.epsMul a) =
      spMap (GlobalTheory.CompanionTheory.Ar.epsMul (φ a)) ≫ spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) := by
  rw [spMap_comp_spMap, spMap_comp_spMap]
  congr 1
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [GlobalTheory.CompanionTheory.Ar.dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, mul_comm]

theorem comp_list_prod {G : Over S} [GrpObj G] {T T' : Over S} (f : T' ⟶ T) (l : List (T ⟶ G)) :
    f ≫ l.prod = (l.map (f ≫ ·)).prod := by
  induction l with
  | nil => simp [MonObj.comp_one]
  | cons a l ih => simp [MonObj.comp_mul, ih]

theorem comb_eq_pt {G : Over S} [GrpObj G] (φ : K →+* C) {x : Sp K ⟶ S} {x' : Sp C ⟶ S} (hx : spMap φ ≫ x = x')
    {U : Type} [AddCommGroup U] [Module C U] (M : LieModel G x' U) {n : ℕ} (c : Fin n → K)
    (u : Fin n → (epsAt x ⟶ G)) (w : epsAt x ⟶ G) (hc : IsComb c u w) (e : Fin n → U)
    (he : ∀ k, spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (u k).left = (M.pt (e k)).left) :
    spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ w.left = (M.pt (∑ k, φ (c k) • e k)).left := by
  subst hx
  obtain ⟨u', hu', rfl⟩ := hc
  have key : IsComb (fun k => φ (c k)) (fun k => M.pt (e k)) (bcHom φ x ≫ (List.ofFn u').prod) := by
    refine ⟨fun k => bcHom φ x ≫ u' k, fun k => ?_, ?_⟩
    · show spMap (GlobalTheory.CompanionTheory.Ar.dualMap φ) ≫ (u' k).left = _
      rw [hu' k, ← Category.assoc, dual_epsMul, Category.assoc, he k]
    · rw [comp_list_prod, List.map_ofFn]
      rfl
  have := ((GlobalTheory.T.lie_model_eigenvectors_action S C G _ U M).1 n _ _ _).1 key
  exact congrArg (fun q => q.left) this

end Comb

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sum_eq_tyPart {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) (ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ))
    (hρ : ∀ a w, ρ a w = fun k => ty k (a : E) * w k) (τ : E →+* ℂ)
    (hpr : ∀ w, HT.eigProj ρ τ w = tyPart ty τ w) (z : ℂ) {n : ℕ}
    (e : Fin n ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (a : D.La) :
    ∑ k, τ (HT.dualInt E (e k)) • (z • P (RingOfIntegers.basis E (e k) • a)) = z • tyPart ty τ (P a) := by
  have h1 : ∀ s : 𝓞 E, P (s • a) = ρ s (P a) := fun s => by
    rw [hρ]; funext j; exact hP.1 s a j
  rw [← hpr, HT.eigProj, LinearMap.sum_apply, Finset.smul_sum,
    ← Equiv.sum_comp e (fun q => z • (τ (HT.dualInt E q) • ρ (RingOfIntegers.basis E q)) (P a))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h1, smul_comm]
  rfl

theorem isDerivAt0_of_isCMVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (b : Bool) (τ : E →+* ℂ) (a : PureType.lat hP (sgnRt H b)) (v : epsAt (under X.y) ⟶ Xo.univ.t.G), X.IsCMVec b τ a v → IsDerivAt0 (fun s => (FU.ex i P s).left) ((Z b).z • tyPart ty τ (P a)) (spMap (dualMap (algebraMap X.K ℂ)) ≫ v.left) := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X b τ a v hv
  obtain ⟨M, ρ, -, hρ, hder, hpr⟩ := GlobalTheory.T.lie_model_with_cm_action E H D l Xo c g ty FU i P hP
  obtain ⟨n, e, u, hu, hc⟩ := hv
  have hk : ∀ k, spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap X.K ℂ)) ≫ (u k).left =
      (M.pt ((Z b).z • P (RingOfIntegers.basis E (e k) • (a : (FU.Di i).La)))).left := fun k =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows.isDerivAt0_unique
      ((GlobalTheory.T.cm_image_unique_lattice E H D l Xo c g ty FU i Z P hP X b _).2 (u k) (hu k)).2 (hder _)
  have h := comb_eq_pt (algebraMap X.K ℂ) X.pt M _ u v hc _ hk
  rw [h]
  have hs : ∑ k, (algebraMap X.K ℂ) (X.β (tauE c τ (HT.dualInt E (e k)))) •
      ((Z b).z • P (RingOfIntegers.basis E (e k) • (a : (FU.Di i).La))) = (Z b).z • tyPart ty τ (P a) :=
    sum_eq_tyPart hP ρ hρ τ (hpr τ) _ e a
  rw [hs]
  exact hder _

end Main

end GlobalTheory.CompanionTheory.Ar.Fl.CoordPart
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem flagStep_mono' {Ω E' : Type} [Field Ω] [AddCommGroup E'] [Module Ω E'] {r : ℕ} (b : Fin r → E') {i i' : ℕ} (h : i ≤ i') :
    flagStep Ω b i ≤ flagStep Ω b i' :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

theorem exists_satFlag {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Type} [Field L] [NumberField L] (M : LieModel G ξ Li)
    (z : Sp (𝓞 L) ⟶ X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier) {r : ℕ}
    (b : Fin r → Li) (hr : ∀ i : ℕ, i ≤ r → Module.finrank (𝓞 L) (subFib M (flagStep Ω b i) z MB) = i) :
    ∃ A : SatFlag B r, ∀ i, A.F i = subFib M (flagStep Ω b i.val) z MB :=
  ⟨{ F := fun i => subFib M (flagStep Ω b i.val) z MB
     mono := fun _ _ hi => subFib_mono M (flagStep_mono' b (Fin.le_def.1 hi)) z MB
     sat := fun _ => subFib_saturated M _ z B MB
     rank := fun i => hr i.val (Nat.lt_succ_iff.1 i.2) }, fun _ => rfl⟩

theorem rank_fib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier),
    Fintype.card (CMType H) * (D.p + D.q) = Module.finrank (𝓞 L) B.carrier ∧
    (∀ s (i : ℕ), i ≤ labelRk D s → Module.finrank (𝓞 L) (subFib 𝔐.M (flagStep Ω (Fl.b s) i) z MB) = i) ∧
    ∀ s (i : ℕ), flagStep Ω (Fl.b s) i ≤ 𝔐.Vgen s := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 _ Fl L _ _ z B MB
  classical
  have hgen : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hs : genPt 𝔐.ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z) := 𝔐.all _
  have hu := fun n hn => isUnit_natCast_stalk 𝔐.X L (spMap (algebraMap (𝓞 L) L) ≫ z) n hn
  obtain ⟨b, hb1, hb2, hb3, hb4, hb5, hb6⟩ := GlobalTheory.T.exists_flag_basis_at_stalk E H D l Xo c Y S Ω K J y 𝔐 Fl ⟨_, hs⟩ hu
  obtain ⟨T, _, _, _, _, TL, j, hj, hbc⟩ := GlobalTheory.T.exists_lie_model_base_change 𝔐.X 𝔐.t.G (𝓞 L) L z B.carrier MB
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := GlobalTheory.T.lie_model_frame_spans_generic 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M L _ T TL hs
    (Σ s, Fin (labelRk D s)) _ hgen hb3 hb4 hb5
  have hbr := fun U => GlobalTheory.T.lie_model_projective_generic_fibre 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M L z B.carrier MB T TL j U hgen hj hbc
  refine ⟨?_, ?_, ?_⟩
  · rw [(hbr ⊥).1]
    have e1 := finrank_span_eq_card hw2
    rw [hw3, finrank_top] at e1
    rw [e1, Fintype.card_sigma, Fintype.sum_sum_type]
    have a1 : ∀ τ : CMType H, Fintype.card (Fin (labelRk D (Sum.inl τ))) = D.p := fun _ => Fintype.card_fin _
    have a2 : ∀ τ : CMType H, Fintype.card (Fin (labelRk D (Sum.inr τ))) = D.q := fun _ => Fintype.card_fin _
    simp only [a1, a2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  · intro s i hi
    rw [(hbr _).2]
    let g : Fin i → Σ s, Fin (labelRk D s) := fun k => ⟨s, ⟨k.1, lt_of_lt_of_le k.2 hi⟩⟩
    have hg : Function.Injective g := by
      intro a b' hab
      simp only [g, Sigma.mk.injEq, heq_eq_eq, true_and, Fin.mk.injEq] at hab
      exact Fin.ext hab
    have himg : (fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) '' Set.range g = b s '' {k | (k : ℕ) < i} := by
      ext x
      constructor
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨⟨k.1, lt_of_lt_of_le k.2 hi⟩, k.2, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨_, ⟨⟨k.1, hk⟩, rfl⟩, rfl⟩
    have hspan : Submodule.span L {w' | ∃ e ∈ flagStep Ω (Fl.b s) i, 𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w')} =
        Submodule.span L (Set.range (w ∘ g)) := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro w' ⟨e, he, hv⟩
        obtain ⟨h', hl⟩ := (LieModel.exists_valAt_iff 𝔐.M _ e).1 ⟨_, hv⟩
        have h2 := hb2 s i e (by rw [hb1]; exact he) hl
        rw [← himg] at h2
        have := hw4 (Set.range g) e w' h2 hv
        rwa [← Set.range_comp] at this
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        refine Submodule.subset_span ⟨b s ⟨k.1, lt_of_lt_of_le k.2 hi⟩, ?_, hw1 (g k)⟩
        rw [← hb1]
        exact Submodule.subset_span ⟨_, k.2, rfl⟩
    rw [hspan, finrank_span_eq_card (hw2.comp g hg), Fintype.card_fin]
  · intro s i
    rw [← hb1, ← hb6]
    exact Submodule.span_mono (Set.image_subset_range _ _)

theorem flag_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∃ (A : FlagPair B (CMType H) D.p D.q), A.IsOrthFull ∧ (∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A.W τ).F i)) ∧ ∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A.S τ).F i) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 _ Fl h hO L _ _ z B MB hF
  obtain ⟨h1, h2, h3⟩ := rank_fib E H D l Xo c Y S Ω K J y 𝔐 Fl L z B MB
  have ho := GlobalTheory.T.orthogonal_metric_hermitian_bundle E H D l Xo c Y S Ω K J y 𝔐 h hO L z B MB hF
  have hex : ∀ s, ∃ A : SatFlag B (labelRk D s), ∀ i, A.F i = subFib 𝔐.M (flagStep Ω (Fl.b s) i.val) z MB := by
    intro s
    exact exists_satFlag 𝔐.M z B MB (Fl.b s) (h2 s)
  choose A hA using hex
  have hW : ∀ (τ : CMType H) (i : Fin (D.p + 1)), IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A (.inl τ)).F i) := by
    intro τ i
    rw [hA (.inl τ) i]
    exact isSubFibre_subFib _ _ _ _
  have hS : ∀ (τ : CMType H) (i : Fin (D.q + 1)), IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A (.inr τ)).F i) := by
    intro τ i
    rw [hA (.inr τ) i]
    exact isSubFibre_subFib _ _ _ _
  have hpart : ∀ s, FlagPair.part (⟨fun τ => A (.inl τ), fun τ => A (.inr τ)⟩ : FlagPair B (CMType H) D.p D.q) s =
      subFib 𝔐.M (flagStep Ω (Fl.b s) (labelRk D s)) z MB := by
    rintro (τ | τ)
    · exact hA (.inl τ) (Fin.last _)
    · exact hA (.inr τ) (Fin.last _)
  refine ⟨⟨fun τ => A (.inl τ), fun τ => A (.inr τ)⟩, ⟨?_, h1⟩, hW, hS⟩
  intro a b hab
  rw [hpart, hpart]
  exact ho a b hab _ _ (h3 a _) (h3 b _)

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end
