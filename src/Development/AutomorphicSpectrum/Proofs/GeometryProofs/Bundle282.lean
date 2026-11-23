module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle004
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle005
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FinConstFor
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle006
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle004
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle121
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle280
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle226
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle216
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle093
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle094
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle035
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle035
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle155
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle062
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle110
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle107
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle115
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle156
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle129
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle117
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.TopA

theorem exists_padic_emb (F : IntermediateField ℚ ℂ) [NumberField F] (p : Nat.Primes) :
    Nonempty (F →+* ℂ_[p]) :=
  ⟨(IsAlgClosed.lift (M := ℂ_[p]) (R := ℚ) (S := F)).toRingHom⟩

theorem eq_of_clopen_irred {X : Type*} [TopologicalSpace X] {U U' : Set X} (hU : IsClopen U)
    (hUi : IsIrreducible U) (hU' : IsClopen U') (hUi' : IsIrreducible U') {u : X} (hu : u ∈ U) (hu' : u ∈ U') :
    U = U' :=
  (hUi.isConnected.isPreconnected.subset_isClopen hU' ⟨u, hu, hu'⟩).antisymm
    (hUi'.isConnected.isPreconnected.subset_isClopen hU ⟨u, hu', hu⟩)

theorem finite_primes_dvd {n : ℕ} (hn : n ≠ 0) : {p : Nat.Primes | (p : ℕ) ∣ n}.Finite :=
  ((Set.finite_Iic n).preimage Subtype.val_injective.injOn).subset fun p hp =>
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp

theorem model_hyp {K : Type} [Field K] (V : ValuationSubring K) [IsDiscreteValuationRing V] :
    Function.Injective V.subtype ∧ IsNoetherianRing V ∧
      ∀ x : K, ∃ a b : V, V.subtype b ≠ 0 ∧ x * V.subtype b = V.subtype a := by
  refine ⟨Subtype.val_injective, inferInstance, fun x => ?_⟩
  rcases V.mem_or_inv_mem x with h | h
  · exact ⟨⟨x, h⟩, 1, by simp, by simp⟩
  · by_cases hx : x = 0
    · exact ⟨0, 1, by simp, by simp [hx]⟩
    · exact ⟨1, ⟨x⁻¹, h⟩, by simpa using hx, by simp [hx]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_place {l : Level H} (c : Coeff l) [NumberField c.F] (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) :
    ∃ W : ValuationSubring ℂ, ((p : ℕ) : ℂ) ∈ W.nonunits ∧ IsDiscreteValuationRing (c.V W) ∧
      ∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ c.V W := by
  obtain ⟨W, hp, hW⟩ := GlobalTheory.T.padic_embedding_valuation_subring c.F p κ
  obtain ⟨V, hV, hκ, -, -⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring c.F p κ
  have hmem : ∀ x : c.F, x ∈ c.V W ↔ ‖κ x‖ ≤ 1 := fun x => (hW x).symm
  have heq : c.V W = V := by ext x; rw [hmem, hκ]
  refine ⟨W, hp, ?_, fun x => (hmem x).symm⟩
  rw [heq]; exact hV

theorem exists_cpt {D : Datum H} {l : Level H} (Xo : Moduli D l) (c : Coeff l) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β)
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    {U : Set (Xo.XF c)} (hU : IsClopen U) (hUi : IsIrreducible U) : Nonempty (CptOver Y U) := by
  obtain ⟨u, hu⟩ := hUi.nonempty
  obtain ⟨U', Z, hu', hc, hi⟩ := GlobalTheory.T.exists_clopen_irreducible_cpt E H D l Xo c O β Y u hβ
  rw [eq_of_clopen_irred hU hUi hc hi hu hu']
  exact ⟨Z⟩

theorem local_gen (hA0 : FlatLineGenerator) (hA1 : FlatLineGeneratorComponent) (hC : FinConstAll) {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} (U : Set (Xo.XF c)) (τ : E →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (hpq : 1 ≤ D.p + D.q)
    (hτ : τ (H.rt : E) = H.rt0) (hty : IsTypeFn H D.p D.q ty) (hU : IsClopen U) (hUi : IsIrreducible U)
    (hP : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      (Set.range y ⊆ U ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P))
    (W : ValuationSubring ℂ) [IsDiscreteValuationRing (c.V W)] (Y : Model Xo c (c.V W).subtype)
    (hSF : Y.SplitFibres) (hN3 : Y.N3) (p : Nat.Primes) (κ : c.F →+* ℂ_[p])
    (hκ : ∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ c.V W) :
    ∃ φ : FrameFn Xo c, IsFlatGen U τ φ FU i ∧ (∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t) ∧
      ∃ t, HasFinNorm U τ φ p κ t := by
  obtain ⟨Z⟩ := exists_cpt Xo c Y (model_hyp (c.V W)) hU hUi
  have hG : Z.IsGeom := GlobalTheory.T.generic_fibre_uniformised_frame E H D l Xo c _ _ Y U Z g ty FU i hty (fun y hy hr => (hP y hy).1 hr)
  obtain ⟨φ, hl, hf, -⟩ := hA0 E H D l Xo c _ _ Y U Z τ (model_hyp (c.V W)) hpq hτ hG
  obtain ⟨hinf, hfg⟩ := hA1 E H D l Xo c _ _ Y U Z τ φ (model_hyp (c.V W)) hpq hτ hG hl hf
  refine ⟨φ, hfg g ty FU i hty (fun P y hPer hu hy => (hP y hy).2 ⟨P, hPer, hu⟩), fun s => ?_, ?_⟩
  · obtain ⟨t, ht, -⟩ := hinf s
    exact ⟨t, ht⟩
  · refine hC E H D l Xo c _ _ Y U Z τ p κ φ hτ Subtype.val_injective (fun x => (hκ x).trans ?_) hSF hN3 hG hf hl
    exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

theorem hasFinNorm_of_eq {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {U : Set (Xo.XF c)}
    {τ : E →+* ℂ} {φ φ' : FrameFn Xo c} (hl : IsLineFn U τ φ) {a : c.F} (ha : a ≠ 0)
    (he : ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ' F y v w = β a * φ F y v w)
    {p : Nat.Primes} {κ : c.F →+* ℂ_[p]} {t : ℝ} (ht : HasFinNorm U τ φ' p κ t) :
    HasFinNorm U τ φ p κ (t - Real.log ‖κ a‖) := by
  intro V K _ _ _ _ _ _ j β y v w T tK m m' hj hjβ hfr hv hw
  have h1 := ht V K j β y v w T tK m m' hj hjβ hfr hv hw
  have hja : j (β a) = κ a := by rw [← hjβ]; rfl
  have h2 : ‖κ a‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero κ).mpr ha)
  have h3 : ‖j (φ K y v w)‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero j).mpr (hl.ne K β y v w hfr))
  rw [he K β y v w hfr, map_mul, hja, norm_mul, Real.log_mul h2 h3] at h1
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat.TopA

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.TopA in
theorem thmFlatA_of_parts : PartI → FlatLineGenerator → FlatLineGeneratorComponent → FinConst → ThmFlatA := by
  intro hI hA0 hA1 _ E _ _ _ H D Xo l c _ U τ g ty FU i hpq hτ hg hty hU hUi hP
  have hC : FinConstAll := GlobalTheory.T.finite_constant_all_holds
  obtain ⟨-, hI'⟩ := hI
  obtain ⟨Ys, hYs, -⟩ := hI' E H D hpq Xo
  have key : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ φ : FrameFn (Xo l) c, IsFlatGen U τ φ FU i ∧
      (∀ s : c.F →+* ℂ, ∃ t, HasInfNorm U τ φ s t) ∧ ∃ t, HasFinNorm U τ φ p κ t := by
    intro p κ
    obtain ⟨W, hpW, hdvr, hκ⟩ := exists_place c p κ
    haveI := hdvr
    obtain ⟨-, hYi⟩ := hYs p W p.2 hpW
    obtain ⟨hSF, hN3, -⟩ := hYi ⟨l, c, hg p p.2⟩
    exact local_gen hA0 hA1 hC U τ FU i hpq hτ hty hU hUi hP W (Ys p W p.2 hpW ⟨l, c, hg p p.2⟩) hSF hN3 p κ hκ
  obtain ⟨κ₀⟩ := exists_padic_emb c.F ⟨2, Nat.prime_two⟩
  obtain ⟨φ, hφ, hinf, -⟩ := key _ κ₀
  have hfin : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm U τ φ p κ t := by
    intro p κ
    obtain ⟨φ', hφ', -, t, ht⟩ := key p κ
    obtain ⟨a, ha, he⟩ := GlobalTheory.T.flat_gen_frame_complex_compat E H D l (Xo l) c U τ φ' φ g ty FU i hty hφ' hφ
      (fun y hy hr => (hP y hy).1 hr)
    exact ⟨_, hasFinNorm_of_eq hφ.line ha he ht⟩
  let N : LogNorms c.F := ⟨fun s => (hinf s).choose, fun p κ => (hfin p κ).choose -
    D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖)⟩
  have hN : HasNorms U τ φ N := ⟨fun s => (hinf s).choose_spec, fun p κ => by
    simp only [N, sub_add_cancel]
    exact (hfin p κ).choose_spec⟩
  refine ⟨φ, N, hφ, hN, ?_⟩
  obtain ⟨n, hn, hn0⟩ := GlobalTheory.T.finite_norm_zero_outside_denom E H D l (Xo l) c U τ φ hτ hU.isOpen hUi.nonempty hφ.line
  have hS := GlobalTheory.T.logIdeal_support_finite E (differentIdeal ℤ (𝓞 E)) differentIdeal_ne_bot
  refine (((finite_primes_dvd hn.ne').union (finite_primes_dvd H.d_prime.ne_zero)).union hS).subset ?_
  rintro p ⟨ι₀, hι⟩
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at hcon
  obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
  obtain ⟨-, -, -, -, hd⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring c.F p ι₀
  have hd' : ‖((H.d : ℕ) : ℂ_[p])‖ = 1 := by simpa using hd H.d h2
  have h0 := hn0 p ι₀ _ h1 (hN.2 p ι₀)
  rw [h3 (ι₀.comp (tauIn c τ)), hd', Real.log_one] at h0
  simp only [sub_zero, mul_zero, add_zero] at h0
  exact hι h0

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeModel

theorem model_on_hodge_of_family_pos : FamilyExistsPos → HodgeLatticeFlagBound := by
  intro hF E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV _ _ Fl S₀ T hT p hpS hpS₀ hHT hp2 hdisc φ hφ A _ _ _
  intro m _ hm O _ _ _ _ _ _ _
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
  · haveI : IsEmpty (Fin (D.p + D.q)) := by rw [h0]; exact Fin.isEmpty'
    intro τ k _ Q _
    have h1 : ((T.map (Int.castRingHom O)).comp fun i : Fin (D.p + D.q) => (τ, i)).ck (pointIdeal O y) k Q = 0 := by
      simp [LocPair.ck, GroundTheory.Heights₂.Heights.NumbersDVR.pairNum]
    have h3 : ∀ τ', liePs (Ψ := CMType H) (N := D.p + D.q) D.p (k - 1) τ' = 0 := by
      rintro (τ' | τ') <;> simp [liePs]
    have h2 : bracket (N := D.p + D.q) D.p φ p k τ = 0 := by
      simp [bracket, h3]
    rw [h1, h2]
    simp [cycNum]
  have hpP : p.Prime := 𝔐.S_prime p hpS
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI : CharZero Ω := charZero_of_injective_ringHom 𝔐.cst.injective
  obtain ⟨hAD, hAfin, hAinj, hAcst, hloc⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV A
  haveI := hAD
  haveI := hAfin
  obtain ⟨hOint, hOfn⟩ := hloc m O
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨-, hModel, hVert⟩ := GlobalTheory.T.localization_model_over_place K J Ω y A hAinj hAcst d hV m O
  have hT2 := hT
  obtain ⟨hS₀, hvb, hsub, e₀, e, hR₀, hR, hfg, hvo⟩ := hT2
  have hTv := hVert ϖ hϖ _ _ T hvo
  have hOinj : Function.Injective (algebraMap O Ω) := hOint.1
  have hb : ∀ t, LinearIndependent Ω (Fl.b t) ∧ Submodule.span Ω (Set.range (Fl.b t)) = 𝔐.Vgen t :=
    GlobalTheory.T.flag_basis_lin_indep_span E H D l Xo c O₀ β Y S Ω K J y 𝔐 Fl
  have hfam := hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV hpos Fl.b hb p hpS hHT hp2 hdisc φ hφ A m hm O
  choose Sg hSg ε φ' F hF1 hF2 hF3 w σ Df hDf using hfam
  have hFc : ∀ t, 0 < Fintype.card (F t) - 1 := fun t => by
    have := Fintype.one_lt_card (α := F t)
    omega
  have hN0 : 0 < ∏ t, (Fintype.card (F t) - 1) := Finset.prod_pos fun t _ => hFc t
  obtain ⟨O', _, _, _, _, _, _, Ω', _, _, _, _, _, _, ζ, hO'inj, hζ, hadj⟩ := GlobalTheory.T.exists_dvr_extension_field O Ω hOinj _ hN0
  have hζt : ∀ t, IsPrimitiveRoot (ζ ^ ((∏ t, (Fintype.card (F t) - 1)) / (Fintype.card (F t) - 1)))
      (Fintype.card (F t) - 1) := fun t =>
    hζ.pow hN0 (Nat.div_mul_cancel
      (Finset.dvd_prod_of_mem (fun t => Fintype.card (F t) - 1) (Finset.mem_univ t))).symm
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible O'
  haveI : CharZero Ω' := charZero_of_injective_ringHom (algebraMap Ω Ω').injective
  haveI : CharZero O' := (algebraMap O' Ω').charZero
  have hModel' := (GlobalTheory.T.model_over_dvr_extension O Ω K J y d hModel hOint O' Ω' hO'inj).2
  have hfn' := GlobalTheory.T.function_field_dvr_extension O Ω K J y hOfn O' Ω' ζ hadj
  have hTwin : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O'
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O' (fun v => algebraMap Ω Ω' (y v))) d :=
    (GroundTheory.Heights₂.Heights.NumbersDVR.BundleExamples.isModelOver_iff O' _ d).2 ⟨hV.1, hModel'⟩
  have hagree : ∀ s (q : Cpt 𝔐.ξ), (∀ p' : ℕ, p'.Prime → ¬ InFibre 𝔐.ξ p' q) → 𝔐.HT p s q = 𝔐.dR s q :=
    GlobalTheory.T.hodge_flag_outside_prime_fibres E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS
  have hLat := GlobalTheory.T.hodge_flag_cm_type_degree E H D l Xo c O₀ β Y S Ω K J y 𝔐 Fl S₀ T hT p hpS hpS₀ hagree
  have hag2 : ∀ s, ∀ q : Cpt 𝔐.ξ, q ∈ overPrime 𝔐.ξ p → ¬ InFibre 𝔐.ξ p q → 𝔐.dR s q = 𝔐.HT p s q := by
    intro s q hq hqp
    refine (hagree s q fun p' hp' => ?_).symm
    by_cases h : p' = p
    · subst h; exact hqp
    · exact hq p' hp' h
  have hB := fun s => GlobalTheory.T.arith_variety_dedekind_constants 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie d hV A hAinj hAcst p hpP m hm O ϖ hϖ 𝔐.Li
    (labelRk D s) (Fl.b s) (hb s).1 (𝔐.dR s) (𝔐.HT p s) (labelPair D T s) (hLat s) (hag2 s)
  choose B B' v v' hBlat hBfp using hB
  have hC := fun s : CMType H ⊕ CMType H => GlobalTheory.T.flag_pair_chart_bundle_compat O Ω K J y ϖ _ (B s.swap) (B' s.swap) (v s.swap) (v' s.swap) _ _ _ _
    (hBfp s.swap)
  choose C C' u u' hClat hCfp using hC
  have hmm : ∀ {σ' : Type} (Q : LocPair J ℤ σ'),
      (Q.map (Int.castRingHom O)).map (algebraMap O O') = Q.map (Int.castRingHom O') := by
    intro σ' Q
    rw [map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hE := fun s => GlobalTheory.T.model_descent_valuation_fibre O Ω K J y d hModel hOint O' Ω' hO'inj ϖ ϖ' hϖ hϖ' _ (B s) (B' s) (v s)
    (v' s) ((labelPair D T s).map (Int.castRingHom O)) (hBfp s)
  choose LB LB' lv lv' hLBlat hLBfp using hE
  have hE2 := fun s => GlobalTheory.T.model_descent_valuation_fibre O Ω K J y d hModel hOint O' Ω' hO'inj ϖ ϖ' hϖ hϖ' _ (C s) (C' s) (u s)
    (u' s) ((omPair D T s).map (Int.castRingHom O)) (hCfp s)
  choose LC LC' lu lu' hLClat hLCfp using hE2
  have hRel : ∀ t, Relations (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p (φ' t)
      (fun τ => (labelPair D T (ε t τ)).map (Int.castRingHom O'))
      (fun τ => (omPair D T (ε t τ)).map (Int.castRingHom O')) := by
    intro t
    obtain ⟨-, -, hpre, hfamOf⟩ := hDf t
    obtain ⟨χ, Df', hM3, hspan⟩ := GlobalTheory.T.model_descent_generic_fibre O Ω K J y d hModel hOint O' Ω' hO'inj (F t) p _ (hζt t)
      (D.p + D.q) (Sg t) _ _ (w t) (σ t) (φ' t) (Df t) hpre
    refine GlobalTheory.T.arithmetic_relations_statement_holds O' Ω' K J (fun v => algebraMap Ω Ω' (y v)) ϖ' hϖ' d hTwin hfn' p hpP
      (algebraMap O O' (w t)) χ (φ' t) Df' hM3
      (fun τ => LB (ε t τ)) (fun τ => LB' (ε t τ)) (fun τ => LC (ε t τ)) (fun τ => LC' (ε t τ)) ?_ _ _ ?_
    · intro τ c hc
      have hc' : segreVec y c ≠ 0 := by
        intro h
        apply hc
        show ∏ k, algebraMap Ω Ω' (y ⟨k, c k⟩) = 0
        rw [← map_prod]
        exact (congrArg (algebraMap Ω Ω') h).trans (map_zero _)
      obtain ⟨hl, hW, ho, hoh⟩ := hfamOf c hc' τ
      obtain ⟨s1, s2, s3, s4⟩ := hspan c hc' τ
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [(hLBlat _ c hc').1, (hBlat _ c hc').1, s1, hl]; rfl
      · rw [(hLBlat _ c hc').2, (hBlat _ c hc').2, s2, hW]; rfl
      · rw [(hLClat _ c hc').1, (hClat _ c hc').1, (hBlat _ c hc').1, s3, ho]; rfl
      · rw [(hLClat _ c hc').2, (hClat _ c hc').2, (hBlat _ c hc').2, s4, hoh]; rfl
    · intro τ
      refine ⟨⟨lv (ε t τ), lv' (ε t τ), ?_⟩, ⟨lu (ε t τ), lu' (ε t τ), ?_⟩⟩
      · have h := hLBfp (ε t τ)
        rw [hmm] at h
        exact h
      · have h := hLCfp (ε t τ)
        rw [hmm] at h
        exact h
  have hLoc : LabelChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p φ
      (fun s => (labelPair D T s).map (Int.castRingHom O')) (fun s => (omPair D T s).map (Int.castRingHom O')) := by
    refine GlobalTheory.T.local_comparison_of_orbits_holds O' K J (CMType H ⊕ CMType H) _ d p hpP.two_le φ _ _ _ _ fun τ => ?_
    obtain ⟨hrange, hcomm, -, -⟩ := hDf τ
    exact ⟨Sg τ, inferInstance, ε τ, φ' τ, hrange, hcomm, hRel τ⟩
  have hLoc2 : LabelChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p φ
      (fun s => (labelPair D T s).map (Int.castRingHom O')) (fun s => (omPairM D T s).map (Int.castRingHom O')) := by
    intro k hk Q hQ τ
    rcases τ with τ | τ
    · exact hLoc k hk Q hQ (.inl τ)
    · exact hLoc k hk Q hQ (.inr τ)
  have hp0' : (p : O') ≠ 0 := Nat.cast_ne_zero.2 hpP.ne_zero
  have hFlag' := GlobalTheory.T.flag_m3_from_local O' ϖ' hϖ' K J _ d hModel' p hp0' (CMType H) D.p D.q φ (T.map (Int.castRingHom O'))
    (fun s => (labelPair D T s).map (Int.castRingHom O')) (fun s => (omPairM D T s).map (Int.castRingHom O'))
    (fun τ => rfl)
    (fun τ => by
      show (dualRev (dualRev (T.comp _))).map _ = _
      rw [dualRev_dualRev]
      rfl)
    (fun τ k Q _ => (GlobalTheory.T.local_number_permutation_invariant O' K J D.q Fin.revPerm _ k Q).1 (p : O')
      (fun i => -(T.map (Int.castRingHom O')).x (τ, Fin.natAdd D.p i)))
    hLoc2
  have hT' : FlagChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p D.p φ
      ((T.map (Int.castRingHom O)).map (algebraMap O O')) := by
    rw [hmm]
    exact hFlag'
  exact (GlobalTheory.T.model_descent_integral_closure O Ω K J y d hModel hOint O' Ω' hO'inj ϖ hϖ p).1 hpP.ne_zero (CMType H) (D.p + D.q) D.p φ
    (T.map (Int.castRingHom O)) hTv hT'

end GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
end
