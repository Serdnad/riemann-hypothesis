module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle047
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle103
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle067
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle096
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle087
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeFlagCmTypeDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle099
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle045
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle028
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem isPiece_chart {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ U : X.Opens, IsPiece ξ U (chartSub x c) ∧ ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := by
  obtain ⟨U, hU, hm⟩ := hT.affine c hc
  have hq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := fun q =>
    ⟨fun h => ((hm q.1).1 h).2, fun h => (hm q.1).2 ⟨q.2, h⟩⟩
  refine ⟨U, ⟨hU, fun q h => ((hm q).1 h).1, fun a => ?_⟩, hq⟩
  refine (hT.ring c hc a).trans (forall_congr' fun q => imp_congr (hq q).symm Iff.rfl)

theorem coordTie_int_inst {X : Scheme.{0}} {F : Type} [Field F] {ξ : Spec (CommRingCat.of F) ⟶ X} {κ : Type} {x : κ → F}
    (inst : Algebra ℤ F) (h : @CoordTie X F _ ℤ _ inst ξ κ x) : @CoordTie X F _ ℤ _ (Ring.toIntAlgebra F) ξ κ x := by
  rwa [Subsingleton.elim inst (Ring.toIntAlgebra F)] at h

theorem locSub_le_of_mul {F : Type} [Field F] {R : Subring F} {a b g : F} (hb : b ∈ R) (h : a * b = g) (hg : g ≠ 0) :
    locSub R a ≤ locSub R g := by
  refine (Subring.closure_le).2 (Set.union_subset (fun y hy => le_locSub R g hy) ?_)
  rintro _ rfl
  have ha : a ≠ 0 := left_ne_zero_of_mul (h ▸ hg)
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (h ▸ hg)
  have e : a⁻¹ = b * g⁻¹ := by rw [← h]; field_simp
  rw [SetLike.mem_coe, e]
  exact (locSub R g).mul_mem (le_locSub R g hb) (inv_mem_locSub R g)

theorem flag_smooth : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E) (m n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (f : X' ⟶ X), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → (∀ s, IsTwistGen ξ x (L s) (m s) (φ s)) → (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → CoordTie ℤ ξ' (flagCoord κ x φ c) → (∀ q : X', genPt ξ' ⤳ q) → Dominates ξ' ξ f (algebraMap Ω (GenField Ω r)) → (∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p') → Smooth f := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L m n φ c X' ξ' f hT hall hVB hTw hc hT' hall' hdom hch
  classical
  have hi : Function.Injective (algebraMap Ω (GenField Ω r)) := (algebraMap Ω (GenField Ω r)).injective
  refine GlobalTheory.T.dominating_pieces_smooth X X' Ω (GenField Ω r) ξ ξ' f (algebraMap Ω (GenField Ω r)) hT.gen hT'.gen hdom (fun p' => ?_)
  let P' : Cpt ξ' := ⟨p', hall' p'⟩
  obtain ⟨⟨c₀, J⟩, hcJ⟩ := hT'.cover P'
  have hy0 : flagCoord κ x φ c (c₀, J) ≠ 0 := hcJ.1
  have hx0 : x c₀ ≠ 0 := by
    intro h0
    apply hy0
    simp [flagCoord, h0]

  have hover : ∀ Q' : Cpt ξ', InChart ξ' (flagCoord κ x φ c) ((c₀, J) : FlagIx κ n r) Q' →
      InChart ξ x c₀ ⟨f Q'.1, hall _⟩ := by
    intro Q' hQ
    refine (hch Q' c₀ (hall _)).2 ⟨by simpa using hx0, fun k => ?_⟩
    have h := hQ.2 ((k, J) : FlagIx κ n r)
    have hpr : (∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det) ≠ 0 := by
      intro h0
      apply hy0
      simp [flagCoord, h0]
    have e : flagCoord κ x φ c ((k, J) : FlagIx κ n r) / flagCoord κ x φ c ((c₀, J) : FlagIx κ n r) =
        algebraMap Ω (GenField Ω r) (x k) / algebraMap Ω (GenField Ω r) (x c₀) := by
      simp only [flagCoord]
      have : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := by simpa using hx0
      field_simp
    rwa [e] at h
  let P : Cpt ξ := ⟨f p', hall _⟩
  have h2 : InChart ξ x c₀ P := hover P' hcJ
  have hfr := fun s => GlobalTheory.T.twisted_frame_in_chart X Ω ξ E κ x (r s) (V s) (L s) (m s) (n s) (φ s) (c s) c₀ P hT hall (hVB s) (hTw s) (hc s) h2
  choose g hgR hgu T M N hT0 hM hN hNM hφ using hfr
  let g₀ : Ω := ∏ s, g s
  have hg₀R : g₀ ∈ chartSub x c₀ := Subring.prod_mem _ fun s _ => hgR s
  have hg₀0 : g₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => (hgu s).1
  have hreg : ∀ a ∈ chartSub x c₀, ∀ Q : Cpt ξ, InChart ξ x c₀ Q → a ∈ regAt ξ Q := fun a ha Q hQ =>
    (hT.ring c₀ hx0 a).1 ha Q hQ
  have hg₀inv : g₀⁻¹ ∈ regAt ξ P := by
    have : g₀⁻¹ = ∏ s, (g s)⁻¹ := by simp [g₀]
    rw [this]
    exact Subring.prod_mem _ fun s _ => (hgu s).2.2
  have hg₀u : unitAt ξ P g₀ := ⟨hg₀0, hreg _ hg₀R P h2, hg₀inv⟩
  let R : Subring Ω := locSub (chartSub x c₀) g₀
  have hle : ∀ s, locSub (chartSub x c₀) (g s) ≤ R := fun s =>
    locSub_le_of_mul (b := ∏ s' ∈ Finset.univ.erase s, g s')
      (Subring.prod_mem _ fun s' _ => hgR s') (Finset.mul_prod_erase Finset.univ g (Finset.mem_univ s)) hg₀0
  have hRP : ∀ a ∈ R, a ∈ regAt ξ P := by
    have : R ≤ regAt ξ P := (Subring.closure_le).2 (Set.union_subset (fun y hy => hreg y hy P h2)
      (by rintro _ rfl; exact hg₀inv))
    exact this
  obtain ⟨hPh, hdom1, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' (GenField Ω r) ξ' f _ hdom P'
  have hRO : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ regAt ξ' P' := fun a ha => hdom1 a (hRP a ha)
  haveI : IsLocalRing (regAt ξ' P') := (regAt_isLocalRing_isFractionRing_stalk X' _ ξ' hT'.gen P').1
  have hscale : ∀ (k : κ) (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), _ :=
    fun k J' => flagCoord_eq (m := m) x hφ k J'
  have hax : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := by simpa using hx0
  have hprod0 := hscale c₀ J
  have hβ0 : ∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0 := by
    intro q h0
    apply hy0
    rw [hprod0, Finset.prod_eq_zero (Finset.mem_univ q) (by rw [h0, mul_zero]), mul_zero]
  have hβJ : ∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ regAt ξ' P' := by
    intro q J'
    have h := hcJ.2 ((c₀, Function.update J q J') : FlagIx κ n r)
    rw [hscale c₀ (Function.update J q J'), hprod0, mul_div_mul_left _ _ hax,
      prod_update_div (β := fun q => Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
        (fun q b => (algebraMap Ω (GenField Ω r) (x c₀) ^ m q.1) ^ ((q.2 : ℕ) + 1) * stepMinor (flagB M T q.1) q.2 b) J
        (fun q => mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hax)) (hβ0 q)) q J',
      mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ hax))] at h
    exact h
  obtain ⟨t, htR, ht0, htO, htiO, hmap, hsm⟩ := GlobalTheory.T.frame_matrices_regular_generic Ω S r n R (regAt ξ' P') T M N J hRO hT0
    (fun s j l => hle s (hM s j l)) (fun s l j => hle s (hN s l j)) hNM hβ0 hβJ
  obtain ⟨hgA, hAeq⟩ := GlobalTheory.T.chart_frame_matrix_regular Ω E κ x S r n m φ c M T c₀ J g₀ hx0 hg₀R hg₀0 hφ hβ0
  obtain ⟨U₀, hU₀, hU₀m⟩ := isPiece_chart hT hx0
  obtain ⟨U₁, hU₁, hU₁m⟩ := GlobalTheory.T.piece_localization_at_element X Ω ξ U₀ _ g₀ hT.gen hU₀ hg₀R hg₀0
  obtain ⟨W₀, hW₀, hW₀m⟩ := isPiece_chart (coordTie_int_inst _ hT') hy0
  have hig0 : algebraMap Ω (GenField Ω r) g₀ ≠ 0 := by simpa using hg₀0
  obtain ⟨W₁, hW₁, hW₁m⟩ := GlobalTheory.T.piece_localization_at_element X' _ ξ' W₀ _ _ hT'.gen hW₀ hgA hig0
  rw [hAeq] at hW₁
  obtain ⟨W₂, hW₂, hW₂m⟩ := GlobalTheory.T.piece_localization_at_element X' _ ξ' W₁ _ t hT'.gen hW₁ htR ht0
  refine ⟨U₁, W₂, R, _, hmap, hU₁, hW₂, ?_, ?_, hsm⟩
  · intro q' hq'
    let Q' : Cpt ξ' := ⟨q', hall' q'⟩
    have e1 := ((hW₂m Q').1 hq').1
    obtain ⟨e2, e3⟩ := (hW₁m Q').1 e1
    have e4 := (hW₀m Q').1 e2
    have e5 := hover Q' e4
    obtain ⟨h', -, hun⟩ := RegAtDom.regAt_dominates X Ω ξ X' (GenField Ω r) ξ' f _ hdom Q'
    exact (hU₁m ⟨f q', hall _⟩).2 ⟨(hU₀m _).2 e5, hun hT'.gen g₀ (hreg _ hg₀R _ e5) e3⟩
  · refine (hW₂m P').2 ⟨(hW₁m P').2 ⟨(hW₀m P').2 hcJ, hig0, hRO _ (le_locSub _ _ hg₀R), ?_⟩, ht0, htO, htiO⟩
    rw [← map_inv₀]
    exact hRO _ (inv_mem_locSub _ _)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem ringOfIntegers_hom_injective {F : Type} [Field F] [NumberField F] {R : Type} [Field R] [CharZero R]
    (a : 𝓞 F →+* R) : Function.Injective a := by
  have hI : (RingHom.ker a).comap (algebraMap ℤ (𝓞 F)) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    have h0 : ((n : ℤ) : R) = 0 := by
      have h1 : a (algebraMap ℤ (𝓞 F) n) = 0 := hn
      simpa using h1
    have h2 : n = 0 := by exact_mod_cast h0
    simp [h2]
  exact (RingHom.injective_iff_ker_eq_bot a).2 (Ideal.eq_bot_of_comap_eq_bot hI)

theorem exists_ringHom_extend {F : Type} [Field F] [NumberField F] {R : Type} [Field R] [CharZero R]
    (a : 𝓞 F →+* R) : ∃ κ : F →+* R, κ.comp (algebraMap (𝓞 F) F) = a :=
  ⟨IsFractionRing.lift (ringOfIntegers_hom_injective a),
    RingHom.ext fun x => IsFractionRing.lift_algebraMap (ringOfIntegers_hom_injective a) x⟩

theorem exists_isOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), 𝔐.Interior z → ∃ (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z hz
  have := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let a : 𝓞 c.F →+* ℂ := (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom
  have ha : z ≫ 𝔐.f ≫ Y.s = spMap a := by
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨κ, hκ⟩ := exists_ringHom_extend a
  have hc : (z ≫ 𝔐.f) ≫ Y.s = spMap κ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, ha, ← hκ, Chg.spMap_comp']
  let w : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift (z ≫ 𝔐.f) (spMap κ) hc
  have hw₁ : w ≫ pullback.fst _ _ = z ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hw₂ : w ≫ pullback.snd _ _ = spMap κ := pullback.lift_snd _ _ _
  have := Y.jQ_open
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨u, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, hw₁, Scheme.Hom.comp_apply]
    have hu : u = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hu
    exact (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 _).2 hz
  let x : Sp ℂ ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ w hr
  have hx : x ≫ Y.jQ = w := IsOpenImmersion.lift_fac _ _ _
  refine ⟨κ, x ≫ pullback.fst _ _, x, ?_, rfl, ?_⟩
  · rw [Model.j, ← Category.assoc, hx, hw₁]
  · rw [← Y.jQ_over, ← Category.assoc, hx, hw₂]

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Num.HodgeModel
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)


theorem _root_.GlobalTheory.T.hodge_flag_cm_type_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β)
    (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)]
    (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] [DecidableEq (CMType H)] (Fl : 𝔐.Flag)
    (S₀ : Finset ℕ) (T : LocPair J ℤ (CMType H × Fin (D.p + D.q))), Fl.TwoLevels S₀ T → ∀ p ∈ S, p ∉ S₀ →
    (∀ (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ p' : ℕ, p'.Prime → ¬ InFibre 𝔐.ξ p' q) → 𝔐.HT p s q = 𝔐.dR s q) →
    ∀ s, IsLatFlagPair y (overPrime 𝔐.ξ p) (𝔐.dR s) (𝔐.HT p s) (Fl.b s) (labelPair D T s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwoLevelLat.latFlagPair_of_twoLevels | exact GlobalTheory.CompanionTheory.Ar.TwoLevelLat.latFlagPair_of_twoLevels | (intros; apply GlobalTheory.CompanionTheory.Ar.TwoLevelLat.latFlagPair_of_twoLevels <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open GlobalTheory.CompanionTheory.Ar.Flat.Rep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
  {φ : G'.left ⟶ G.left}

theorem grpPull_mul (hφ : IsGrpPullback G' G f φ) (T : Over S') {g : T.left ⟶ S} (hg : g = T.hom ≫ f)
    (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hg
  exact hφ.2 T x y x₀ y₀ hx hy

theorem grpPull_one (hφ : IsGrpPullback G' G f φ) (T : Over S') {g : T.left ⟶ S} (hg : g = T.hom ≫ f) :
    (1 : Over.mk g ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  subst hg
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = T.hom ≫ f := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (1 : T ⟶ G'))
  let e : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have h := hφ.2 T 1 1 e e rfl rfl
  rw [_root_.mul_one] at h
  have h2 : e * e = e := Over.OverMorphism.ext h
  have h3 : e = 1 := mul_eq_left.1 h2
  exact (congrArg (fun q : Over.mk (T.hom ≫ f) ⟶ G => q.left) h3).symm

end Grp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Same

variable {Y : Model Xo c β} {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}

theorem sameVec_one (Y : Model Xo c β) (y : Sp F ⟶ Xo.XF c) : SameVec Y y 1 1 := by
  let T : Over (Xo.XF c) := epsAt y
  refine ⟨(1 : T ⟶ Y.oF.t.G).left, Over.w _, ?_, ?_⟩
  · exact (grpPull_one Y.m0.cart T (Category.assoc _ _ _).symm).symm
  · exact (grpPull_one Y.m.cart T (Category.assoc _ _ _).symm).symm

theorem sameVec_mul {a b : epsAt (under y) ⟶ Xo.univ.t.G} {a' b' : epsAt (y ≫ Y.j) ⟶ Y.t.G}
    (h₁ : SameVec Y y a a') (h₂ : SameVec Y y b b') : SameVec Y y (a * b) (a' * b') := by
  obtain ⟨u₁, p₁, q₁, r₁⟩ := h₁
  obtain ⟨u₂, p₂, q₂, r₂⟩ := h₂
  let T : Over (Xo.XF c) := epsAt y
  let x₁ : T ⟶ Y.oF.t.G := Over.homMk u₁ p₁
  let x₂ : T ⟶ Y.oF.t.G := Over.homMk u₂ p₂
  refine ⟨(x₁ * x₂).left, Over.w (x₁ * x₂), ?_, ?_⟩
  · exact (grpPull_mul Y.m0.cart T (Category.assoc _ _ _).symm x₁ x₂ a b q₁.symm q₂.symm).symm
  · exact (grpPull_mul Y.m.cart T (Category.assoc _ _ _).symm x₁ x₂ a' b' r₁.symm r₂.symm).symm

theorem sameVec_scale {a u : epsAt (under y) ⟶ Xo.univ.t.G} {a' : epsAt (y ≫ Y.j) ⟶ Y.t.G} (h : SameVec Y y a a')
    (r : F) (hu : u.left = spMap (GlobalTheory.CompanionTheory.Ar.epsMul r) ≫ a.left) :
    SameVec Y y u (LieTangent.epsScale (y ≫ Y.j) r ≫ a') := by
  obtain ⟨u₀, p, q, t⟩ := h
  refine ⟨spMap (GlobalTheory.CompanionTheory.Ar.epsMul r) ≫ u₀, ?_, ?_, ?_⟩
  · rw [Category.assoc, p, ← Category.assoc, LieTangent.spec_eps_alg]
  · rw [Category.assoc, q, hu]
  · rw [Category.assoc, t]
    rfl

end Same

theorem valFam_sum {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {F : Type} [Field F]
    (y : Sp F ⟶ Xo.XF c) (hg : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) {n : ℕ} (e : Fin n → Z.V)
    (u : Fin n → (epsAt (under y) ⟶ Xo.univ.t.G))
    (h : ∀ j, ∃ a, Z.M.ValAt (y ≫ Y.j) (e j) a ∧ SameVec Y y (u j) a) :
    ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, e j) w' ∧ SameVec Y y (List.ofFn u).prod w' := by
  induction n with
  | zero =>
    refine ⟨1, ?_, ?_⟩
    · simpa using Z.M.valAt_zero hg
    · simpa using sameVec_one Y y
  | succ n ih =>
    obtain ⟨a, ha, hb⟩ := h 0
    obtain ⟨w', hw, hs⟩ := ih (fun i => e i.succ) (fun i => u i.succ) fun i => h i.succ
    refine ⟨a * w', ?_, ?_⟩
    · rw [Fin.sum_univ_succ]
      exact ha.add hw
    · rw [List.ofFn_succ, List.prod_cons]
      exact sameVec_mul hb hs

theorem valFam_sum_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c) (n : ℕ) (b : Fin n → Z.V) (v : Vecs y n) (s : Fin n → Z.Ω) (r : Fin n → F) (w : epsAt (under y) ⟶ Xo.univ.t.G), genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) → IsValFam Z y b v → (∀ j, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (s j) (r j)) → IsComb r v w → ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, s j • b j) w' ∧ SameVec Y y w w' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z F _ y n b v s r w hg h hs hw
  obtain ⟨u, hu, rfl⟩ := hw
  refine valFam_sum Z y hg _ u fun j => ?_
  obtain ⟨h1, t, e1, e2⟩ := hs j
  obtain ⟨a, ha, hb⟩ := h j
  have h2 := ha.smul h1 t
  rw [e1, e2] at h2
  exact ⟨_, h2, sameVec_scale hb (r j) (hu j)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.Rep
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LinePull

theorem wedge_eq_span_pull {X₀ X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {f : X ⟶ X₀} {i : Ω₀ →+* Ω}
    {V₀ V : Type} [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] {j : V₀ →+ V}
    (hD : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) (hE : IsExtOver i j) {L₀ : Lat ξ₀ V₀} {L : Lat ξ V} {n : ℕ}
    {a₀ : ⋀[Ω₀]^n V₀} {a : ⋀[Ω]^n V} (x : Cpt ξ) (h : genPt ξ₀ ⤳ f x.1) {u : Fin n → V₀} {α : Ω₀} (hα : α ≠ 0)
    (hF : L₀.IsFrameAt u ⟨f x.1, h⟩) (hL : L x = L₀.pull ξ f j x)
    (hW : L₀.wedge n ⟨f x.1, h⟩ = Submodule.span (regAt ξ₀ ⟨f x.1, h⟩) {α • a₀})
    (hP : CptIn.IsPullWedge i j a₀ a) :
    L.wedge n x = Submodule.span (regAt ξ x) {i α • a} := by
  obtain ⟨_, hreg, -⟩ := pull_reg_and_gen X₀ Ω₀ ξ₀ X Ω ξ f i hD x
  have hF' := FlagPull.pull_isFrameAt hD hE x h hF
  have hFr : L.IsFrameAt (fun k => j (u k)) x := ⟨hF'.1, hL.trans hF'.2⟩
  obtain ⟨hw, -⟩ := WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ L n _ x hFr
  obtain ⟨hw₀, hne⟩ := WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ L₀ n u _ hF
  obtain ⟨ε, hε, e⟩ := ZUnit.exists_of_span_eq hne (hw₀.symm.trans hW)
  have hεα : ε * α ≠ 0 := mul_ne_zero hε.1 hα
  have ha₀ : a₀ = (ε * α)⁻¹ • exteriorPower.ιMulti Ω₀ n u := by
    rw [e, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hεα, one_smul]
  have ha := hP u _ ha₀
  have hne' : i ε ≠ 0 := (map_ne_zero i).2 hε.1
  have hiα : i α ≠ 0 := (map_ne_zero i).2 hα
  have e2 : exteriorPower.ιMulti Ω n (fun k => j (u k)) = i ε • i α • a := by
    rw [ha, smul_smul, smul_smul, ← map_mul, ← map_mul, mul_inv_cancel₀ hεα, map_one, one_smul]
  rw [hw, e2]
  have hu : i ε ∈ regAt ξ x := hreg _ hε.2.1
  have hv : (i ε)⁻¹ ∈ regAt ξ x := by
    rw [← map_inv₀]
    exact hreg _ hε.2.2
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨i ε, hu⟩, rfl⟩
  · refine ⟨⟨(i ε)⁻¹, hv⟩, ?_⟩
    show (i ε)⁻¹ • i ε • i α • a = i α • a
    rw [inv_smul_smul₀ hne']

theorem isCoeffAt_pull : ∀ (X₀ X : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ X₀) (i : Ω₀ →+* Ω) (V₀ V : Type) [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] (j : V₀ →+ V) (A₀ B₀ : Lat ξ₀ V₀) (A B : Lat ξ V) (p q : ℕ) (a₀ : ⋀[Ω₀]^p V₀) (b₀ : ⋀[Ω₀]^q V₀) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (x₀ : Cpt ξ₀) (u₁ : Fin p → V₀) (u₂ : Fin q → V₀), IsCptGen ξ₀ → IsCptGen ξ → Dominates ξ ξ₀ f i → IsExtOver i j → x₀.1 = f x.1 → A₀.IsFrameAt u₁ x₀ → B₀.IsFrameAt u₂ x₀ → A x = A₀.pull ξ f j x → B x = B₀.pull ξ f j x → IsCoeffAt A₀ B₀ p q a₀ b₀ x₀ 1 → CptIn.IsPullWedge i j a₀ a → CptIn.IsPullWedge i j b₀ b → IsCoeffAt A B p q a b x 1 := by
  intro X₀ X Ω₀ Ω _ _ ξ₀ ξ f i V₀ V _ _ _ _ j A₀ B₀ A B p q a₀ b₀ a b x x₀ u₁ u₂ _ _ hD hE hx hF₁ hF₂ hA hB hC hPa hPb
  obtain ⟨α, β, hα, -, hAw, hBw, hαβ⟩ := hC
  rw [one_mul] at hαβ
  subst hαβ
  obtain ⟨y, hy⟩ := x₀
  obtain rfl : y = f x.1 := hx
  exact ⟨i α, i α, (map_ne_zero i).2 hα, (map_ne_zero i).2 hα,
    wedge_eq_span_pull hD hE x hy hα hF₁ hA hAw hPa, wedge_eq_span_pull hD hE x hy hα hF₂ hB hBw hPb, one_mul _⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LinePull
end
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

open GlobalTheory.CompanionTheory.Ar.BT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {F : Type} [Field F]

abbrev NAdd (E : Type) [Field E] [NumberField E] (n p : ℕ) : Type := Fin n → (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})

def toNAdd {n p : ℕ} (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) : (Fin n → F) →+ NAdd E n p where
  toFun a i := sc (a i)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def fromNAdd {n p : ℕ} (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) : NAdd E n p →+ (Fin n → F) where
  toFun t i := pq (t i)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def bcLin (C : Type) [Field C] [Algebra Ω C] {m n : ℕ} (f : (Fin m → Ω) →ₗ[Ω] (Fin n → Ω)) :
    (Fin m → C) →ₗ[C] (Fin n → C) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map (algebraMap Ω C))

variable {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {c' : ∀ k, J k}

def testOrd (P : ChartPack G O c') {C : Type} [Field C] [Algebra O C] [Algebra Ω C] (RC : Subalgebra O C) :
    Submodule RC (NAdd E (D.p + D.q) p → C) :=
  Submodule.span RC {f | ∃ g ∈ P.Γ₁.btOrder ⊤, f = fun x =>
    algebraMap Ω C ((g (Multiplicative.ofAdd x) : CR O y c') : Ω)}

def testOrdW (P : ChartPack G O c') (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) {C : Type} [Field C] [Algebra O C]
    [Algebra Ω C] (RC : Subalgebra O C) : Submodule RC ((Fin (D.p + D.q) → F) → C) :=
  (testOrd P RC).map (LinearMap.funLeft RC C (toNAdd sc : (Fin (D.p + D.q) → F) → NAdd E (D.p + D.q) p))

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end
end
