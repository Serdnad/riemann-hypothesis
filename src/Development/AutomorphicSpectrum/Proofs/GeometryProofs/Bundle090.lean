module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle076
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle073
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle058
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle055
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MlLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle081
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle080
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.Centre

theorem isUnit_regAt_iff {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (p : Cpt ξ) (a : regAt ξ p) : IsUnit a ↔ unitAt ξ p (a : Ω) := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
    have hab : (a : Ω) * (b : Ω) = 1 := congrArg Subtype.val hb
    have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hab
    refine ⟨h0, a.2, ?_⟩
    rw [← eq_inv_of_mul_eq_one_right hab]
    exact b.2
  · rintro ⟨h0, -, hi⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨(a : Ω)⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem exists_centre : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω') (p' : Cpt ξ'), p' ∈ ctrSet o x i ξ' → ∃ p₀ : Cpt M.ξ, ((∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p') ∧ ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a) ∧ (∀ p : Cpt M.ξ, (∀ a ∈ regAt M.ξ p, i a ∈ regAt ξ' p') → p₀.1 ⤳ p.1) ∧ ∀ c, x c ≠ 0 → (∀ j, i (x j / x c) ∈ regAt ξ' p') → InChart M.ξ x c p₀ := by
  intro o _ Ω _ _ κ _ x M X' Ω' _ ξ' i p' hp'
  obtain ⟨c, hc, hreg⟩ := hp'
  haveI : IsLocalRing (regAt ξ' p') := (GlobalTheory.T.regAt_local_order_fraction X' Ω' ξ').1 p'
  let φ : chRing o x c →+* regAt ξ' p' :=
    (i.comp (chRing o x c).val.toRingHom).codRestrict (regAt ξ' p') (fun a => hreg a a.2)
  let P : Ideal (chRing o x c) := (IsLocalRing.maximalIdeal (regAt ξ' p')).comap φ
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨p₀, ⟨hin, hP⟩, -⟩ := GlobalTheory.T.chart_prime_existsUnique_point o Ω κ x M c hc P hPp
  have key : ∀ u : chRing o x c, unitAt M.ξ p₀ (u : Ω) ↔ unitAt ξ' p' (i u) := by
    intro u
    have h := hP u
    have h2 : u ∈ P ↔ ¬ unitAt ξ' p' (i u) := by
      change φ u ∈ IsLocalRing.maximalIdeal (regAt ξ' p') ↔ _
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_regAt_iff]
      rfl
    tauto
  have hloc := fun (c₁ : κ) (p : Cpt M.ξ) (h : InChart M.ξ x c₁ p) =>
    GlobalTheory.T.regAt_chart_localization o Ω κ x M c₁ p h
  have hch : ∀ a ∈ chRing o x c, a ∈ regAt M.ξ p₀ := (hloc c p₀ hin).1
  have hdom : ∀ a ∈ regAt M.ξ p₀, i a ∈ regAt ξ' p' := by
    intro a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c p₀ hin).2 a).1 ha
    have h1 := (key ⟨v, hv⟩).1 hvu
    rw [map_div₀, div_eq_mul_inv]
    exact mul_mem (hreg u hu) h1.2.2
  have hlift : ∀ a ∈ regAt M.ξ p₀, unitAt ξ' p' (i a) → unitAt M.ξ p₀ a := by
    intro a ha hu'
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c p₀ hin).2 a).1 ha
    have hiu : unitAt ξ' p' (i u) := by
      have h1 : i u = i (u / v) * i v := by rw [← map_mul, div_mul_cancel₀ _ hvu.1]
      rw [h1]
      exact Flat.ZUnit.mul hu' ((key ⟨v, hv⟩).1 hvu)
    have hu0 : unitAt M.ξ p₀ u := (key ⟨u, hu⟩).2 hiu
    rw [div_eq_mul_inv]
    exact Flat.ZUnit.mul hu0 (Flat.ZUnit.inv hvu)
  have hchart : ∀ c₁, x c₁ ≠ 0 → (∀ j, i (x j / x c₁) ∈ regAt ξ' p') → InChart M.ξ x c₁ p₀ := by
    intro c₁ h1 hj
    have hmem : x c₁ / x c ∈ regAt M.ξ p₀ := hch _ (Algebra.subset_adjoin ⟨c₁, rfl⟩)
    have hunit : unitAt ξ' p' (i (x c₁ / x c)) := by
      refine ⟨(map_ne_zero i).2 (div_ne_zero h1 hc), hdom _ hmem, ?_⟩
      rw [← map_inv₀, inv_div]
      exact hj c
    have hu := hlift _ hmem hunit
    refine ⟨h1, fun j => ?_⟩
    have h2 : x j / x c₁ = x j / x c * (x c₁ / x c)⁻¹ := by
      field_simp
    rw [h2]
    exact mul_mem (hch _ (Algebra.subset_adjoin ⟨j, rfl⟩)) hu.2.2
  refine ⟨p₀, ⟨hdom, hlift⟩, ?_, hchart⟩
  intro p hp
  rw [← GlobalTheory.T.regAt_le_iff_specializes o Ω κ x M p p₀]
  obtain ⟨c₁, hc₁⟩ := M.tie.cover p
  have hin₁ := hchart c₁ hc₁.1 (fun j => hp _ (hc₁.2 j))
  intro a ha
  obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((hloc c₁ p hc₁).2 a).1 ha
  have hch₁ := (hloc c₁ p₀ hin₁).1
  have hv' : unitAt M.ξ p₀ v := hlift v (hch₁ v hv)
    ⟨(map_ne_zero i).2 hvu.1, hp v hvu.2.1, by rw [← map_inv₀]; exact hp _ hvu.2.2⟩
  rw [div_eq_mul_inv]
  exact mul_mem (hch₁ u hu) hv'.2.2

end GlobalTheory.CompanionTheory.Ar.Centre
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VbGen

theorem flagStep_comp {Ω Ω' V V' : Type} [Field Ω] [Field Ω'] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω' V'] (i : Ω →+* Ω') (j : V →+ V') (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e) {r : ℕ}
    (b b' : Fin r → V) (k : ℕ) (h : flagStep Ω b k = flagStep Ω b' k) :
    flagStep Ω' (fun a => j (b a)) k = flagStep Ω' (fun a => j (b' a)) k := by
  have key : ∀ c c' : Fin r → V, flagStep Ω c k ≤ flagStep Ω c' k →
      flagStep Ω' (fun a => j (c a)) k ≤ flagStep Ω' (fun a => j (c' a)) k := by
    intro c c' hle
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have hmem : c a ∈ flagStep Ω c' k := hle (Submodule.subset_span ⟨a, ha, rfl⟩)
    show j (c a) ∈ _
    refine Submodule.span_induction (p := fun v _ => j v ∈ flagStep Ω' (fun a => j (c' a)) k) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨d, hd, rfl⟩
      exact Submodule.subset_span ⟨d, hd, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
    · intro t x _ hx
      rw [hj]
      exact Submodule.smul_mem _ _ hx
  exact le_antisymm (key _ _ h.le) (key _ _ h.ge)

theorem span_image_span {Ω Ω' V V' : Type} [Field Ω] [Field Ω'] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω' V'] (i : Ω →+* Ω') (j : V →+ V') (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e)
    (R : Subring Ω) (R' : Subring Ω') (hR : ∀ a ∈ R, i a ∈ R') {r : ℕ} (b : Fin r → V) :
    Submodule.span R' (j '' (Submodule.span R (Set.range b) : Set V)) =
      Submodule.span R' (Set.range fun a => j (b a)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    refine Submodule.span_induction
      (p := fun v _ => j v ∈ Submodule.span R' (Set.range fun a => j (b a))) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨d, rfl⟩
      exact Submodule.subset_span ⟨d, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
    · intro t x _ hx
      have h1 : j (t • x) = (⟨i t, hR t t.2⟩ : R') • j x := hj (t : Ω) x
      rw [h1]
      exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨b a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩

theorem discr_inv_mem {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ)
    (F : Type) [Field F] [NumberField F] (h : ∀ n : ℕ, 0 < n → unitAt ξ p (n : Ω)) :
    (((NumberField.discr F : ℤ) : Ω))⁻¹ ∈ regAt ξ p := by
  have hn0 : 0 < (NumberField.discr F).natAbs := Int.natAbs_pos.2 (NumberField.discr_ne_zero F)
  obtain ⟨-, -, hu⟩ := h _ hn0
  rcases Int.natAbs_eq (NumberField.discr F) with e | e
  · rw [e]; simpa using hu
  · rw [e]
    simpa using (regAt ξ p).neg_mem hu



theorem isFlagVBOn_genFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → B.M.lat = A.M.lat.pull B.ξ h jA → ∀ q ∈ genFib B.ξ, ∀ s, (B.V s).IsFlagVBOn {q} (fun a => jA (Fl.b s a)) := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A Fl B i h jA hdom hf hcst hext hpt hρ hlat q hq s
  intro q' hq'
  obtain rfl : q' = q := hq'
  haveI : CharZero Ω₁ := charZero_of_injective_ringHom A.cst.injective
  have hgenA := A.tie.gen
  have hgenB := B.tie.gen
  obtain ⟨hsp, hreg, hun⟩ := RegAtDom.regAt_dominates A.X Ω₁ A.ξ B.X Ω B.ξ h i hdom q'
  have hunit : ∀ n : ℕ, 0 < n → unitAt A.ξ ⟨h q'.1, hsp⟩ (n : Ω₁) := fun n hn =>
    hun hgenB _ (natCast_mem _ n) (by simpa using hq n hn)
  have hVA : A.V s ⟨h q'.1, hsp⟩ = A.dR s ⟨h q'.1, hsp⟩ :=
    Lat.patch_of_not S₀ _ _ fun r hr hfib => hfib (hunit r (A.S_prime r hr).pos)
  have hVB : B.V s q' = B.dR s q' :=
    Lat.patch_of_not S _ _ fun r hr hfib => hfib (hq r (B.S_prime r hr).pos)
  have hdisc := discr_inv_mem ⟨h q'.1, hsp⟩ E hunit
  have hint : ∀ a, A.emb s a ∈ regAt A.ξ ⟨h q'.1, hsp⟩ := fun a =>
    GlobalTheory.T.integral_element_regular A.X Ω₁ A.ξ ⟨h q'.1, hsp⟩ hgenA (A.normal (h q'.1)).2 _
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)
  obtain ⟨U, hU, b, hb, hfr⟩ := Fl.sub s ⟨h q'.1, hsp⟩ trivial
  obtain ⟨hli, hbs⟩ := hfr ⟨h q'.1, hsp⟩ trivial hU
  refine ⟨⊤, trivial, fun a => jA (b a), fun k => flagStep_comp i jA hext.1 _ _ k (hb k), ?_⟩
  intro q'' hq'' _
  rw [show q'' = q' from hq'']
  refine ⟨hext.2 _ b hli, ?_⟩
  have key := GlobalTheory.T.lattice_eigen_field_extension E Ω₁ Ω i A.Li B.Li jA A.ρ B.ρ (A.emb s) _ _ (A.M.lat ⟨h q'.1, hsp⟩) hext
    (fun a e => (hρ a e).symm) hreg
    (fun a e he => GlobalTheory.T.lie_lattice_stable_under_action A.X Ω₁ A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act _ a e he) hint hdisc
  have hem : B.emb s = i.comp (A.emb s) := by
    show B.cst.comp _ = i.comp (A.cst.comp _)
    rw [hcst]; rfl
  have hL : B.M.lat q' = Submodule.span (regAt B.ξ q') (jA '' (A.M.lat ⟨h q'.1, hsp⟩ : Set A.Li)) := by
    rw [hlat]
    show Lat.pull _ _ _ _ _ = _
    unfold Lat.pull
    congr 1
    ext e'
    constructor
    · rintro ⟨_, e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨hsp, e, he, rfl⟩
  have hA : A.M.lat ⟨h q'.1, hsp⟩ ⊓ (eigSp A.ρ (A.emb s)).restrictScalars (regAt A.ξ ⟨h q'.1, hsp⟩) =
      Submodule.span (regAt A.ξ ⟨h q'.1, hsp⟩) (Set.range b) := hVA.symm.trans hbs
  rw [hVB]
  show B.M.lat q' ⊓ (eigSp B.ρ (B.emb s)).restrictScalars (regAt B.ξ q') = _
  rw [hL, hem, key, hA]
  exact span_image_span i jA hext.1 _ _ hreg b

end GlobalTheory.CompanionTheory.Ar.VbGen
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

theorem exists_valPoint {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X)
    (W : ValuationSubring Ω') (i : Ω →+* Ω') (q : Cpt ξ) (hinj : Function.Injective (genMap ξ q))
    (h : DomBy W.toSubring i ξ q) :
    ∃ z : Sp W ⟶ X, spMap W.subtype ≫ z = spMap i ≫ ξ ∧ z (IsLocalRing.closedPoint W) = q.1 := by
  obtain ⟨h1, h2⟩ := h
  let φ : X.presheaf.stalk q.1 →+* W :=
    (i.comp (genMap ξ q)).codRestrict W.toSubring (fun a => h1 _ ⟨a, rfl⟩)
  have hφ : ∀ a, ((φ a : W) : Ω') = i (genMap ξ q a) := fun _ => rfl
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    have hne : genMap ξ q a ≠ 0 := by
      intro h0
      have : φ a = 0 := Subtype.ext (by rw [hφ, h0, map_zero]; rfl)
      rw [this] at ha
      exact not_isUnit_zero ha
    have hinv : (i (genMap ξ q a))⁻¹ ∈ W.toSubring := by
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hb' : i (genMap ξ q a) * (b : Ω') = 1 := by
        have := congrArg (fun x : W => (x : Ω')) hb
        simpa [hφ] using this
      rw [inv_eq_of_mul_eq_one_right hb']
      exact b.2
    obtain ⟨b, hb⟩ := h2 _ ⟨a, rfl⟩ hne hinv
    refine IsUnit.of_mul_eq_one b (hinj ?_)
    rw [map_mul, hb, map_one, mul_inv_cancel₀ hne]
  let z : Sp W ⟶ X := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk q.1
  refine ⟨z, ?_, ?_⟩
  · have e : CommRingCat.ofHom φ ≫ CommRingCat.ofHom W.subtype =
        X.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
      ext a
      rfl
    have e2 : spMap W.subtype ≫ Spec.map (CommRingCat.ofHom φ) =
        spMap i ≫ Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) := by
      simp only [spMap, ← Spec.map_comp]
      rw [e]
      rfl
    show spMap W.subtype ≫ Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk q.1 = _
    rw [← Category.assoc, e2]
    simp only [Category.assoc]
    have e3 : Spec.map (X.presheaf.stalkSpecializes q.2) ≫ X.fromSpecStalk q.1 = X.fromSpecStalk (genPt ξ) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk q.2
    have e4 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ X.fromSpecStalk (genPt ξ) = ξ :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    have e5 : Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes q.2) ≫
        X.fromSpecStalk q.1 = ξ :=
      (congrArg (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ ·) e3).trans e4
    exact congrArg (spMap i ≫ ·) e5
  · have : IsLocalHom (CommRingCat.ofHom φ).hom := hloc
    change X.fromSpecStalk q.1 (Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint W)) = q.1
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

theorem isSeparated_of_isProjOver' {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsSeparated (PSpace.str R N) := by
    unfold PSpace.str
    infer_instance
  infer_instance

theorem image_eq_of_domBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (i : Ω₀ →+* Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → ∀ (W : ValuationSubring Ω) (q : Cpt 𝔐.ξ) (q₀ : Cpt 𝔐₀.ξ), DomBy W.toSubring (RingHom.id Ω) 𝔐.ξ q → DomBy W.toSubring i 𝔐₀.ξ q₀ → 𝔐.f q.1 = 𝔐₀.f q₀.1 := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ i hξ W q q₀ hq hq₀
  obtain ⟨z, hz, hzc⟩ := exists_valPoint 𝔐.ξ W (RingHom.id Ω) q (𝔐.tie.gen.inj q) hq
  obtain ⟨z₀, hz₀, hzc₀⟩ := exists_valPoint 𝔐₀.ξ W i q₀ (𝔐₀.tie.gen.inj q₀) hq₀
  have hsep : IsSeparated Y.s := isSeparated_of_isProjOver' Y.proj
  have hinj : Function.Injective W.subtype := Subtype.val_injective
  have hdom : IsDominant (spMap W.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical W.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot W.subtype).1 hinj]; exact bot_le)⟩
  have hgen : spMap W.subtype ≫ z ≫ 𝔐.f = spMap W.subtype ≫ z₀ ≫ 𝔐₀.f := by
    rw [← Category.assoc, hz, ← Category.assoc, hz₀]
    have : spMap (RingHom.id Ω) = 𝟙 _ := by simp [spMap]
    rw [this, Category.id_comp, hξ]
    simp only [Category.assoc]
  have hbase : (z ≫ 𝔐.f) ≫ Y.s = (z₀ ≫ 𝔐₀.f) ≫ Y.s := by
    have hsepZ : IsSeparated (specZIsTerminal.from (Sp (𝓞 c.F))) := inferInstance
    refine ext_of_isDominant_of_isSeparated (X := Sp W) (specZIsTerminal.from (Sp (𝓞 c.F)))
      (specZIsTerminal.hom_ext _ _) (spMap W.subtype) ?_
    simp only [← Category.assoc] at hgen ⊢
    rw [hgen]
  have heq : z ≫ 𝔐.f = z₀ ≫ 𝔐₀.f :=
    ext_of_isDominant_of_isSeparated (X := Sp W) Y.s hbase (spMap W.subtype) hgen
  have := congrArg (fun g : Sp W ⟶ Y.X => g (IsLocalRing.closedPoint W)) heq
  change 𝔐.f (z (IsLocalRing.closedPoint W)) = 𝔐₀.f (z₀ (IsLocalRing.closedPoint W)) at this
  rwa [hzc, hzc₀] at this

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.M0
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.field_point_lifts_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (letI := β.toAlgebra; IsFractionRing O c.F) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Y.X), Set.range x ⊆ Set.range Y.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = x := by
  exact @PositivityTheory.HtPt.Ml.lift_generic_point
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.sab_map_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), ∃ m : SABMap t t (𝟙 S), m.φ = 𝟙 t.G.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_sabMap_id | exact GlobalTheory.CompanionTheory.Ar.exists_sabMap_id | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_sabMap_id <;> assumption)
end
