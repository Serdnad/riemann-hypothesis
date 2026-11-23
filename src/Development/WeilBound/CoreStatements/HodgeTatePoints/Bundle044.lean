module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle005
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle016
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GhModelAlg
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle042
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.WeilBound.CoreStatements.HodgeTatePoints.FarsharpA
public import Development.WeilBound.CoreStatements.HodgeTatePoints.FarsharpB
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle037
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle043
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem span_values [IsCommMonObj G] (hξ : IsCptGen ξ) (hs : Smooth G.hom) (M : LieModel G ξ V) {R : Type}
    [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) {ER : Type}
    [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER) :
    Submodule.span R {v | ∃ e, M.ValAt z e (MR.pt v)} = ⊤ := by
  have exists_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R)
      (x : Spec (CommRingCat.of A) ⟶ S) (z : Spec (CommRingCat.of R) ⟶ S)
      (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {E F : Type} [AddCommGroup E] [Module A E] [AddCommGroup F]
      [Module R F] (M : LieModel G x E) (N : LieModel G z F) :
      ∃ j : E →+ F, (∀ e, (N.pt (j e)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap φ)) ≫ (M.pt e).left) ∧
        (∀ (a : A) e, j (a • e) = φ a • j e) ∧
        (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) A E),
          ∃ b' : Module.Basis (Fin n) R F, ∀ k, b' k = j (b k)) := by
    subst hz
    letI := φ.toAlgebra
    obtain ⟨j, h1, h2, h3⟩ := PositivityTheory.HtPt.Htat.lie_bc S G A R x E F M N
    refine ⟨j, h1, h2, fun hs n b => ?_⟩
    exact ⟨Module.Basis.mk (h3 hs n b).1 (h3 hs n b).2.ge, fun k => Module.Basis.mk_apply _ _ _⟩
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, -, hjb⟩ := exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) MA MR
  obtain ⟨i, hi, -, -⟩ := exists_base (genMap ξ ⟨centre z, h⟩) _ ξ
    (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M
  obtain ⟨hf, hp⟩ := PositivityTheory.HtPt.Htat.lie_fin X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) EA MA
  have : Module.Free (X.presheaf.stalk (centre z)) EA := Module.free_of_flat_of_isLocalRing
  obtain ⟨bz, hbz⟩ := hjb hs _ (Module.finBasis _ EA)
  refine top_le_iff.1 (bz.span_eq.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  refine ⟨i (Module.finBasis _ EA k), h, MA.pt (Module.finBasis _ EA k), ⟨MA.tan _, ?_⟩, ?_⟩
  · exact hi _
  · rw [hbz, hj]

theorem lieValAt_end {M : LieModel G ξ V} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} {f : G ⟶ G} [IsMonHom f] {A : V →ₗ[Ω] V} (hA : M.IsDiffOf f A) {e : V}
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z (A e) (w ≫ f) := by
  obtain ⟨hc, v, hv, hw⟩ := h
  refine ⟨hc, v ≫ f, ⟨?_, ?_⟩, ?_⟩
  · rw [LieTangent.isTanAt_iff, ← Category.assoc, (LieTangent.isTanAt_iff _).1 hv.1, MonObj.one_comp]
  · change (M.pt (A e)).left = _
    rw [hA e]
    change (M.pt e).left ≫ f.left = _ ≫ (v.left ≫ f.left)
    rw [hv.2, Category.assoc]
  · change w.left ≫ f.left = _
    change w.left ≫ f.left = _ ≫ (v.left ≫ f.left)
    rw [hw, Category.assoc]

theorem lieValAt_smul {M : LieModel G ξ V} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} {ER : Type} [AddCommGroup ER] [Module R ER] {MR : LieModel G z ER} {e : V}
    {v : ER} (h : M.ValAt z e (MR.pt v)) {a : Ω} {r : R} (ha : ValAt ξ z a r) :
    M.ValAt z (a • e) (MR.pt (r • v)) := by
  obtain ⟨h1, s, rfl, rfl⟩ := ha
  rw [MR.pt_smul]
  exact h.smul h1 s

def emptyCurve (K : Type) [Field K] : ACurve K where
  I := Empty
  v := fun i => i.elim
  w := fun i => i.elim
  fin := fun _ _ => Set.toFinite _
  prod := fun _ _ => finsum_of_isEmpty _

theorem eig_val : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (k K : Type) [Field k] [Field K] [Algebra k K] (z : Spec (CommRingCat.of K) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (O S : Type) [CommRing O] [Fintype S] (act : O → (G ⟶ G)) (r : O →+* Module.End Ω V) (rz : O →+* Module.End K Vz) (σ : S → (O →+* Ω)) (χ : S → (O →+* k)), IsCptGen ξ → Smooth G.hom → (∀ a, IsMonHom (act a)) → M.IsActOf act r → Mz.IsActOf act rz → IsSplit χ → (∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a))) → M.lat ⟨centre z, h₀⟩ = ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩ → ∀ s, Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} = eigSp rz ((algebraMap k K).comp (χ s)) := by
  intro X Ω _ ξ k K _ _ _ z G _ _ V _ _ M Vz _ _ Mz h₀ O S _ _ act r rz σ χ hξ hs hm hr hrz hχ hσ hlat s
  classical
  have : Module.Finite K Vz := (PositivityTheory.HtPt.Htat.lie_fin X G K z Vz Mz).1
  obtain ⟨e, -, -, he3, -, he5⟩ := GlobalTheory.T.eigen_projectors_split_action K (emptyCurve K) Vz (fun i => i.elim) O k S χ hχ (fun i => i.elim) rz
    ⟨fun i => i.elim, Module.finBasis K Vz, Set.toFinite (α := Empty) _⟩ (fun a i => i.elim)
  obtain ⟨m, c, a, hc, hes⟩ := he5 s
  let U : S → Submodule K Vz := fun s =>
    Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)}
  have hU : ∀ t, U t ≤ eig (fun a => rz a) (fun a => algebraMap k K (χ t a)) := by
    intro t
    refine Submodule.span_le.2 ?_
    rintro v ⟨x, hx, hv⟩
    refine mem_eig.2 fun b => Mz.inj ?_
    have := hm b
    have h1 := lieValAt_end (hr b) hv
    have h2 := lieValAt_smul hv (hσ t b)
    have h3 : r b x = σ t b • x := (mem_eig (ρ := fun a => r a) (χ := fun a => σ t a)).1 hx.2 b
    rw [h3] at h1
    exact (hrz b v).trans (h1.unique hξ h2)
  have htop : ⨆ t, U t = ⊤ := by
    refine top_le_iff.1 ((span_values hξ hs M z h₀ Mz).symm.le.trans (Submodule.span_le.2 ?_))
    rintro v ⟨x, hx⟩
    obtain ⟨_, hxl⟩ := (M.exists_valAt_iff z x).1 ⟨_, hx⟩
    have key : ∀ x ∈ ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩, ∃ v ∈ ⨆ t, U t, M.ValAt z x (Mz.pt v) := by
      intro x hx
      induction hx using Submodule.iSup_induction' with
      | mem t x hx =>
        obtain ⟨w, hw⟩ := (M.exists_valAt_iff z x).2 ⟨h₀, hx.1⟩
        obtain ⟨v, rfl⟩ := Mz.onto w hw.isTanAt
        exact ⟨v, Submodule.mem_iSup_of_mem t (Submodule.subset_span ⟨x, hx, hw⟩), hw⟩
      | zero => exact ⟨0, zero_mem _, by rw [Mz.pt_zero]; exact M.valAt_zero h₀⟩
      | add x y _ _ hx hy =>
        obtain ⟨v, hv, hv'⟩ := hx
        obtain ⟨w, hw, hw'⟩ := hy
        exact ⟨v + w, add_mem hv hw, by rw [Mz.add]; exact hv'.add hw'⟩
    obtain ⟨v', hv', hv''⟩ := key x (hlat ▸ hxl)
    rw [Mz.inj (hx.unique hξ hv'')]
    exact hv'
  refine le_antisymm (hU s) fun v hv => ?_
  have key : ∀ v ∈ ⨆ t, U t, e s v ∈ U s := by
    intro v hv
    induction hv using Submodule.iSup_induction' with
    | mem t x hx =>
      have h1 : e s x = algebraMap k K (if t = s then 1 else 0) • x := by

        rw [← hc t, hes, LinearMap.sum_apply, map_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [LinearMap.smul_apply, mem_eig.1 (hU t hx) (a j), map_mul, mul_smul]
      rw [h1]
      split_ifs with h
      · subst h; exact Submodule.smul_mem _ _ hx
      · simp
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  have := key v (htop ▸ Submodule.mem_top)
  rwa [he3 s v hv] at this

end PositivityTheory.HtPt.Ci
end
end

section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

set_option backward.isDefEq.respectTransparency false

namespace PositivityTheory.HtPt.Gh

open GlobalTheory.CompanionTheory.Ar.LieTangent

section Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem htDual_le_lat {p : ℕ} (hpS : p ∈ S) (s : CMType H ⊕ CMType H) (q q' : Cpt 𝔐.ξ) (hqq : q'.1 ⤳ q.1)
    (hq : InFibre 𝔐.ξ p q) (hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' q → p' = p) (hq' : ∀ p' ∈ S, ¬ InFibre 𝔐.ξ p' q')
    (hreg : ∀ a, 𝔐.emb s a ∈ regAt 𝔐.ξ q) (e : 𝔐.Li)
    (he : e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q) : e ∈ 𝔐.M.lat q' := by
  obtain ⟨U, hU, b, -, hb⟩ := 𝔐.vb s q trivial
  have h1 := (hb q trivial hU).2
  have h2 := (hb q' trivial (hqq.mem_open U.isOpen hU)).2
  rw [Lat.patch_of_unique _ _ _ hpS hq hu] at h1
  rw [Lat.patch_of_not _ _ _ hq'] at h2
  have h3 : e ∈ Submodule.span (regAt 𝔐.ξ q) (Set.range b) := by
    rw [← h1]
    cases s with
    | inr τ => exact he
    | inl τ =>
      exact Submodule.subset_span ⟨𝔐.M.mem_eigSp_of_mem_htDual _ _ _ _ he, fun d _ =>
        Submodule.smul_mem _ (⟨_, hreg d⟩ : regAt 𝔐.ξ q) he⟩
  clear he
  induction h3 using Submodule.span_induction with
  | mem x hx =>
    have : x ∈ Submodule.span (regAt 𝔐.ξ q') (Set.range b) := Submodule.subset_span hx
    rw [← h2] at this
    exact this.1
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
    obtain ⟨_, t, rfl⟩ := a
    exact Submodule.smul_mem _ (⟨genMap 𝔐.ξ q t, _, genMap_specializes q q'.2 hqq t⟩ : regAt 𝔐.ξ q') hx

end Reg


theorem hodge_tate_free_sandwich : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (κ : Ω), HTFree 𝔐 p → Sandwich 𝔐 p κ → ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O' : Type) [CommRing O'] [IsLocalRing O'] [Algebra O' C], v.Integers O' → v (p : C) < 1 → ∀ (z : Sp O' ⟶ 𝔐.X) (EC : Type) [AddCommGroup EC] [Module C EC] [Module O' EC] [IsScalarTower O' C EC] (MC : LieModel 𝔐.t.G (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) EC) (ρC : 𝓞 E →+* Module.End C EC) (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* O') (κz : O'), MC.IsActOf 𝔐.t.act.act ρC → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z (𝔐.emb s a) (σ a)) → GlobalTheory.CompanionTheory.Ar.ValAt 𝔐.ξ z κ κz → 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O' ≤ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC ∧ (∀ w ∈ 𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC, κz • w ∈ 𝔐.M.fibAt 𝔐.M.lat z MC ⊓ (GlobalTheory.CompanionTheory.Ar.eigSp ρC ((algebraMap O' C).comp σ)).restrictScalars O') ∧ (𝔐.M.fibAt (𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s)) z MC).FG := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 p hp hpS κ hfree hsand C _ _ v O' _ _ _ hv hvp z EC _ _ _ _ MC
    ρC s σ κz hact hσ hκ
  have hξ := 𝔐.tie.gen
  haveI := 𝔐.t.semi.smooth
  have h : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have h' : genPt 𝔐.ξ ⤳ centre (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) := 𝔐.all _
  have hsp := centre_specializes (algebraMap O' C) z
  have hpu : ¬ IsUnit (p : O') := fun hu => by
    have := hv.one_of_isUnit hu
    rw [map_natCast] at this
    exact hvp.ne this
  have hq : InFibre 𝔐.ξ p ⟨centre z, h⟩ := fun hu => hpu ((unitAt_centre_iff hξ z h p).1 hu)
  have hu : ∀ p' ∈ S, InFibre 𝔐.ξ p' ⟨centre z, h⟩ → p' = p := by
    intro p' hp' hf
    by_contra hne
    have hc : IsCoprime (p' : O') (p : O') :=
      Nat.Coprime.cast ((Nat.coprime_primes (𝔐.S_prime p' hp') hp.out).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h1 | h1
    · exact hf ((unitAt_centre_iff hξ z h p').2 (isUnit_of_mul_isUnit_right h1))
    · exact hpu (isUnit_of_mul_isUnit_right h1)
  have hq' : ∀ p' ∈ S, ¬ InFibre 𝔐.ξ p' ⟨_, h'⟩ := fun p' hp' hf =>
    hf ((unitAt_centre_iff hξ _ h' p').2 (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (𝔐.S_prime p' hp').ne_zero)))
  have hreg : ∀ a, 𝔐.emb s a ∈ regAt 𝔐.ξ ⟨centre z, h⟩ := fun a => by
    obtain ⟨_, t, ht, -⟩ := hσ a
    exact ⟨t, ht⟩
  obtain ⟨n, βb, gm, hβ, hVal⟩ := exists_frame 𝔐.M z MC h h'
  haveI : FiniteDimensional Ω 𝔐.Li := Module.Finite.of_basis βb
  obtain ⟨U, hU, b, hbs, hb⟩ := hfree.2 s ⟨centre z, h⟩ hq
  obtain ⟨hli, hbq⟩ := hb _ hq hU
  obtain ⟨f, hf1, hf2⟩ := exists_predual b hli hbs
  have hw : ∀ j, ∃ w ∈ omP 𝔐 p ⟨centre z, h⟩, (𝔐.Vgen s).dualRestrict w = b j := fun j => by
    have : b j ∈ ((omP 𝔐 p).map (𝔐.Vgen s).dualRestrict) ⟨centre z, h⟩ := by
      rw [hbq]; exact Submodule.subset_span ⟨j, rfl⟩
    exact this
  choose w hw1 hw2 using hw
  have hw3 : ∀ j (e : 𝔐.Vgen s), w j e = b j e := fun j e => by rw [← hw2]; rfl
  have hgk : ∀ a, genMap 𝔐.ξ ⟨_, h'⟩ ((𝔐.X.presheaf.stalkSpecializes hsp).hom a) = genMap 𝔐.ξ ⟨centre z, h⟩ a :=
    fun a => genMap_specializes ⟨centre z, h⟩ h' hsp a
  have hfW : ∀ j, (f j : 𝔐.Li) ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) ⟨centre z, h⟩ := fun j => by
    refine (𝔐.M.mem_htDual _ _ _ _ _ (f j)).2 fun u hu => ?_
    have hu' : u ∈ Submodule.span (regAt 𝔐.ξ ⟨centre z, h⟩) (Set.range b) := hbq ▸ hu
    clear hu
    induction hu' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      refine (hf1 i j).symm ▸ (?_ : (if i = j then (1 : Ω) else 0) ∈ regAt 𝔐.ξ ⟨centre z, h⟩)
      by_cases hij : i = j
      · rw [ite_eq_left hij]
        exact one_mem _
      · rw [ite_eq_right hij]
        exact zero_mem _
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => exact mul_mem a.2 hx
  have hfib : ∀ L : Lat 𝔐.ξ 𝔐.Li, 𝔐.M.fibAt L z MC = Submodule.span O'
      {x | ∃ e ∈ (L ⟨centre z, h⟩ : Set 𝔐.Li),
        𝔐.M.ValAt (Spec.map (CommRingCat.ofHom (algebraMap O' C)) ≫ z) e (MC.pt x)} := fun L => by
    unfold LieModel.fibAt
    congr 1
    ext x
    exact ⟨fun ⟨_, e, h1, h2⟩ => ⟨e, h1, h2⟩, fun ⟨e, h1, h2⟩ => ⟨h, e, h1, h2⟩⟩
  rw [hfib, hfib]
  refine alg_main (A := 𝔐.X.presheaf.stalk (centre z)) (𝔐.X.presheaf.stalkSpecializes hsp).hom
    (genMap 𝔐.ξ ⟨_, h'⟩) (hξ.inj _) (Scheme.stalkClosedPointTo _).hom (Scheme.stalkClosedPointTo z).hom
    (fun a => congrArg (fun g => g.hom a) (stalk_base (algebraMap O' C) z)) βb gm _ hVal 𝔐.ρ ρC (𝔐.emb s) σ
    ?_ ?_ _ _ w (fun j => f j) hβ ?_ hfW ?_ ?_ ?_ κ κz ?_ ?_
  · intro a
    obtain ⟨_, t, h1, h2⟩ := hσ a
    exact ⟨t, (hgk t).trans h1, h2⟩
  · intro a e x hx
    haveI := 𝔐.t.act.hom a
    exact valAt_act 𝔐.M MC _ _ _ (𝔐.act a) (hact a) hx
  · intro j e he
    obtain ⟨t, ht⟩ := 𝔐.M.htOm_le _ _ _ (hw1 j) e he
    exact ⟨t, (hgk t).trans ht⟩
  · intro e he
    obtain ⟨h1, h2⟩ := (𝔐.M.mem_htDual_iff _ _ _ _ _ e).1 he
    refine ⟨h1, fun j => ?_⟩
    obtain ⟨t, ht⟩ := h2 _ (hw1 j)
    exact ⟨t, (hgk t).trans ht⟩
  · intro e he
    have := congrArg Subtype.val (hf2 ⟨e, he⟩)
    simpa [← hw3] using this
  · intro j
    obtain ⟨u, hu'⟩ := (𝔐.M.exists_valAt_iff _ _).2
      ⟨h', htDual_le_lat 𝔐 hpS s ⟨centre z, h⟩ ⟨_, h'⟩ hsp hq hu hq' hreg _ (hfW j)⟩
    obtain ⟨x, rfl⟩ := MC.onto u hu'.isTanAt
    exact ⟨x, hu'⟩
  · obtain ⟨_, t, h1, h2⟩ := hκ
    exact ⟨t, (hgk t).trans h1, h2⟩
  · intro e he
    exact (((hsand _ hq).2.2.2 s).2 e he).1

end PositivityTheory.HtPt.Gh
end

section

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace PositivityTheory.HtPt.Farsharp

variable (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
  (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
  (hp : v (p : C) < 1)


include hv hp in
theorem smul_dUnit_mem (A : Type) [CommRing A] [Bialgebra O A] [IsCocomm O A] [Module.Finite O A]
    [Module.Projective O A] (hfin : {u : A | IsGroupLikeElem O u}.Finite) (q : O) (hq : q ≠ 0)
    (M : Submodule O (Cot O A)) (hM : ∀ u, IsGroupLikeElem O u → dUnit (R := O) u ∈ M)
    (hqM : ∀ y, q • y ∈ M) (κ : O) (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C))
    (y : Cot O A) : κ • y ∈ M := by
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have : ValuationRing O := by
    refine @ValuationRing.mk O _ _ ⟨fun a b => ?_⟩
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inr hc.symm⟩
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inl hc.symm⟩
  let ε := counitAlgHom O A
  let π : A →ₗ[O] A := LinearMap.id - Algebra.linearMap O A ∘ₗ ε.toLinearMap
  have hπ : ∀ a, π a = a - algebraMap O A (ε a) := fun _ => rfl
  let μ : A ⊗[O] A →ₗ[O] A := LinearMap.mul' O A ∘ₗ TensorProduct.map π π
  have hμ : ∀ a b, μ (a ⊗ₜ b) = π a * π b := fun a b => by simp [μ]
  let N : Submodule O A := Submodule.span O {u : A | IsGroupLikeElem O u} ⊔
    (LinearMap.range μ ⊔ LinearMap.range (q • (LinearMap.id : A →ₗ[O] A)))
  have hN : N.FG := (Submodule.fg_span hfin).sup ((Submodule.fg_range _).sup (Submodule.fg_range _))
  have hNM : N ≤ M.comap (AugCot.d ε) := by
    refine sup_le (Submodule.span_le.2 hM) (sup_le ?_ ?_)
    · rintro _ ⟨t, rfl⟩
      induction t with
      | tmul a b =>
        have h0 : ∀ a, ε (π a) = 0 := fun a => by rw [hπ]; simp
        rw [Submodule.mem_comap, hμ, AugCot.d_mul, h0, h0, zero_smul, zero_smul, add_zero]
        exact zero_mem _
      | add x y hx hy =>
        change AugCot.d ε (μ (x + y)) ∈ M
        rw [map_add, map_add]
        exact add_mem hx hy
    · rintro _ ⟨a, rfl⟩
      rw [Submodule.mem_comap, LinearMap.smul_apply, map_smul]
      exact hqM _
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ y
  rw [← map_smul]
  refine hNM (mem_of_forall_dvd N hN hq
    (fun a => Submodule.mem_sup_right (Submodule.mem_sup_right ⟨a, rfl⟩)) _ fun φ hφ => ?_)
  have hu : ∀ u : A, IsGroupLikeElem O u → q ∣ φ u := fun u hu =>
    hφ u (Submodule.mem_sup_left (Submodule.subset_span hu))
  rw [map_smul]
  refine dvd_mul_of_val p C v O hv hp A q hq φ (fun a b => ?_) hu κ hκ a
  have h1 := hφ _ (Submodule.mem_sup_right (Submodule.mem_sup_left ⟨a ⊗ₜ b, rfl⟩))
  have h2 := (hu 1 IsGroupLikeElem.one).mul_left (ε a * ε b)
  have h3 : μ (a ⊗ₜ b) = a * b - ε a • b - ε b • a + (ε a * ε b) • (1 : A) := by
    rw [hμ, hπ, hπ]
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [h3, map_add (f := _), map_sub, map_sub, map_smul, map_smul, map_smul] at h1
  exact (dvd_add_left h2).1 h1


include hv hp in
theorem smul_mem_range_dlogLinear [Algebra ℤ_[p] O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (κ : O) (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C)) (w : G.omega) :
    κ • w ∈ LinearMap.range (dlogLinear G) := by
  have hpp : p.Prime := Fact.out
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2
    ⟨hv.hom_inj, fun hx => hv.exists_of_le_one (hv.mem_of_integral hx)⟩
  have := G.dual.finite_tate C
  have hp0 : (p : O) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h1
    exact Nat.cast_ne_zero.2 hpp.ne_zero h1
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have key : ∀ κ : O, v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C) → ∀ n (y : Cot O (G.A n)),
      κ • y ∈ (LinearMap.range (dlogLinear G)).map (lev G n) := fun κ hκ n y => by
    have hch : ∀ u (hu : IsGroupLikeElem O u),
        charFun O (G.A n) (toConv (evalPoint u hu)) = u := fun u hu =>
      CartierDual.eq_of_forall_apply (R := O) fun φ => apply_charFun _ φ
    have : Finite (CartierDual O (G.A n) →ₐ[O] O) :=
      Nat.finite_of_card_ne_zero ((G.dual.natCard_pts_eq C n).trans_ne (pow_ne_zero _ hpp.ne_zero))
    refine smul_dUnit_mem p C v O hv hp (G.A n)
      ((Set.finite_range fun χ : CartierDual O (G.A n) →ₐ[O] O =>
        charFun O (G.A n) (toConv χ)).subset fun u hu => ⟨_, hch u hu⟩)
      ((p : O) ^ n) (pow_ne_zero _ hp0) _ (fun u hu => ?_)
      (fun y => by rw [pow_smul_cot]; exact zero_mem _) κ hκ y
    obtain ⟨χ, hχ⟩ := G.dual.pt_surjective C n (evalPoint u hu)
    refine ⟨dlog G χ, ⟨1 ⊗ₜ χ, by rw [dlogLinear_tmul, one_smul]⟩, ?_⟩
    rw [lev_apply, dlog_val, ← hch u hu, ← hχ]
    rfl
  refine smul_mem_of_levels G _ (Submodule.fg_range _) κ (key κ hκ) (key p ?_) w
  rw [map_natCast]
  exact pow_le_of_le_one zero_le hp.le (Nat.sub_pos_of_lt hpp.one_lt).ne'

theorem hodgeTateCokerSharp : GlobalTheory.CompanionTheory.Ar.HT.HodgeTateCokerSharp := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO G κ hκ w
  obtain ⟨z, hz⟩ := smul_mem_range_dlogLinear p C v O hv hp G.dual κ hκ w
  rw [← hz]
  clear hz
  induction z with
  | tmul c χ =>
    obtain ⟨t, rfl⟩ := (tateCongr O G.bidual).surjective χ
    exact ⟨c ⊗ₜ t, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩

end PositivityTheory.HtPt.Farsharp
end
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace PositivityTheory.HtPt.Siua

theorem siu_kodaira : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement →
    GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.Statement :=
  siu_kodaira_of PositivityTheory.HtPt.Siub.siu_segre

end PositivityTheory.HtPt.Siua
end
