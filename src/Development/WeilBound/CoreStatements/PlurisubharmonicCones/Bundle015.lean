module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle197
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle246
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle172
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFieldExtension
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle259
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle132
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle253
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle025
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle014
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Imports
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle025
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle258
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace LevelTowerAlt

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ}
  {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_root (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (hx : A.ξ ≫ A.f = x ≫ Y.j) (hpos : 0 < D.p + D.q)
    (p : ℕ) (hp : p ∈ S) : ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ A.R p) := by
  obtain ⟨s0, o, ⟨m0⟩⟩ := GlobalTheory.T.abelian_scheme_point_object E H D l Xo c _ _ Y A.X A.f A.t A.m Ω A.ξ x hx
  let q : Cpt A.ξ := ⟨_, specializes_rfl⟩
  exact (GlobalTheory.T.full_torsion_integrally_closed E H D l (KA l) (baseKA l) A.X Ω A.ξ s0 o A.t m0 A.Li A.M (p ^ A.R p) q A.tie.gen
    (pow_pos (A.S_prime p hp).pos _) (A.tors p hp) (A.normal q.1).2
    (HcptPull.noeth_stalk A.tie.gen q ((GlobalTheory.T.regAt_noetherian_model_noetherian A.X Ω A.ξ ℤ _ _ A.tie).1 q))).2.1 hpos

theorem exists_flagged (hW : Out.WeilSt) (A : HodgeCpt Y S y) (x : Sp Ω ⟶ Xo.XF c) (hx : A.ξ ≫ A.f = x ≫ Y.j) (dg : ℕ)
    (hcov : A.IsCover dg) (hS : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) (hHT : ∀ p ∈ S, HT.HTFree A p) :
    ∃ (Ω' : Type) (_ : Field Ω') (K' : Type) (_ : Fintype K') (J' : K' → Type) (_ : ∀ k, Fintype (J' k))
      (y' : (Σ k, J' k) → Ω') (B : HodgeCpt Y S y') (Fl : B.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K' → ℤ)
      (e : CMType H × Fin (D.p + D.q) → Ω') (i : Ω →+* Ω') (g : B.X ⟶ A.X) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)),
      Nonempty K' ∧ Function.Injective bk ∧ (∀ k a, y' ⟨bk k, bx k a⟩ = i (y ⟨k, a⟩)) ∧
      GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ g i ∧ B.f = g ≫ A.f ∧ B.R = A.R ∧ (∀ p ∈ S, HT.HTFree B p) ∧
      Fl.RootLines xdeg e := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
  · have hd : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ A.ξ (𝟙 _) (RingHom.id Ω) := by
      unfold GlobalTheory.CompanionTheory.Ar.Dominates
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
    obtain ⟨K₃, _, J₃, _, y₃, bk, bx, hne, hinj, hy, hT⟩ := exists_join A.tie A.tie (𝟙 _) (RingHom.id Ω) hd
    obtain ⟨Fl⟩ := flag_zero (reTie A hT) dg hcov h0
    haveI : IsEmpty (CMType H × Fin (D.p + D.q)) := ⟨fun r => by have := r.2.2; omega⟩
    exact ⟨Ω, _, K₃, _, J₃, inferInstance, y₃, reTie A hT, Fl, fun _ => 0, fun _ => 1, RingHom.id Ω, 𝟙 _, bk, bx, hne, hinj, hy, hd,
      (Category.id_comp _).symm, rfl, hHT, isEmptyElim⟩
  · have hζ := exists_root A x hx hpos
    obtain ⟨Ω', _, _, i, K₂, _, J₂, _, y₂, B, g₂, b, Li₀, a₀, m₀, M₀, j, V₀, hg₂, hBf, hBR, hB, hb, hj, hV, hgen⟩ :=
      GlobalTheory.T.hodge_cpt_good_reduction_degree hW E H D l Xo c Y S Ω K J y A x dg hx hS hHT hζ hcov
    have hBy : B.ξ ≫ B.f = (spMap i ≫ x) ≫ Y.j := by
      rw [hBf, ← Category.assoc, hg₂, Category.assoc, hx, Category.assoc]
    obtain ⟨K₃, _, J₃, _, y₃, bk, bx, ⟨k₀⟩, hinj, hy, hT⟩ := exists_join A.tie B.tie g₂ i hg₂
    obtain ⟨K₄, _, J₄, _, y₄, bk', bx', C, g₃, Fl, xdeg, e, hinj', hy', hg₃, hCf, hCR, -, hC, -, -, hroot, -⟩ :=
      GlobalTheory.T.hodge_cpt_label_bases hW E H D l Xo c Y S Ω' K₃ J₃ y₃ (reTie B hT) (spMap i ≫ x) b Li₀ a₀ m₀ M₀ j V₀ dg hBy hS hB
        (fun p hp => by
          obtain ⟨ζ, hζ'⟩ := hζ p hp
          exact ⟨i ζ, by rw [show (reTie B hT).R = A.R from hBR]; exact hζ'.map_of_injective i.injective⟩) hb hj hV hgen
    refine ⟨Ω', _, K₄, _, J₄, inferInstance, y₄, C, Fl, xdeg, e, i, g₃ ≫ g₂, bk' ∘ bk, fun k => (bx k).trans (bx' (bk k)),
      ⟨bk' k₀⟩, hinj'.comp hinj, fun k a => (hy' _ _).trans (hy k a), ?_, ?_, hCR.trans hBR, hC, hroot⟩
    · have h3 : C.ξ ≫ g₃ = B.ξ := by
        have h := hg₃
        unfold GlobalTheory.CompanionTheory.Ar.Dominates at h
        rw [h, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      show C.ξ ≫ g₃ ≫ g₂ = _
      rw [← Category.assoc, h3]
      exact hg₂
    · rw [Category.assoc, ← hBf]; exact hCf

end

theorem hodge_compact_cover_primes : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) [Fintype (CMType H)], 𝔐.IsCover dg → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → (∀ p ∈ S, HT.HTFree 𝔐 p) → ∃ (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐' : HodgeCpt Y S M.y) (Fl : 𝔐'.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (i : Ω →+* M.Ω) (g : 𝔐'.X ⟶ 𝔐.X) (bk : K → M.K) (bx : ∀ k, J k ≃ M.ι (bk k)) (j : 𝔐.Li →+ 𝔐'.Li), Function.Injective bk ∧ (∀ k x, M.y ⟨bk k, bx k x⟩ = i (y ⟨k, x⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐'.ξ 𝔐.ξ g i ∧ (∀ p ∈ S, HT.HTFree 𝔐' p) ∧ Fl.RootLines M.xdeg e ∧ (∀ (a : Ω) v, j (a • v) = i a • j v) ∧ (∀ (n : ℕ) (v : Fin n → 𝔐.Li), LinearIndependent Ω v → LinearIndependent M.Ω fun k => j (v k)) ∧ ∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ g j := by
  intro hW E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y A dg inst hcov hS hHT
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨-, ⟨x, hx⟩, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l (Xo l) c _ _ Y S Ω K J y A hβ
  obtain ⟨Ω', _, K', _, J', _, y', B, Fl, xdeg, e, i, g, bk, bx, hne, hinj, hy, hd, hf, hR, hB, hroot⟩ :=
    exists_flagged hW A x hx dg hcov hS hHT
  obtain ⟨j, hext, hV⟩ := exists_pull A B g i x hx hS (fun p hp => (hHT p hp).2) hd hf hR
  obtain ⟨hbir, har⟩ := GlobalTheory.T.hodge_cpt_birational_arith_var E H D l (Xo l) c _ _ Y S Ω' K' J' y' B Fl hβ
  have har' : IsArithVar (mCoordIdeal y') (@Fintype.card (CMType H) inst * ((D.p + D.q) * (D.p + D.q - 1) / 2) + 1) := by
    convert har
  choose L hL using GlobalTheory.T.exists_smooth_conj_invariant_metric K' J'
  exact ⟨{ K := K', «ι» := J', Ω := Ω', y := y', arith := har', birational := hbir, xdeg := xdeg,
           x := fun _ r => L (xdeg r), x_deg := fun _ _ => (hL _).1, x_smooth := fun _ _ => (hL _).2.1,
           x_conj := fun _ _ => (hL _).2.2, kA := 1, kA_pos := one_pos, A := L 0, A_smooth := (hL _).2.1,
           A_conj := (hL _).2.2, δ := 1, δ_pos := one_pos },
    B, Fl, e, i, g, bk, bx, j, hinj, hy, hd, hB, hroot, hext.1, hext.2, hV⟩

end LevelTowerAlt
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace LevelTowerAlt.Gram

theorem exists_gram : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (x : Sp ℂ ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), (∀ i, IsTanAt t.G x (v i)) → ∃ Γ : Matrix (Fin n) (Fin n) ℂ, IsHodgeGram t.G t.PP.L x v Γ := by
  intro E _ _ _ H S t hp hA hK x n v hv
  obtain ⟨Q, ψ, -, hQ, hQL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H S t hp hA hK ℂ x
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, Hm, χ, -, hAH, -, d₁, -⟩ := GlobalTheory.thetaUnifAV_all Q rig hrig
  have hl : ∀ a, ∃ t' : epsR ℂ ⟶ Q.A, t'.left ≫ ψ = (v a).left ∧ IsTangent t' := by
    intro a
    have sq : (v a).left ≫ t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x := Over.w (v a)
    let t' : epsR ℂ ⟶ Q.A := Over.homMk (hQ.1.lift _ _ sq) (hQ.1.lift_snd _ _ _)
    have h1 : t'.left ≫ ψ = (v a).left := hQ.1.lift_fst _ _ _
    refine ⟨t', h1, (ReciprocityTheory.ChartRestriction.G.Chart.tan_push hQ t').2 ?_⟩
    rw [h1]
    exact hv a
  choose t' h1 h2 using hl
  choose W hW _ using fun a => d₁ (t' a) (h2 a)
  exact ⟨Matrix.of fun a b => Real.pi * hermForm Hm (W a) (W b), Q, ψ, t', u, Hm, χ, W, hQ, hQL.symm, hAH,
    fun a => ⟨h1 a, hW a⟩, fun _ _ => rfl⟩

theorem gram_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (Γ Γ' : Matrix (Fin n) (Fin n) ℂ), L.IsLB → (∀ i, IsTanAt G x (v i)) → IsHodgeGram G L x v Γ → (∀ p q, HodgeIP G L x (v p) (v q) (Γ' p q)) → Γ' = Γ.transpose := by
  intro S G _ L x n v Γ Γ' hL hv hG hIP
  obtain ⟨Q, ψ, v', u, Hm, χ, W, hp, hiso, hAH, hvW, hΓ⟩ := hG
  have hM := pull_isLB hL ψ
  obtain ⟨w, hw⟩ := LBIso.symm hiso
  obtain ⟨ht₁, ht₂, -⟩ := GlobalTheory.AnyUnif.tangent_and_unimodular GlobalTheory.thetaUnifAV_all Q u
  have htan : ∀ a, IsTangent (v' a) := fun a =>
    (ReciprocityTheory.ChartRestriction.G.Chart.tan_push hp (v' a)).2 (by rw [(hvW a).1]; exact hv a)
  ext p q
  obtain ⟨-, -, -, A, _, φ, g, u', Hm', χ', a', b', a, b, h1, h2, h3, h4, h5, h6, e⟩ :=
    hodgeInnerProduct_iff_hodgeForm.1 (hIP p q)
  have key := GlobalTheory.T.hol_unif_compare_isogeny S G L x Q.A A ψ φ Q.g g (GlobalTheory.TorsionTauCompare.transport Q.isLB hM hw u) u' Hm Hm' χ χ'
    hL Q.isAb hp h1 ht₁ ht₂ (GlobalTheory.TorsionTauCompare.isAH_transport Q.isLB hM hw u hAH) h2 (v' q) (v' p) a' b' (W q) (W p) a b
    (htan q) (htan p) (h3.trans (hvW q).1.symm) (h4.trans (hvW p).1.symm) (hvW q).2 (hvW p).2 h5 h6
  rw [e, key, Matrix.transpose_apply, hΓ]

end LevelTowerAlt.Gram
end
