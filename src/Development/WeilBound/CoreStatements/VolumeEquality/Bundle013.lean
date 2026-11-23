module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle072
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle190
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle027
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle118
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle048
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle009
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove GlobalTheory.VerticalDeriv GlobalTheory.FibreDeriv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'}
  {f : X' ⟶ X} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {R : RiemLat E g Λ}

theorem fibreLatVec_move (m : SABMap t' t f) {z : Sp ℂ ⟶ X'} {z₀ : Sp ℂ ⟶ X} (hz : z ≫ f = z₀) {A₀ : Type}
    (x : A₀ → Fin g → ℂ) (v' : A₀ → (epsAt z ⟶ t'.G)) (v : A₀ → (epsAt z₀ ⟶ t.G)) (hv : ∀ i, (v' i).left ≫ m.φ = (v i).left) :
    FibreLatVec t' z R x v' ↔ FibreLatVec t z₀ R x v := by
  subst hz
  constructor
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩
    obtain ⟨w, hw, -⟩ := m.lin
    obtain ⟨v₁, hv₁⟩ := lbIso_pull (L' := t'.PP.L) (L := t.PP.L) ⟨w, hw⟩ φ
    have h₁ := pull_isLB t'.PP.isLB φ
    have h₂ := pull_isLB t.PP.isLB (φ ≫ m.cm.F)
    refine ⟨A, inferInstance, φ ≫ m.cm.F, GlobalTheory.ArchMetricCompare.carry u h₁ h₂ hv₁, χ, hpb.comp m.cart,
      GlobalTheory.ArchMetricCompare.carry_isAH h₁ h₂ hv₁ hAH, fun a p => ?_, hinj, hmem, fun i => ?_⟩
    · show (u.ex (R.B a p)).left ≫ φ ≫ m.cm.F = (u.ex p).left ≫ (φ ≫ m.cm.F) ≫ (t.act.act a).left
      rw [← Category.assoc, hact a p, Category.assoc, Category.assoc, Category.assoc, m.act a]
    · obtain ⟨w₁, e₁, d₁⟩ := hvec i
      exact ⟨w₁, by rw [← Category.assoc, e₁]; exact hv i, d₁⟩
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩
    have hp := m.cart.1
    obtain ⟨F, rfl, hw⟩ : ∃ F : A.left ⟶ t'.G.left, F ≫ m.cm.F = φ ∧ F ≫ t'.G.hom = A.hom ≫ z :=
      ⟨hp.lift φ (A.hom ≫ z) (by rw [hpb.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
    obtain ⟨w, hw', -⟩ := m.lin
    obtain ⟨v₁, hv₁⟩ := (lbIso_pull (L' := t'.PP.L) (L := t.PP.L) ⟨w, hw'⟩ F).symm
    have h₁ := pull_isLB t'.PP.isLB F
    have h₂ := pull_isLB t.PP.isLB (F ≫ m.cm.F)
    refine ⟨A, inferInstance, F, GlobalTheory.ArchMetricCompare.carry u h₂ h₁ hv₁, χ, m.cart.cancel hpb hw,
      GlobalTheory.ArchMetricCompare.carry_isAH h₂ h₁ hv₁ hAH, fun a p => ?_, hinj, hmem, fun i => ?_⟩
    · show (u.ex (R.B a p)).left ≫ F = (u.ex p).left ≫ F ≫ (t'.act.act a).left
      apply hp.hom_ext
      · have e := hact a p
        simp only [Category.assoc] at e ⊢
        rw [m.act a]
        exact e
      · simp only [Category.assoc]
        rw [Over.w (t'.act.act a), hw, ← Category.assoc, ← Category.assoc, Over.w (u.ex _), Over.w (u.ex _)]
    · obtain ⟨w₁, e₁, d₁⟩ := hvec i
      refine ⟨w₁, hp.hom_ext ?_ ?_, d₁⟩
      · rw [Category.assoc, e₁]
        exact (hv i).symm
      · rw [Category.assoc, hw, ← Category.assoc, Over.w w₁, Over.w (v' i)]
        rfl

structure GoodExp (t : SAB H X) (z : Sp ℂ ⟶ X) (R : RiemLat E g Λ) (h : (Fin g → ℂ) → Fin g → ℂ)
    (e : (Fin g → ℂ) → (Sp ℂ ⟶ t.G.left)) : Prop where
  hol : IsHolTo Set.univ e
  vert : ∀ ζ, e ζ ≫ t.G.hom = z
  zero : e 0 = (1 : Over.mk z ⟶ t.G).left
  uniq : ∀ w₁ w₂ u, IsDerivAt0 e w₁ u → IsDerivAt0 e w₂ u → w₁ = w₂
  onto : ∀ u : Sp (DualNumber ℂ) ⟶ t.G.left, u ≫ t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ z →
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ u = e 0 → ∃ w, IsDerivAt0 e w u
  lat : ∀ (A₀ : Type) (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt z ⟶ t.G)), (∀ a, IsDerivAt0 e (h (x a)) (v a).left) →
    FibreLatVec t z R x v

theorem fst_alg : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap (algebraMap ℂ (DualNumber ℂ)) = 𝟙 (Sp ℂ) := by
  unfold spMap
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

variable {h : (Fin g → ℂ) → Fin g → ℂ}

theorem GoodExp.push (m : SABMap t' t f) {z : Sp ℂ ⟶ X'} {z₀ : Sp ℂ ⟶ X} (hz : z ≫ f = z₀)
    {e' : (Fin g → ℂ) → (Sp ℂ ⟶ t'.G.left)} (G : GoodExp t' z R h e') : GoodExp t z₀ R h fun ζ => e' ζ ≫ m.φ := by
  have hp := m.cart.1
  have key : ∀ w u, IsDerivAt0 (fun ζ => e' ζ ≫ m.φ) w u → ∃ u', IsDerivAt0 e' w u' ∧ u' ≫ m.φ = u ∧
      u' ≫ t'.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ z := fun w u hu => by
    obtain ⟨u', hu'⟩ := exists_isDerivAt0 G.hol w
    exact ⟨u', hu', isDerivAt0_unique (isDerivAt0_comp hu' m.φ) hu, isDerivAt0_vertical _ _ G.vert hu'⟩
  refine ⟨GlobalTheory.HolTorsion.isHolTo_comp G.hol _, fun ζ => ?_, ?_, fun w₁ w₂ u h₁ h₂ => ?_, fun u hu h0 => ?_,
    fun A₀ x v hv => ?_⟩
  · rw [Category.assoc, hp.w, ← Category.assoc, G.vert, hz]
  · subst hz
    rw [G.zero]
    exact LiePull.one_left m.cart z
  · obtain ⟨u₁, a₁, b₁, c₁⟩ := key _ _ h₁
    obtain ⟨u₂, a₂, b₂, c₂⟩ := key _ _ h₂
    have : u₁ = u₂ := hp.hom_ext (b₁.trans b₂.symm) (c₁.trans c₂.symm)
    subst this
    exact G.uniq _ _ _ a₁ a₂
  · have hc : u ≫ t.G.hom = (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ z) ≫ f := by rw [hu, Category.assoc, hz]
    obtain ⟨w, hw⟩ := G.onto (hp.lift u _ hc) (hp.lift_snd _ _ _) (hp.hom_ext
      (by rw [Category.assoc, hp.lift_fst]; exact h0)
      (by rw [Category.assoc, hp.lift_snd, ← Category.assoc, fst_alg, Category.id_comp, G.vert]))
    have := isDerivAt0_comp hw m.φ
    rw [show hp.lift u _ hc ≫ m.φ = u from hp.lift_fst _ _ _] at this
    exact ⟨w, this⟩
  · choose u' a b c using fun a => key _ _ (hv a)
    let v' : A₀ → (epsAt z ⟶ t'.G) := fun a => Over.homMk (u' a) (c a)
    exact (fibreLatVec_move m hz x v' v b).1 (G.lat A₀ x v' a)

theorem GoodExp.pull (m : SABMap t' t f) {z : Sp ℂ ⟶ X'} {z₀ : Sp ℂ ⟶ X} (hz : z ≫ f = z₀)
    {e : (Fin g → ℂ) → (Sp ℂ ⟶ t.G.left)} (G : GoodExp t z₀ R h e) {e' : (Fin g → ℂ) → (Sp ℂ ⟶ t'.G.left)}
    (hol : IsHolTo Set.univ e') (h₁ : ∀ ζ, e' ζ ≫ m.φ = e ζ) (h₂ : ∀ ζ, e' ζ ≫ t'.G.hom = z) : GoodExp t' z R h e' := by
  have hp := m.cart.1
  have he : (fun ζ => e' ζ ≫ m.φ) = e := funext h₁
  have key : ∀ w u, IsDerivAt0 e' w u → IsDerivAt0 e w (u ≫ m.φ) := fun w u hu => he ▸ isDerivAt0_comp hu m.φ
  refine ⟨hol, h₂, ?_, fun w₁ w₂ u a₁ a₂ => G.uniq _ _ _ (key _ _ a₁) (key _ _ a₂), fun u hu h0 => ?_, fun A₀ x v hv => ?_⟩
  · subst hz
    refine hp.hom_ext ?_ ?_
    · rw [h₁, G.zero]
      exact (LiePull.one_left m.cart z).symm
    · rw [h₂, Over.w]
      rfl
  · obtain ⟨w, hw⟩ := G.onto (u ≫ m.φ) (by rw [Category.assoc, hp.w, ← Category.assoc, hu, Category.assoc, hz])
      (by rw [← Category.assoc, h0, h₁])
    obtain ⟨u', hu'⟩ := exists_isDerivAt0 hol w
    have : u' = u := hp.hom_ext (isDerivAt0_unique (key _ _ hu') hw) ((isDerivAt0_vertical _ _ h₂ hu').trans hu.symm)
    exact ⟨w, this ▸ hu'⟩
  · let v₀ : A₀ → (epsAt z₀ ⟶ t.G) := fun a => Over.homMk ((v a).left ≫ m.φ) (by
      rw [Category.assoc, hp.w, ← Category.assoc, Over.w (v a), ← hz]
      exact Category.assoc _ _ _)
    exact (fibreLatVec_move m hz x v v₀ fun _ => rfl).2 (G.lat A₀ x v₀ fun a => key _ _ (hv a))

end SheetDecomposition
end
end

section

noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem vecAt_conj {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
    {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R R' : (Fin n → ℂ) → RiemLat E g Λ) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (t₀ : Fin n → ℂ)
    (hR : ∀ t, (∀ x, (R' t).P x = star ((R (star t)).P x)) ∧ (R' t).Hm = (R (star t)).Hm.map (starRingEnd ℂ) ∧
      ∀ a x, (R' t).B a x = star ((R (star t)).B a (star x)))
    (h : VecAt 𝔐 R (fun t => spMap (starRingEnd ℂ) ≫ z (star t)) (star t₀)) : VecAt 𝔐 R' z t₀ := by
  intro m s hs
  obtain ⟨x, hx, hev⟩ := h m s fun a => by
    obtain ⟨v, hv⟩ := hs a
    show ∃ v, 𝔐.M.ValAt (spMap (starRingEnd ℂ) ≫ z (star (star t₀))) (s a) v
    rw [star_star]
    exact ⟨_, Cj.valAt_conj 𝔐.M _ _ v hv⟩
  refine ⟨fun a t => star (x a (star t)), fun a => Cj.analyticAt_star_star (hx a), ?_⟩
  filter_upwards [(continuous_star.continuousAt (x := t₀)).tendsto.eventually hev] with t ht
  obtain ⟨v, hv, hF⟩ := ht
  have key : ∀ (w w' : Sp ℂ ⟶ 𝔐.X) (v : Fin m → (epsAt w ⟶ 𝔐.t.G)), w' = spMap (starRingEnd ℂ) ≫ w →
      (∀ a, 𝔐.M.ValAt w (s a) (v a)) → FibreLatVec 𝔐.t w (R (star t)) (fun a => x a (star t)) v →
      ∃ v' : Fin m → (epsAt w' ⟶ 𝔐.t.G), (∀ a, 𝔐.M.ValAt w' (s a) (v' a)) ∧
        FibreLatVec 𝔐.t w' (R' t) (fun a => star (x a (star t))) v' := by
    rintro w _ v rfl hv hF
    exact ⟨fun a => Cj.cjVec w (v a), fun a => Cj.valAt_conj 𝔐.M w _ _ (hv a),
      Cj.fibreLatVec_conj 𝔐.t w _ _ _ v (hR t).1 (hR t).2.1 (hR t).2.2 (fun a => (hv a).isTanAt) hF⟩
  exact key _ _ v (by rw [Cj.cj_cj, star_star]) hv hF

theorem kUnifConj : KUnifConj := by
  rintro E _ _ _ H D l Xo c Y sm j j' n g q κ ⟨U⟩
  choose F' hq hσ hform hR using fun k => GlobalTheory.T.conjugate_universal_family E (CMType H) j j' n g (U.Di k).La (U.F k)
  have hcanc : ∀ {X : Scheme.{0}} {a b : Sp ℂ ⟶ X}, spMap (starRingEnd ℂ) ≫ a = spMap (starRingEnd ℂ) ≫ b → a = b :=
    fun {X a b} e => by rw [← Cj.cj_cj a, e, Cj.cj_cj]
  have hs : spMap (((starRingEnd ℂ).comp κ).comp (algebraMap (𝓞 c.F) c.F)) =
      spMap (starRingEnd ℂ) ≫ spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) :=
    Spec.map_comp (CommRingCat.ofHom (κ.comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))
  refine ⟨{
    ι := U.ι
    fin := U.fin
    Di := U.Di
    sig := U.sig
    F := F'
    q_eq := fun k => (hq k).trans (U.q_eq k)
    form_eq := fun k => ?_
    σ_eq := fun k τ => ?_
    Γ := U.Γ
    mem_Γ := U.mem_Γ
    arith := fun k => ?_
    pt := fun k t => spMap (starRingEnd ℂ) ≫ U.pt k (star t)
    hol := fun k => ?_
    comp_s_eq_spMap_of_isOver := fun k t ht => ?_
    interior := fun k t ht => ?_
    disj := fun k k' t ht t' ht' e =>
      U.disj k k' _ (Cj.star_mem_ballDom ht) _ (Cj.star_mem_ballDom ht') (hcanc e)
    fibre := fun k t ht t' ht' => ?_
    onto := fun p hp hps => ?_
    lat := fun k t ht => ?_
    vec := fun S Ω _ K _ J _ y 𝔐 k V z hV hVs hz hzf t₀ ht₀ => ?_
    locc := fun m T y hT hTc hy hyi hys b hb b' hb' k k' t ht t' ht' e e' => ?_ }⟩
  · rw [hform]
    rcases U.form_eq k with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  · rw [hσ, U.σ_eq]
    rfl
  · have h := U.arith k
    unfold UnivFam.IsArith at h ⊢
    rwa [hform, Cj.autGrp_neg]
  · have h := GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ (U.hol k)
    rwa [Cj.preimage_star_ballDom] at h
  · rw [Category.assoc, U.comp_s_eq_spMap_of_isOver k _ (Cj.star_mem_ballDom ht), hs]
  · rw [Cj.centre_conj]
    exact U.interior k _ (Cj.star_mem_ballDom ht)
  · have h := U.fibre k _ (Cj.star_mem_ballDom ht) _ (Cj.star_mem_ballDom ht')
    constructor
    · intro e
      obtain ⟨γ, hγ, he⟩ := h.1 (hcanc e)
      exact ⟨γ, hγ, Cj.eqvBy_conj (hR k t).1 (hR k t').1 he⟩
    · rintro ⟨γ, hγ, he⟩
      have e := h.2 ⟨γ, hγ, Cj.eqvBy_conj (fun x => by rw [(hR k t).1, star_star])
        (fun x => by rw [(hR k t').1, star_star]) he⟩
      show spMap (starRingEnd ℂ) ≫ U.pt k (star t) = spMap (starRingEnd ℂ) ≫ U.pt k (star t')
      rw [e]
  · obtain ⟨k, t, ht, e⟩ := U.onto (spMap (starRingEnd ℂ) ≫ p) (by rwa [Cj.centre_conj])
      (by rw [Category.assoc, hps, hs, Cj.cj_cj])
    refine ⟨k, star t, Cj.star_mem_ballDom ht, ?_⟩
    show spMap (starRingEnd ℂ) ≫ U.pt k (star (star t)) = p
    rw [star_star, e, Cj.cj_cj]
  · have h := Cj.fibreLatVec_conj Y.t _ _ ((F' k).R t) _ _ (hR k t).1 (hR k t).2.1 (hR k t).2.2 (fun a => a.elim)
      (U.lat k _ (Cj.star_mem_ballDom ht))
    obtain ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, -⟩ := h
    exact ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, fun a => a.elim⟩
  · refine vecAt_conj 𝔐 (U.F k).R (F' k).R z t₀ (hR k) ?_
    refine U.vec S Ω K J y 𝔐 k (star ⁻¹' V) _ (hV.preimage continuous_star) (fun t ht => ?_)
      (GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ hz) (fun t ht => ?_) _ (by simpa using ht₀)
    · simpa using Cj.star_mem_ballDom (hVs ht)
    · rw [Category.assoc, hzf _ ht, Cj.cj_cj, star_star]
  · have hpre : IsPreconnected (star ⁻¹' T : Set (Fin m → ℂ)) := by
      have e₀ : (star ⁻¹' T : Set (Fin m → ℂ)) = star '' T := by
        ext x
        constructor
        · intro h
          exact ⟨star x, h, star_star x⟩
        · rintro ⟨a, ha, rfl⟩
          show star (star a) ∈ T
          rwa [star_star]
      rw [e₀]
      exact hTc.image _ continuous_star.continuousOn
    refine U.locc m (star ⁻¹' T) _ (hT.preimage continuous_star) hpre (GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ hy) (fun a ha => ?_)
      (fun a ha => ?_) (star b) (by simpa using hb) (star b') (by simpa using hb') k k' _ (Cj.star_mem_ballDom ht) _
      (Cj.star_mem_ballDom ht') ?_ ?_
    · rw [Cj.centre_conj]
      exact hyi _ ha
    · rw [Category.assoc, hys _ ha, hs, Cj.cj_cj]
    · show spMap (starRingEnd ℂ) ≫ y (star (star b)) = _
      rw [star_star, e, Cj.cj_cj]
    · show spMap (starRingEnd ℂ) ≫ y (star (star b')) = _
      rw [star_star, e', Cj.cj_cj]

end SheetDecomposition
end
end
