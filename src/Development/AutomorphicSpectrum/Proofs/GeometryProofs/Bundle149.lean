module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle015
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle132
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle086
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle142
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle099
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ImaginaryRootConj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle028
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle133
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle143
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle144
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle022
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle031
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LabPt

theorem valAt_of_const {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    {O : Type} [CommRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) {R : Type} [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of R) ⟶ X) (ρ : O →+* R) (hz : z ≫ s = Spec.map (CommRingCat.ofHom ρ))
    (h : genPt ξ ⤳ centre z) (o : O) : ValAt ξ z (algebraMap O Ω o) (ρ o) := by
  refine ⟨h, (X.presheaf.germ ⊤ (centre z) trivial).hom
    (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)),
    Flat.ConstReg.genMap_germ_const ξ s hs ⟨centre z, h⟩ o, ?_⟩
  have h1 : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  have h1' := congrArg (fun q => q.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  refine h1'.trans ?_
  have h2 : z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
    rw [← hz]; simp only [Scheme.Hom.comp_appTop]; rfl
  have h3 := congrArg (fun q => q.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (ρ o) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := h3
  show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = ρ o
  rw [h2, ← h3']
  simp

theorem valAt_unique {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hξ : IsCptGen ξ)
    {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X)
    (h : genPt ξ ⤳ centre z) {a : Ω} {r r' : R} (h₁ : ValAt ξ z a r) (h₂ : ValAt ξ z a r') : r = r' := by
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  obtain ⟨_, e₁⟩ := (hφ a r).1 h₁
  obtain ⟨_, e₂⟩ := (hφ a r').1 h₂
  exact e₁.symm.trans e₂

theorem injective_of_charZero {A : Type} [CommRing A] [IsDomain A] [Algebra.IsIntegral ℤ A] {L : Type} [Field L]
    [CharZero L] (t : A →+* L) : Function.Injective t := by
  have hk : RingHom.ker t = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    ext n
    simp [Ideal.mem_comap, RingHom.mem_ker]
  exact (RingHom.injective_iff_ker_eq_bot t).2 hk

theorem card_hom_le (E : Type) [Field E] [NumberField E] (L : Type) [Field L] [CharZero L] :
    Finite (𝓞 E →+* L) ∧ Nat.card (𝓞 E →+* L) ≤ Module.finrank ℚ E := by
  let f : (𝓞 E →+* L) → (E →ₐ[ℚ] AlgebraicClosure L) := fun t =>
    ((algebraMap L (AlgebraicClosure L)).comp
      (IsFractionRing.lift (K := E) (injective_of_charZero t))).toRatAlgHom
  have hf : Function.Injective f := by
    intro t t' h
    refine RingHom.ext fun a => (algebraMap L (AlgebraicClosure L)).injective ?_
    have := DFunLike.congr_fun h (algebraMap (𝓞 E) E a)
    simpa [f] using this
  have hc : Nat.card (E →ₐ[ℚ] AlgebraicClosure L) = Module.finrank ℚ E := by
    rw [Nat.card_eq_fintype_card, AlgHom.card]
  haveI : Finite (𝓞 E →+* L) := Finite.of_injective f hf
  exact ⟨inferInstance, (Nat.card_le_card_of_injective f hf).trans hc.le⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bijective_of_injective (H : Host E) {L : Type} [Field L] [CharZero L]
    (f : CMType H ⊕ CMType H → (𝓞 E →+* L)) (hf : Function.Injective f) : Function.Bijective f := by
  obtain ⟨hfin, hle⟩ := card_hom_le E L
  refine hf.bijective_of_nat_card_le (hle.trans ?_)
  rw [Nat.card_eq_of_bijective _ (LabelCount.labelCx_bijective H), Nat.card_eq_fintype_card,
    NumberField.Embeddings.card]

theorem isCMFam_of_bijective {A : Type} [Fintype A] (f g : A → (𝓞 E →+* ℂ))
    (hb : Function.Bijective (Sum.elim f g)) (hc : ∀ τ, g τ = (starRingEnd ℂ).comp (f τ)) :
    IsCMFam f ∧ IsCMFam g := by
  have cc : ∀ s : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s :=
    fun s => RingHom.ext fun a => by simp
  have hf : Function.Injective f := fun a b h =>
    Sum.inl_injective (hb.1 (a₁ := .inl a) (a₂ := .inl b) h)
  have hg : Function.Injective g := fun a b h =>
    Sum.inr_injective (hb.1 (a₁ := .inr a) (a₂ := .inr b) h)
  have hd : ∀ a b, f a ≠ g b := fun a b h => by
    have := hb.1 (a₁ := .inl a) (a₂ := .inr b) h
    simp at this
  refine ⟨⟨hf, fun s => ⟨?_, fun hn => ?_⟩⟩, ⟨hg, fun s => ⟨?_, fun hn => ?_⟩⟩⟩
  · rintro ⟨τ, rfl⟩ ⟨τ', h⟩
    exact hd τ' τ (h.trans (hc τ).symm)
  · obtain ⟨x, hx⟩ := hb.2 s
    rcases x with τ | τ
    · exact ⟨τ, hx⟩
    · have hx' : g τ = s := hx
      exact absurd ⟨τ, by rw [← hx', hc, cc]⟩ hn
  · rintro ⟨τ, rfl⟩ ⟨τ', h⟩
    refine hd τ τ' (Eq.symm (h.trans ?_))
    rw [hc, cc]
  · obtain ⟨x, hx⟩ := hb.2 s
    rcases x with τ | τ
    · have hx' : f τ = s := hx
      exact absurd ⟨τ, by rw [← hx', hc]⟩ hn
    · exact ⟨τ, hx⟩

theorem exists_labVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ 𝔐.X), ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* L), 𝔐.LabVal z id σ ∧ (∀ σ', 𝔐.LabVal z id σ' → σ' = σ) ∧ Function.Bijective σ ∧ (∀ s, Function.Injective (σ s)) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E ∧ ∀ e : L →+* ℂ, IsCMFam (fun τ => e.comp (σ (.inl τ))) ∧ IsCMFam (fun τ => e.comp (σ (.inr τ))) ∧ ∀ τ, e.comp (σ (.inr τ)) = (starRingEnd ℂ).comp (e.comp (σ (.inl τ))) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 L _ _ z
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { }
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 c.F →+* L, spMap ρ = z ≫ 𝔐.f ≫ Y.s :=
    ⟨(Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom, by simp [spMap]⟩
  let κ : c.F →+* L := IsFractionRing.lift (injective_of_charZero ρ)
  have hκ : ∀ o, κ (algebraMap (𝓞 c.F) c.F o) = ρ o := fun o => IsFractionRing.lift_algebraMap _ o
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have hsp : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hval : ∀ (s : CMType H ⊕ CMType H) (a : 𝓞 E), ValAt 𝔐.ξ z (𝔐.emb s a) (κ (labelEmb c s a)) := by
    intro s a
    have hint : IsIntegral ℤ (labelEmb c s a) :=
      (NumberField.RingOfIntegers.isIntegral a).map (labelEmb c s).toIntAlgHom
    have hm : algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = labelEmb c s a :=
      IsIntegralClosure.algebraMap_mk' _ _ hint
    have h := valAt_of_const 𝔐.ξ (𝔐.f ≫ Y.s) 𝔐.cst_over z ρ hρ.symm hsp (IsIntegralClosure.mk' (𝓞 c.F) _ hint)
    have he : algebraMap (𝓞 c.F) Ω (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = 𝔐.emb s a := by
      show 𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint)) = 𝔐.cst (labelEmb c s a)
      rw [hm]
    rw [he, ← hκ, hm] at h
    exact h
  let σ : CMType H ⊕ CMType H → (𝓞 E →+* L) := fun s => κ.comp (labelEmb c s)
  have hinj : ∀ {L' : Type} [Field L'] (κ' : c.F →+* L'),
      Function.Injective fun s : CMType H ⊕ CMType H => κ'.comp (labelEmb c s) := fun κ' s t h =>
    LabelCount.labelEmb_injective c (RingHom.ext fun a => κ'.injective (RingHom.congr_fun h a))
  have hconj : ∀ (e : L →+* ℂ) (τ : CMType H),
      e.comp (σ (.inr τ)) = (starRingEnd ℂ).comp (e.comp (σ (.inl τ))) := by
    intro e τ
    refine RingHom.ext fun a => ?_
    let ψ : E →+* ℂ := (e.comp κ).comp (τ.1.codRestrict c.F (c.conj τ.1))
    show ψ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (ψ (a : E))
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  refine ⟨σ, hval, fun σ' h' => ?_, bijective_of_injective H σ (hinj κ), fun s => injective_of_charZero _, ?_,
    fun e => ?_⟩
  · funext s
    refine RingHom.ext fun a => ?_
    exact valAt_unique 𝔐.ξ 𝔐.tie.gen z hsp (h' s a) (hval s a)
  · have h := (LabelCount.labels_injective_card E H l c c.F (RingHom.id _)).2
    rw [Fintype.card_sum] at h
    omega
  · have hb : Function.Bijective (fun s => e.comp (σ s)) :=
      bijective_of_injective H _ (hinj (e.comp κ))
    have hb' : Function.Bijective (Sum.elim (fun τ => e.comp (σ (.inl τ))) fun τ => e.comp (σ (.inr τ))) := by
      convert hb using 1
      funext s
      rcases s with τ | τ <;> rfl
    obtain ⟨h1, h2⟩ := isCMFam_of_bijective _ _ hb' (hconj e)
    exact ⟨h1, h2, hconj e⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.LabPt
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.DetLine

theorem matrix_eq_mul {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b₀ c b : Fin r → E}
    {T T' A : Matrix (Fin r) (Fin r) Ω} (hb₀ : LinearIndependent Ω b₀)
    (hT : ∀ k, c k = ∑ k', T k' k • b₀ k') (hT' : ∀ k, b k = ∑ k', T' k' k • b₀ k')
    (hA : ∀ k, b k = ∑ i, A i k • c i) : T' = T * A := by
  ext i k
  have h : ∑ k', (T' k' k - (T * A) k' k) • b₀ k' = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Finset.sum_smul, ← hT']
    rw [sub_eq_zero, hA k, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, _root_.mul_comm]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb₀ _ h i)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem det_mem_span (L : Lat ξ E) {r : ℕ} {b₀ c b : Fin r → E} {q : Cpt ξ} {T T' : Matrix (Fin r) (Fin r) Ω}
    (hb₀ : LinearIndependent Ω b₀) (hc : L.IsFrameAt c q) (hb : L.IsFrameAt b q)
    (hT : ∀ k, c k = ∑ k', T k' k • b₀ k') (hT' : ∀ k, b k = ∑ k', T' k' k • b₀ k') :
    T'.det ∈ Submodule.span (regAt ξ q) {T.det} := by
  have hmem : ∀ k, b k ∈ Submodule.span (regAt ξ q) (Set.range c) := fun k => by
    rw [← hc.2, hb.2]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun k => (Submodule.mem_span_range_iff_exists_fun (regAt ξ q)).1 (hmem k)
  let M : Matrix (Fin r) (Fin r) (regAt ξ q) := Matrix.of fun i k => a k i
  have hM : T' = T * (regAt ξ q).subtype.mapMatrix M :=
    matrix_eq_mul hb₀ hT hT' fun k => (ha k).symm
  refine Submodule.mem_span_singleton.2 ⟨M.det, ?_⟩
  rw [hM, Matrix.det_mul, ← RingHom.map_det, _root_.mul_comm]
  rfl

theorem isVB_detLat : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E]
    (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ →
    Submodule.span Ω (Set.range b₀) = V → L.IsVB r V → (Cusp.detLat L b₀).IsVB 1 ⊤ := by
  intro X Ω _ ξ E _ _ L r V b₀ hb₀ hsp hL p _
  obtain ⟨U, hU, c, hc, hf⟩ := hL p trivial
  have hcV : ∀ k, c k ∈ Submodule.span Ω (Set.range b₀) := fun k => by
    rw [hsp, ← hc]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hbV : ∀ k, b₀ k ∈ Submodule.span Ω (Set.range c) := fun k => by
    rw [hc, ← hsp]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hcV k)
  choose s hs using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hbV k)
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun i k => a k i
  let S : Matrix (Fin r) (Fin r) Ω := Matrix.of fun i k => s k i
  have hT : ∀ k, c k = ∑ k', T k' k • b₀ k' := fun k => (ha k).symm
  have hTS : (1 : Matrix (Fin r) (Fin r) Ω) = T * S :=
    matrix_eq_mul hb₀ hT (fun k => by simp [Matrix.one_apply, ite_smul]) fun k => (hs k).symm
  have ht : T.det ≠ 0 := fun h => by
    have := congrArg Matrix.det hTS
    rw [Matrix.det_one, Matrix.det_mul, h, zero_mul] at this
    exact one_ne_zero this
  refine ⟨U, hU, fun _ => T.det, ?_, fun q _ hq => ⟨?_, ?_⟩⟩
  · refine eq_top_iff.2 fun x _ => ?_
    have hx : x = (x * T.det⁻¹) • T.det := by
      rw [smul_eq_mul, _root_.mul_assoc, inv_mul_cancel₀ ht, _root_.mul_one]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · exact linearIndependent_unique_iff.2 ht
  · have hr : Set.range (fun _ : Fin 1 => T.det) = {T.det} := Set.range_const
    rw [hr]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨b, T', hfr, hT', rfl⟩
      exact det_mem_span L hb₀ (hf q trivial hq) hfr hT hT'
    · rintro _ rfl
      exact ⟨c, T, hf q trivial hq, hT, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.DetLine
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.orthogonal_metric_hermitian_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ (s s' : CMType H ⊕ CMType H), s ≠ s' → ∀ U U' : Submodule Ω 𝔐.Li, U ≤ 𝔐.Vgen s → U' ≤ 𝔐.Vgen s' → OrthAt B (FlagFib.subFib 𝔐.M U z MB) (FlagFib.subFib 𝔐.M U' z MB) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth.orthAt_subFib | exact GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth.orthAt_subFib | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth.orthAt_subFib <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptWedge

section LinAlg

variable {Ω₀ Ω V₀ V : Type} [Field Ω₀] [Field Ω] [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V]

theorem exists_wedge_eq_smul {n : ℕ} {e b : Fin n → V} (h : ∀ k, e k ∈ Submodule.span Ω (Set.range b)) :
    ∃ d : Ω, exteriorPower.ιMulti Ω n e = d • exteriorPower.ιMulti Ω n b := by
  choose T hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  have he : e = fun k => ∑ l, (Matrix.of T) k l • b l := funext fun k => (hT k).symm
  exact ⟨(Matrix.of T).det, by rw [he]; exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω V n b _⟩

theorem isPullWedge_smul_ιMulti (i : Ω₀ →+* Ω) (j : V₀ →+ V) (hj : IsExtOver i j) {n : ℕ} {u : Fin n → V₀}
    (hu : LinearIndependent Ω₀ u) {γ : Ω₀} (hγ : γ ≠ 0) :
    CptIn.IsPullWedge i j (γ • exteriorPower.ιMulti Ω₀ n u)
      (i γ • exteriorPower.ιMulti Ω n fun k => j (u k)) := by
  intro b α hab
  have hw := WedgeFrame.ιMulti_ne_zero hu
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hab
    exact smul_ne_zero hγ hw hab
  have hbe : exteriorPower.ιMulti Ω₀ n b = (α⁻¹ * γ) • exteriorPower.ιMulti Ω₀ n u := by
    rw [mul_smul, hab, smul_smul, inv_mul_cancel₀ hα, one_smul]
  have hm := GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional Ω₀ V₀ n b u _ hu (mul_ne_zero (inv_ne_zero hα) hγ) hbe
  choose T hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω₀).1 (hm k)
  have hb : b = fun k => ∑ l, (Matrix.of T) k l • u l := funext fun k => (hT k).symm
  have h1 : exteriorPower.ιMulti Ω₀ n b = (Matrix.of T).det • exteriorPower.ιMulti Ω₀ n u := by
    rw [hb]; exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω₀ V₀ n u _
  have h2 : γ = α * (Matrix.of T).det := by
    rw [h1, smul_smul] at hab
    exact smul_left_injective Ω₀ hw hab
  have h3 : (fun k => j (b k)) = fun k => ∑ l, (i.mapMatrix (Matrix.of T)) k l • j (u l) := by
    funext k
    rw [hb]

    simp only [map_sum, hj.1]
    rfl
  rw [h3, GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω V n _ _, ← RingHom.map_det, smul_smul, ← map_mul, ← h2]

end LinAlg

theorem exists_eq_smul_ιMulti {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {r : ℕ} {u : Fin r → E} {x : Cpt ξ} (hu : L.IsFrameAt u x)
    {a : ⋀[Ω]^r E} {α : Ω} (hα : α ≠ 0) (hw : L.wedge r x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ γ : Ω, γ ≠ 0 ∧ a = γ • exteriorPower.ιMulti Ω r u := by
  obtain ⟨h1, h2⟩ := WedgeFrame.wedge_eq_span_ιMulti X Ω ξ E L r u x hu
  have h3 : exteriorPower.ιMulti Ω r u ∈ Submodule.span (regAt ξ x) {α • a} := by
    rw [← hw, h1]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h3
  have ht' : ((t : Ω) * α) • a = exteriorPower.ιMulti Ω r u := by
    rw [mul_smul]; exact ht
  have ht0 : (t : Ω) * α ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ht'
    exact h2 ht'.symm
  exact ⟨((t : Ω) * α)⁻¹, inv_ne_zero ht0, by rw [← ht', smul_smul, inv_mul_cancel₀ ht0, one_smul]⟩

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : Set (Xo.XF c)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

theorem tie_act {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) (a : 𝓞 E) (e : Z.V) : j (Z.ρ a e) = 𝔐.ρ a (j e) := by
  obtain ⟨-, -, -, h4⟩ := h
  refine 𝔐.M.inj (Over.OverMorphism.ext (𝔐.m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  rw [h4, Z.act a e, 𝔐.act a (j e), Over.comp_left, Over.comp_left, Category.assoc, 𝔐.m.act, ← Category.assoc]
  exact (congrArg (· ≫ Over.Hom.left (Y.t.act.act a)) (h4 e).symm).trans (Category.assoc _ _ _)

theorem tie_mem_eigSp {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) (σ : 𝓞 E →+* c.F) {e : Z.V} (he : e ∈ eigSp Z.ρ (Z.inc.comp σ)) :
    j e ∈ eigSp 𝔐.ρ (𝔐.cst.comp σ) := by
  have hi := h.2.1
  have hs := h.2.2.1.1
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at he ⊢
  intro a
  rw [← tie_act h, he a, hs, ← hi]
  rfl

theorem exists_side {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) {L : Lat (Z.ξ₀ ≫ Y.j) Z.V} {r : ℕ} {u : Fin r → Z.V} {x : Cpt (Z.ξ₀ ≫ Y.j)}
    (hu : L.IsFrameAt u x) {a : ⋀[Z.Ω]^r Z.V} {α : Z.Ω} (hα : α ≠ 0)
    (hw : L.wedge r x = Submodule.span (regAt (Z.ξ₀ ≫ Y.j) x) {α • a}) {B : Fin r → 𝔐.Li}
    (hB : ∀ k, j (u k) ∈ Submodule.span Ω (Set.range B)) :
    ∃ (a' : ⋀[Ω]^r 𝔐.Li) (d : Ω), d ≠ 0 ∧ a' ≠ 0 ∧ CptIn.IsPullWedge i j a a' ∧
      a' = d • exteriorPower.ιMulti Ω r B := by
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_smul_ιMulti hu hα hw
  have hj : IsExtOver i j := h.2.2.1
  have hind : LinearIndependent Ω fun k => j (u k) := hj.2 r u hu.1
  have hne := WedgeFrame.ιMulti_ne_zero hind
  obtain ⟨d, hd⟩ := exists_wedge_eq_smul hB
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hd
    exact hne hd
  have hiγ : i γ ≠ 0 := (map_ne_zero i).2 hγ
  exact ⟨_, i γ * d, mul_ne_zero hiγ hd0, smul_ne_zero hiγ hne, isPullWedge_smul_ιMulti i j hj hu.1 hγ,
    by rw [hd, smul_smul]⟩

end Comparison₂

theorem exists_pullWedge_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V), CptIn.IsTie Z 𝔐 i j → IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib → ∃ (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (d₁ d₂ : Ω), d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ a' ≠ 0 ∧ b' ≠ 0 ∧ CptIn.IsPullWedge i j a a' ∧ CptIn.IsPullWedge i j b b' ∧ a' = d₁ • (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) ∧ b' = d₂ • (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 Fl τ i j a b hT hL
  have hfr : ∀ x : c.F, ∃ a b : 𝓞 c.F, algebraMap (𝓞 c.F) c.F b ≠ 0 ∧
      x * algebraMap (𝓞 c.F) c.F b = algebraMap (𝓞 c.F) c.F a := by
    intro x
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 c.F)) x
    exact ⟨a, b, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2, hab⟩
  obtain ⟨h1, h2, -, x, hx⟩ := isVBOn_eig_genFib E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y U Z τ.1
    ⟨FaithfulSMul.algebraMap_injective _ _, inferInstance, hfr⟩ τ.2
  obtain ⟨-, -, hg⟩ := hL
  obtain ⟨α, β, hα, hβ, hwa, hwb, -⟩ := hg x hx
  obtain ⟨W₁, hW₁, u₁, hs₁, hf₁⟩ := h1 x hx
  obtain ⟨W₂, hW₂, u₂, hs₂, hf₂⟩ := h2 x hx
  have hu₁ := hf₁ x hx hW₁
  have hu₂ := hf₂ x hx hW₂
  have hB₁ : ∀ k, j (u₁ k) ∈ Submodule.span Ω (Set.range (Fl.b (.inl τ))) := fun k => by
    rw [HodgeCptTest.flag_span 𝔐 Fl]
    have hk : u₁ k ∈ eigSp Z.ρ (Z.inc.comp (tauIn c τ.1)) := hs₁ ▸ Submodule.subset_span ⟨k, rfl⟩
    have := tie_mem_eigSp hT _ hk
    rwa [← CptInputs.labelEmb_inl] at this
  have hB₂ : ∀ k, j (u₂ k) ∈ Submodule.span Ω (Set.range (Fl.b (.inr τ))) := fun k => by
    rw [HodgeCptTest.flag_span 𝔐 Fl]
    have hk : u₂ k ∈ eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ.1))) :=
      hs₂ ▸ Submodule.subset_span ⟨k, rfl⟩
    have := tie_mem_eigSp hT _ hk
    rwa [← CptInputs.labelEmb_inr] at this
  obtain ⟨a', d₁, hd₁, ha', hpa, hea⟩ := exists_side hT hu₁ hα hwa (B := Fl.b (.inl τ)) hB₁
  obtain ⟨b', d₂, hd₂, hb', hpb, heb⟩ := exists_side hT hu₂ hβ hwb (B := Fl.b (.inr τ)) hB₂
  exact ⟨a', b', d₁, d₂, hd₁, hd₂, ha', hb', hpa, hpb, hea, heb⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CptWedge
end
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.root_origin_complete_dvr_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (T : CDVR) (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), ∃ (EC : Type) (_ : AddCommGroup EC) (_ : Module T.Fr EC) (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.exists_lieModel_act_gen | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.exists_lieModel_act_gen | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.exists_lieModel_act_gen <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.triangular_span_coeff_ratio : ∀ (V F EC : Type) [CommRing V] [Field F] [Algebra V F] [AddCommGroup EC] [Module F EC] [Module V EC] [IsScalarTower V F EC] (r : ℕ) (u v w : Fin r → EC) (a b : Fin r → F) (d : V), LinearIndependent F u → FinRd.Roots.TriIn u a v → FinRd.Roots.TriIn u b w → (∀ i, b i ≠ 0) → (∀ x ∈ Submodule.span V (Set.range v), d • x ∈ Submodule.span V (Set.range w)) → ∀ i, ∃ c : V, algebraMap V F d * a i = algebraMap V F c * b i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.diag_compare_of_triIn | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.diag_compare_of_triIn | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.diag_compare_of_triIn <;> assumption)
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.cusp_correspondence_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ 𝔐.X), ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* L), 𝔐.LabVal z id σ ∧ (∀ σ', 𝔐.LabVal z id σ' → σ' = σ) ∧ Function.Bijective σ ∧ (∀ s, Function.Injective (σ s)) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E ∧ ∀ e : L →+* ℂ, IsCMFam (fun τ => e.comp (σ (.inl τ))) ∧ IsCMFam (fun τ => e.comp (σ (.inr τ))) ∧ ∀ τ, e.comp (σ (.inr τ)) = (starRingEnd ℂ).comp (e.comp (σ (.inl τ))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal | exact GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal <;> assumption)

end
end
