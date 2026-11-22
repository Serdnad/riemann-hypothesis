import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RegularAtCentre
import Formalism.LocalToGlobal.ProjectiveLattices.RegModelC
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.Reg.ChartInt

open IsLocalRing Formalism.L2.PjFree

alias vV_nonneg := Transfer.vV_nonneg
alias vV_unit := Transfer.vV_unit
alias mem_of_vV_nonneg := Transfer.mem_of_vV_nonneg
alias nval_nonneg := Transfer.nval_nonneg
alias nval_unit := Transfer.nval_unit
alias ne_zero_map := Transfer.ne_zero_map
alias chval_eq := Transfer.chval_eq
alias chval_div := Transfer.chval_div
alias chval_nonneg := Transfer.chval_nonneg

section Charts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem transfer {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (j : S.J) (g : FractionRing (S.A j)) (x : S.A j) (hx0 : x ≠ 0)
    (hpts : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra S.O V]
      [Module.Finite S.O V] (φ : S.A j →ₐ[S.O] V), φ x ≠ 0 →
        ∃ (e : ℕ) (r : EReal), 0 < e ∧ ChV φ.toRingHom e g r ∧ 0 ≤ r)
    (qq : Ideal (S.A j)) [qq.IsPrime]
    (hqq : qq ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤) :
    ∃ a s : S.A j, s ∉ qq ∧ g * algebraMap (S.A j) (FractionRing (S.A j)) s =
      algebraMap (S.A j) (FractionRing (S.A j)) a := by
  refine Formalism.L2.Pj.RegC.key_centre g x hx0 (fun V _ _ _ _ _ φ a b hab hb hφx => ?_) qq hqq
  obtain ⟨e, r, he, hr, hr0⟩ := hpts V φ hφx
  exact chval_div φ.toRingHom e he g r hr hr0 a b hab hb

theorem nonneg_at {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) (j : S.J) (x : S.A j) (hxE : x ∈ S.Eb j)
    (hx0 : x ≠ 0) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra S.O V]
    (φ : S.A j →ₐ[S.O] V) (e : ℕ) (rr : EReal) (hch : ChV φ.toRingHom e (S.ch j F) rr)
    (hqq : (maximalIdeal V).comap φ.toRingHom ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤) :
    0 ≤ rr := by
  obtain ⟨a', s', hs', hfs'⟩ := transfer S j (S.ch j F) x hx0 (fun V _ _ _ _ _ φ hφx => by
    obtain ⟨ioV, e', hov, -, v, hv, hChV⟩ := S.pts j V φ ⟨x, hxE, hφx⟩
    exact ⟨e', v F, hov.1, hChV a n F hF, h0 v hv⟩) ((maximalIdeal V).comap φ.toRingHom) hqq
  exact chval_nonneg φ.toRingHom e (S.ch j F) rr hch a' s' hfs' hs'

theorem nonneg_at_all_points {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, 0 ≤ v F := by
  intro v hv
  obtain ⟨j, V, _, _, _, _, φ, ioV, e, hov, ⟨x, hxE, hφx⟩, -, hmap, hChV⟩ := S.cover v hv
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  refine nonneg_at S hF h0 j x hxE hx0 V φ e (v F) (hChV a n F hF) ?_
  rw [sup_eq_left.2 hmap]
  exact (Ideal.IsPrime.ne_top inferInstance)

theorem nonneg_at_trivial {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ q ∈ trivSet Xo c, 0 ≤ q F := by
  intro q hq
  obtain ⟨j, V, _, _, _, _, φ, hcen, -, ⟨x, hxE, hφx⟩, hChV⟩ := hQ q hq
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  refine nonneg_at S hF h0 j x hxE hx0 V φ 1 (q F) (hChV a n F hF) ?_
  have hm : maximalIdeal S.O = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [hm, Ideal.map_span, Set.image_singleton, sup_comm]
  exact hcen ϖ hϖ

theorem qpt_mem_trivSet (q : QPt Xo c) : (fun f => ordQ Xo c q f) ∈ trivSet Xo c := by
  refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
  obtain ⟨u, hu⟩ := q.triv a ha
  rw [← hu]
  exact vV_unit (u : q.T.V) (fun h => h u.isUnit)

end Charts

end GlobalTheory.Reg.ChartInt

namespace GlobalTheory

theorem integrality_at_trivial_valuations_of_charts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) → ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR1Quotient Xo c C ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n, ∀ la, (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, 0 ≤ v f) → ∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.trivialClassCondition Xo c) la, 0 ≤ v f := by
  intro E _ _ _ H Dw l Xo c hS C hC
  refine ⟨?_, ?_⟩
  · rintro a n f hf ⟨la, h0⟩ q
    obtain ⟨S, hQ⟩ := (hS la).1
    exact GlobalTheory.Reg.ChartInt.nonneg_at_trivial S hQ (hC a n hf) h0 _ (GlobalTheory.Reg.ChartInt.qpt_mem_trivSet q)
  · intro a n f hf la h0
    obtain ⟨S, -⟩ := (hS la).1
    exact GlobalTheory.Reg.ChartInt.nonneg_at_all_points S (hC a n hf) h0

end GlobalTheory
