module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubRedMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle692
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsChernExistsUniqueAndIso
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle004

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocalTriv

theorem hartogs_chart : ∀ (Y : Scheme.{0}) (V : Y.Opens) (hV : IsAffineOpen V), IsLocallyNoetherian (Sp Γ(Y, V)) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ U : (Sp Γ(Y, V)).Opens, (∀ p : Sp Γ(Y, V), ringKrullDim (Y.presheaf.stalk (hV.fromSpec p)) ≤ 1 → p ∈ U) → Function.Bijective ((Sp Γ(Y, V)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom := by
  intro Y V hV hLN hY U hU
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp Γ(Y, V)) := fun p => by
    let e := (asIso (hV.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv
    obtain ⟨h1, h2⟩ := hY (hV.fromSpec p)
    haveI := h1
    haveI := h2
    haveI : IsDomain ((Sp Γ(Y, V)).presheaf.stalk p) := MulEquiv.isDomain _ e.symm.toMulEquiv
    exact ⟨inferInstance, IsIntegrallyClosed.of_equiv e⟩
  have hb := ((GlobalTheory.extension_over_codim_two (Sp Γ(Y, V)) hN).1 U fun p hp => hU p (by
    let e := (asIso (hV.fromSpec.stalkMap p)).commRingCatIsoToRingEquiv
    exact (ringKrullDim_eq_of_ringEquiv e).trans_le hp)).1 ⊤
  have key : ∀ (V' : (Sp Γ(Y, V)).Opens) (_ : V' = U) (h' : V' ≤ ⊤),
      Function.Bijective (resG (Sp Γ(Y, V)) h') →
        Function.Bijective ((Sp Γ(Y, V)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom := by
    rintro _ rfl _ h
    exact h
  exact key _ (top_inf_eq U) _ hb

theorem factor_locus : ∀ (X T : Scheme.{0}) (W : X.Opens) (c : Pic W.toScheme) (j : T ⟶ X) [IsOpenImmersion j] (V : (j ⁻¹ᵁ W).toScheme.Opens), IsLocus (GlobalTheory.CechPic.pull (j ∣_ W) c) V → ∀ N : X.Opens, (∀ w ∈ N ⊓ W, ∃ z ∈ V, j ((j ⁻¹ᵁ W).ι z) = w) → GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0 := by
  intro X T W c j _ V hV N hN
  have hz : ∀ z : (N ⊓ W).toScheme, ∃ z' ∈ V, (j ∣_ W) z' = X.homOfLE (inf_le_right : N ⊓ W ≤ W) z := by
    intro z
    obtain ⟨z', hz'V, hz'⟩ := hN ((N ⊓ W).ι z) z.2
    refine ⟨z', hz'V, W.ι.isOpenEmbedding.injective ?_⟩
    have e1 : W.ι ((j ∣_ W) z') = j ((j ⁻¹ᵁ W).ι z') :=
      congrArg (fun f => f.base z') (morphismRestrict_ι j W)
    have e2 : W.ι (X.homOfLE (inf_le_right : N ⊓ W ≤ W) z) = (N ⊓ W).ι z :=
      congrArg (fun f => f.base z) (X.homOfLE_ι (inf_le_right : N ⊓ W ≤ W))
    exact e1.trans (hz'.trans e2.symm)
  let k := IsOpenImmersion.lift (j ∣_ W) (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) (by
    rintro _ ⟨z, rfl⟩
    obtain ⟨z', -, h⟩ := hz z
    exact ⟨z', h⟩)
  have hk : k ≫ (j ∣_ W) = X.homOfLE (inf_le_right : N ⊓ W ≤ W) := IsOpenImmersion.lift_fac _ _ _
  rw [← hk, pull_comp]
  refine GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.2 _ _ k _ V hV fun z => ?_
  obtain ⟨z', hz'V, h⟩ := hz z
  have hkz : k z = z' := (j ∣_ W).isOpenEmbedding.injective (by
    have e : (j ∣_ W) (k z) = X.homOfLE (inf_le_right : N ⊓ W ≤ W) z := congrArg (fun f => f.base z) hk
    exact e.trans h.symm)
  rw [hkz]
  exact hz'V

theorem locally_trivial : ∀ (X Y : Scheme.{0}) [IsLocallyNoetherian X] (q : Y ⟶ X) [Smooth q] [Surjective q], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y → ∀ W : X.Opens, (∀ z : Y, ringKrullDim ((Y).presheaf.stalk z) ≤ 1 → z ∈ q ⁻¹ᵁ W) → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (q ∣_ W) c = 0 → ∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0 := by
  intro X Y _ q _ _ hY W hW c hc x
  obtain ⟨y, rfl⟩ := q.surjective x
  obtain ⟨N0, hN0, hx0, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show q y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨N1, hN1, hy1, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ q ⁻¹ᵁ N0 from hx0)
  have hA0 : IsAffineOpen N0 := hN0
  have hA1 : IsAffineOpen N1 := hN1
  have hB : IsNoetherianRing Γ(X, N0) := IsLocallyNoetherian.component_noetherian ⟨N0, hN0⟩
  let g : Γ(X, N0) →+* Γ(Y, N1) := (q.appLE N0 N1 hle).hom
  have hg : g.Flat := HasRingHomProperty.appLE @Flat q inferInstance ⟨N0, hN0⟩ ⟨N1, hN1⟩ hle
  have hsq : spMap g ≫ hA0.fromSpec = hA1.fromSpec ≫ q := IsAffineOpen.SpecMap_appLE_fromSpec q hA0 hA1 hle
  have hpt : ∀ p, hA0.fromSpec (spMap g p) = q (hA1.fromSpec p) := fun p => by
    have := congrArg (fun f => f.base p) hsq
    simpa using this
  have hLN : IsLocallyNoetherian (Sp Γ(Y, N1)) := LocallyOfFiniteType.isLocallyNoetherian (hA1.fromSpec ≫ q)
  let W0 : (Sp Γ(X, N0)).Opens := hA0.fromSpec ⁻¹ᵁ W
  have hbij := hartogs_chart Y N1 hA1 hLN hY (spMap g ⁻¹ᵁ W0) fun p hp => by
    show hA0.fromSpec (spMap g p) ∈ W
    rw [hpt]
    exact hW _ hp
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  let M := L.pull (hA0.fromSpec ∣_ W)
  have hM : M.IsLB := pull_isLB hL _
  have hk : spMap g ⁻¹ᵁ W0 ≤ hA1.fromSpec ⁻¹ᵁ (q ⁻¹ᵁ W) := fun p hp => by
    show q (hA1.fromSpec p) ∈ W
    rw [← hpt]
    exact hp
  have hcomp : (spMap g ∣_ W0) ≫ (hA0.fromSpec ∣_ W) = hA1.fromSpec.resLE (q ⁻¹ᵁ W) _ hk ≫ (q ∣_ W) := by
    rw [← cancel_mono W.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc]
    exact (morphismRestrict_ι_assoc (spMap g) W0 hA0.fromSpec).trans (congrArg _ hsq)
  have htriv : Triv (M.pull (spMap g ∣_ W0)) := by
    have h0 : cls _ (pull_isLB hM (spMap g ∣_ W0)) = 0 := by
      rw [cls_pull hM, cls_pull hL, ← pull_comp, hcomp, pull_comp, hc, map_zero]
    exact (cls_eq_zero_iff _).1 h0
  obtain ⟨y1, rfl⟩ : y ∈ Set.range hA1.fromSpec := hA1.range_fromSpec ▸ hy1
  obtain ⟨s, D, hyD, hD⟩ := GlobalTheory.T.exists_nowhereZero_section_near_of_flat_trivial Γ(X, N0) Γ(Y, N1) g hg W0 hbij M hM htriv y1
  let N : X.Opens := ⟨q '' (hA1.fromSpec '' D), q.isOpenMap _ (hA1.fromSpec.isOpenEmbedding.isOpenMap _ D.isOpen)⟩
  refine ⟨N, ⟨_, ⟨y1, hyD, rfl⟩, rfl⟩, ?_⟩
  refine factor_locus X _ W _ hA0.fromSpec (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s) ⟨M, hM, s, cls_pull hL _ hM, rfl⟩ N ?_
  rintro w ⟨⟨_, ⟨d, hd, rfl⟩, rfl⟩, hwW⟩
  have hdW : d ∈ spMap g ⁻¹ᵁ W0 := by
    show hA0.fromSpec (spMap g d) ∈ W
    rw [hpt]
    exact hwW
  refine ⟨(spMap g ∣_ W0) ⟨d, hdW⟩, hD ⟨d, hdW⟩ hd, ?_⟩
  have e : W0.ι ((spMap g ∣_ W0) ⟨d, hdW⟩) = spMap g d :=
    congrArg (fun f => f.base ⟨d, hdW⟩) (morphismRestrict_ι (spMap g) W0)
  exact (congrArg hA0.fromSpec.base e).trans (hpt d)

end GlobalTheory.LocalTriv
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.TaylorCore

open GlobalTheory.PeriodFamily GlobalTheory.CatCoh

theorem isNilpotent_of_isNilDP {D : Type} [CommRing D] {J : Ideal D} {κ : DividedPowers J} (h : IsNilDP κ) : IsNilpotent J := by
  obtain ⟨N, hN⟩ := h
  have key : ∀ (n : ℕ) (l : List D), (∀ x ∈ l, x ∈ J) → N ≤ l.length + n → ∀ y ∈ J ^ n, l.prod * y = 0 := by
    intro n
    induction n with
    | zero =>
      intro l hl hn y _
      have := hN (l.map fun x => (1, x)) (by simpa using hl) (by simpa [Function.comp_def] using hn)
      rw [List.map_map, List.map_congr_left (f := (fun p : ℕ × D ↦ κ.dpow p.1 p.2) ∘ fun x ↦ (1, x)) (g := id)
        fun x hx => κ.dpow_one (hl x hx), List.map_id] at this
      rw [this, zero_mul]
    | succ n ih =>
      intro l hl hn y hy
      rw [pow_succ'] at hy
      refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) fun a b ha hb => by rw [mul_add, ha, hb, add_zero]
      have := ih (a :: l) (by simpa [ha] using hl) (by simp; omega) b hb
      rw [List.prod_cons] at this
      linear_combination this
  exact ⟨N, eq_bot_iff.2 fun y hy => by simpa using key N [] (by simp) (by simp) y hy⟩

def tayHom {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) : Hol V →+* D where
  toFun f := PeriodFamily.taylor N t f.fn
  map_one' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun _ => 1) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using by rw [← Hol.ev_apply z hz, map_one]),
      (taylor_formal_properties N t).2.2.1, map_one]
  map_zero' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun _ => 0) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using by rw [← Hol.ev_apply z hz, map_zero]),
      (taylor_formal_properties N t).2.2.1, map_zero]
  map_mul' f f' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun z => f.fn z * f'.fn z) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using Hol.fn_mul _ _ hz),
      taylor_mul_of_prod_eq_zero N t ht _ _ (f.analytic _ h0) (f'.analytic _ h0)]
  map_add' f f' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun z => f.fn z + f'.fn z) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using Hol.fn_add _ _ hz),
      (taylor_formal_properties N t).1 _ _ (f.analytic _ h0) (f'.analytic _ h0)]

theorem ev_red {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {D : Type} [CommRing D] [Algebra ℂ D]
    (π : D →ₐ[ℂ] ℂ) (p : E) (hp : p ∈ W) (x : D ⊗[ℂ] Hol W) :
    Hol.ev p hp (Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol W)).comp π) (AlgHom.id ℂ (Hol W))
      (fun _ _ ↦ Commute.all _ _) x) =
    π (Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul d c =>
    simp only [Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.comp_apply, AlgHom.id_apply, Algebra.ofId_apply,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

theorem main : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B : Type} [CommRing B] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (e₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → (0 : I → ℂ) ∈ F.V → (∃ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, p.1 ∈ F₀.V → e₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap π → ∀ (n : IsMor (dp0 B) s κ s' j φ₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' (algebraMap ℂ D) φ) (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ (m : ℕ) (d : Fin m → D) (cs : Fin m → FirstDeRham s₀) (p : Fin m → Λ → ℂ) (ps : Fin m → Λ →+ Hol F₀.V), (∀ i l, ps i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod e₀ (cs i) (ps i)) → n.pull1 c = ∑ i, d i • k.pull1 (cs i) → ∀ l, ∑ i, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn := by
  intro I _ _ g Λ _ F F₀ B _ X X₀ s s₀ σ e e₀ hX hX₀ h0 hV₀ hτ φ₀ hφ₀ D _ _ π κ hκ hπ N t ht htN j hj s' hs' n φ hφ k c per hper
    m d cs p ps hps hcs hdec l
  let πa : D →ₐ[ℂ] ℂ := { π with commutes' := hπ }
  obtain ⟨D', _, _, io, π', nn, hio, hpio, hnil, hn0, hn2, hnt⟩ := SquareZeroSum.exists_sum_sq_zero N D πa t
    (isNilpotent_of_isNilDP hκ) ht htN
  obtain ⟨M, hM⟩ := id hnil
  have hJ : ∀ s : Fin (N + M + 1) → D', (∀ a, s a ∈ RingHom.ker π') → ∏ a, s a = 0 := fun s hs => by
    have h1 : ∏ a, s a ∈ ∏ _a : Fin (N + M + 1), RingHom.ker π' := Ideal.prod_mem_prod fun a _ => hs a
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Ideal.pow_le_pow_right (show M ≤ N + M + 1 by omega) h1
    rwa [hM, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
  have ht0 : ∀ i, π' (io (t i)) = 0 := fun i => (hpio _).trans (ht i)
  have ht' : ∀ s : Fin (N + M + 1) → I, ∏ a, io (t (s a)) = 0 := fun s => hJ _ fun a => ht0 _
  have hT : ∀ f, PeriodFamily.taylor (N + M) (fun i => io (t i)) f = io (PeriodFamily.taylor N t f) := fun f => by
    rw [← (taylor_formal_properties (N + M) t).2.2.2.2.1 D' io f, taylor_eq_of_le N t htN _ (Nat.le_add_right _ _)]
  have hred : ∀ f, π' (PeriodFamily.taylor (N + M) (fun i => io (t i)) f) = f 0 := fun f => by
    have h1 : PeriodFamily.taylor (N + M) (fun i => io (t i)) f - algebraMap ℂ D' (f 0) ∈ RingHom.ker π' :=
      (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ht0 i)) ((taylor_formal_properties (N + M) _).2.2.2.2.2 f)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, AlgHom.commutes] at h1
    exact h1
  obtain ⟨K₀, K, ν, hrich, hK₀, hK, hW, hν⟩ := ChartPair.exists_pair e₀ e (fun _ => 0) analyticOnNhd_const (fun _ _ => h0)
    LinearMap.id (AddMonoidHom.id Λ) fun l z _ => (hτ l z).symm
  obtain ⟨r₀, hr₀, -⟩ := exists_real_isFor e₀ hX₀ K₀ hK₀
  obtain ⟨r, hr, -⟩ := exists_real_isFor e hX K hK
  choose Ta hTa hTd using fun k => TaylorHom.exists_taylor_algHom (N + M) (fun i => io (t i)) ht' (K.W (ν k)) (K₀.W k) (hW k)
  let τV : Hol F.V →+* D' := tayHom (N + M) (fun i => io (t i)) ht' h0
  have hfam := TenFam.main π' r₀ rfl κ hs' (io : D →+* D') hpio hnil K r ν hν Ta τV
    (fun k f => tensor_hol_ext_of_values _ _ _ _ fun q hq => by
      rw [hTa k _ q hq, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      refine (taylor_formal_properties _ _).2.2.2.1 _ _ ?_
      have hc : Continuous fun z : I → ℂ => ((z, q.2) : Tot I g) := by fun_prop
      filter_upwards [hc.continuousAt.preimage_mem_nhds ((K.W (ν k)).isOpen.mem_nhds (hW k q hq))] with z hz
      exact K.fn_cst _ f hz)
    hTd (fun l k' k h₀ => close_paramTaylor_shift F F₀ h0 hτ _ (N + M) hJ _ N nn hn0 hn2 hnt K K₀ l _ _ k k' (hν l k' k h₀) h₀
      (hW k') (Ta k) (Ta k') (hTa k) (hTa k')) φ₀
    (fun k => point_hol_ext_of_isSeparated _ hX _ _ fun q hq => by
      rw [← Category.assoc, ← Category.assoc, hr₀ k q hq, hφ₀ q (K₀.base k q hq), ← hr (ν k) (0, q.2) (hW k q hq),
        ← Cris.spMap_comp]
      refine congrArg (fun ψ => spMap ψ ≫ r.x (ν k)) (RingHom.ext fun h => ?_)
      refine (ev_red π' q hq (Ta k h)).trans ?_
      rw [hTa k h q hq, hred]
      exact (Hol.ev_apply _ _ _).symm)
    j n (fun b => (congrArg io (hj b)).trans (hT _).symm) c per (τV.toAddMonoidHom.comp per) (fun _ => rfl) (hper K r hr)
  obtain ⟨z₀, hz₀⟩ := hV₀
  let q : Fin m → Λ →+ D' := fun i => ((algebraMap ℂ D').comp (Hol.ev z₀ hz₀).toRingHom).toAddMonoidHom.comp (ps i)
  have hq : ∀ i l, q i l = algebraMap ℂ D' (p i l) := fun i l =>
    congrArg (algebraMap ℂ D') ((congrArg (Hol.ev z₀ hz₀) (hps i l)).trans ((Hol.ev z₀ hz₀).commutes _))
  have hfib := fun i => TenFib.ten_fib π' r₀ rfl κ hs' (io : D →+* D') hpio hnil (algebraMap ℂ D) φ hφ k io.commutes (cs i) (p i)
    (ps i) (q i) (hps i) (hq i) (hcs i K₀ r₀ hr₀)

  rw [hdec, map_sum] at hfam
  simp only [LinearMap.map_smulₛₗ, hfib] at hfam
  have hz : K₀.tenZ (∑ i, io (d i) • q i - τV.toAddMonoidHom.comp per) =
      ∑ i, io (d i) • K₀.tenZ (q i) - K₀.tenZ (τV.toAddMonoidHom.comp per) := by
    let Z : (Λ →+ D') →ₗ[D'] Z1 (K₀.Ten D') :=
      { toFun := K₀.tenZ
        map_add' := fun a b => Subtype.ext (by funext T T' f; exact map_add (algebraMap D' (T'.ten D')) _ _)
        map_smul' := fun a b => Subtype.ext (by
          funext T T' f
          exact (map_mul (algebraMap D' (T'.ten D')) _ _).trans (Algebra.smul_def _ _).symm) }
    change Z _ = ∑ i, io (d i) • Z _ - Z _

    simp only [map_sub, map_sum, map_smul]
  have := Charts.tenZ_eq_zero K₀ hrich ⟨z₀, hz₀⟩ (∑ i, io (d i) • q i - τV.toAddMonoidHom.comp per) (by

    rw [hz, map_sub, ← hfam, map_sum]
    simp only [map_smul]
    exact sub_self _)
  have h1 := DFunLike.congr_fun (sub_eq_zero.1 this) l
  refine hio ?_

  rw [← hT, map_sum]
  refine Eq.trans ?_ h1
  change _ = (AddMonoidHom.eval l) (∑ i, io (d i) • q i)
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    change io (d i * algebraMap ℂ D (p i l)) = (io (d i) • q i) l
    rw [map_mul, io.commutes, AddMonoidHom.smul_apply, hq, smul_eq_mul]

end GlobalTheory.AnPer.TaylorCore
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.AbLaw GlobalTheory.Published GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.JetIsotropic

section Gen

variable {R : Type} [CommRing R] {I : Ideal R} {S : Scheme.{0}} {κ : DividedPowers I} {t : S ⟶ Sp R}
  {A : Over S} [GrpObj A]

theorem corrForm_antisymm (C : CupSquare κ t (A ⊗ A)) {P : LB (A ⊗ A).left} (hP : P.IsLB)
    (hs : LBIso P (P.pull (lift (snd A A) (fst A A)).left))
    {φ : Crys κ t A →ₗ[R] Crys κ t A →ₗ[R] R} (H : IsCorrForm κ t A A P φ) (x y : Crys κ t A) :
    φ x y = -φ y x := by
  obtain ⟨n, a, b, hc, hφ⟩ := id H
  let s : A ⊗ A ⟶ A ⊗ A := lift (snd A A) (fst A A)
  have ms : IsMor κ ((A ⊗ A).hom ≫ t) κ ((A ⊗ A).hom ≫ t) (RingHom.id R) s.left :=
    IsMor.of_over κ (φ := s.left) (by rw [← Category.assoc, Over.w])
  have hz := isChern_pull ms hc
  rw [crystallinePull2_sum_cup s ms] at hz
  simp only [pullOver_pullOver, s, lift_fst, lift_snd] at hz
  have e' : LBIso (P.pull s.left) P :=
    (cls_eq_iff (pull_isLB hP _) hP).1 ((cls_eq_iff hP (pull_isLB hP _)).2 hs).symm
  have hz' := (isChern_existsUnique_and_iso R _ κ _ _).2 _ _ (pull_isLB hP _) hP e' _ hz
  have H' : IsCorrForm κ t A A P (-φ.flip) := by
    refine ⟨n, fun k ↦ -b k, a, (congrArg (IsChern κ ((A ⊗ A).hom ≫ t) P) ?_).mp hz', fun u v ↦ ?_⟩
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [Submodule.coe_neg, map_neg, LinearMap.map_neg, LinearMap.neg_apply]
      exact (neg_eq_of_add_eq_zero_right (cup_add_cup _ _ _)).symm
    · simp only [LinearMap.neg_apply, LinearMap.flip_apply]
      rw [hφ, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [map_neg, neg_mul, mul_comm]
  have e := congrArg (fun f ↦ f x y) (H.unique C hP H')
  simpa using e

end Gen

section Jet

variable {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}

end Jet

section Diag

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

end Diag

section Props

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] [IsDomain R] [CharZero R]
  {I : Type} [Fintype I]

end Props

section BC

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'} {S S' : Scheme.{0}}
  {κ : DividedPowers I} {t : S ⟶ Sp R} {A : Over S} [GrpObj A] {κ' : DividedPowers I'} {t' : S' ⟶ Sp R'}
  {A' : Over S'} [GrpObj A'] {b : S' ⟶ S} {φ : A'.left ⟶ A.left}

end BC

end GlobalTheory.JetIsotropic
end
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.WigSep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def evAt (π : CuspSub E a) (g : GA E a) : π.V →ₗ[ℂ] ℂ :=
  (LinearMap.proj g).comp ((Sm E a).subtype.comp π.V.subtype)

def ell (π : CuspSub E a) (Ξ : AlgRep E a) (g : GA E a) (i : Fin Ξ.d) :
    Module.Dual ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp (TensorProduct.map (evAt π g) (LinearMap.proj i))

theorem ell_tmul (π : CuspSub E a) (Ξ : AlgRep E a) (g : GA E a) (i : Fin Ξ.d) (φ : π.V) (v : Fin Ξ.d → ℂ) :
    ell π Ξ g i (φ ⊗ₜ v) = φ.1.1 g * v i := by
  simp [ell, evAt]

theorem piScalarRight_eval (π : CuspSub E a) (Ξ : AlgRep E a) (m : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) (g : GA E a) (i : Fin Ξ.d) :
    ((TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d) m) i).1.1 g = ell π Ξ g i m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, Submodule.coe_add, hx, hy]
  | tmul φ v =>
    rw [ell_tmul]
    simp [TensorProduct.piScalarRight_apply, mul_comm]

theorem ell_sep (π : CuspSub E a) (Ξ : AlgRep E a) (m : π.V ⊗[ℂ] (Fin Ξ.d → ℂ))
    (h : ∀ g i, ell π Ξ g i m = 0) : m = 0 := by
  refine (LinearEquiv.map_eq_zero_iff (TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d))).1 ?_
  funext i
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  rw [piScalarRight_eval, h]
  rfl

theorem ell_deriv (π : CuspSub E a) (Ξ : AlgRep E a) (c : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E))
    (h0 : c 0 = 1) (hc : HasDerivAt (fun t => toL (c t).1) (toL Z) 0) (g : GA E a) (i : Fin Ξ.d)
    (m : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    HasDerivAt (fun t => ell π Ξ g i (tensorK π Ξ (c t) m)) (ell π Ξ g i (tensorLie π Ξ (toL Z) m)) 0 := by
  have h0' : Unitary.toUnits (c 0) = 1 := by rw [h0, map_one]
  have hc' : HasDerivAt (fun t => toL (Unitary.toUnits (c t)).val) (toL Z) 0 := hc
  induction m using TensorProduct.induction_on with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simp only [map_add (f := _)]; exact hx.add hy
  | tmul φ v =>
    have h1 := GlobalTheory.CuspRep.hasDerivAt_curve φ.1 g (fun t => Unitary.toUnits (c t)) (toL Z) h0' hc'
    have h2 : HasDerivAt (fun t => (Ξ.mat (Unitary.toUnits (c t)) *ᵥ v) i) ((Ξ.dmat (toL Z) *ᵥ v) i) 0 := by
      simp only [Matrix.mulVec, dotProduct]
      exact HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
        (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (c t)) (toL Z) h0' hc' i j).mul_const (v j)
    have e1 : ∀ t, ell π Ξ g i (tensorK π Ξ (c t) (φ ⊗ₜ v)) =
        φ.1.1 (g * infGL E a (Unitary.toUnits (c t))) * (Ξ.mat (Unitary.toUnits (c t)) *ᵥ v) i := fun t => by
      rw [tensorK, TensorProduct.map_tmul, ell_tmul]
      rfl
    have e2 : ell π Ξ g i (tensorLie π Ξ (toL Z) (φ ⊗ₜ v)) =
        lieD (toL Z) φ.1.1 g * (Ξ.mat (Unitary.toUnits (c 0)) *ᵥ v) i +
          φ.1.1 (g * infGL E a (Unitary.toUnits (c 0))) * (Ξ.dmat (toL Z) *ᵥ v) i := by
      rw [h0', map_one, map_one, mul_one, Matrix.one_mulVec, tensorLie_tmul, map_add (f := _), ell_tmul, ell_tmul]
      rfl
    rw [funext e1, e2]
    exact h1.mul h2

end GlobalTheory.WigSep

namespace GlobalTheory.WigSep

theorem exists_separating_functionals : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), ∃ S : Set (Module.Dual ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), (∀ m, (∀ l ∈ S, l m = 0) → m = 0) ∧ ∀ (c : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E)), c 0 = 1 → HasDerivAt (fun t => toL (c t).1) (toL Z) 0 → ∀ l ∈ S, ∀ m, HasDerivAt (fun t => l (tensorK π Ξ (c t) m)) (l (tensorLie π Ξ (toL Z) m)) 0 := by
  intro E _ _ _ a π Ξ
  refine ⟨Set.range fun p : GA E a × Fin Ξ.d => ell π Ξ p.1 p.2, fun m h => ell_sep π Ξ m fun g i => h _ ⟨(g, i), rfl⟩, ?_⟩
  rintro c Z h0 hc _ ⟨⟨g, i⟩, rfl⟩ m
  exact ell_deriv π Ξ c Z h0 hc g i m

end GlobalTheory.WigSep

end
end
