module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle634
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle647
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2560
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2600
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Local

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens}

theorem exists_unit (hG : GenSt) (hL : Laws U x) (s : ArchSec U x Z (flatWt Dw τ)) (hc : IsCover Y r hle Z la p Xw)
    {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] {ξ : Sp R ⟶ Y.X} [IsOpenImmersion ξ] {β : c'.V W →+* R}
    (hβ : ξ ≫ Y.s = spMap β) (hξ : ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Xw) {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)} (he : IsTanBasis Y.t ξ e) {U₁ U₂ : Fin g → Fin g → R}
    (h₁ : EigFam Y.t ξ (β.comp (embV c' W τ.1)) e U₁) (h₂ : EigFam Y.t ξ (β.comp (embV c' W (conjEmb τ.1))) e U₂)
    (K₁ : Fin (Dw.mult τ.1) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g) (a₁ : Fin (Dw.mult τ.1) → Fin g → R)
    (a₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → R) (ε : ℤˣ) :
    ∃ u : (Localization.Away ((p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂))))ˣ,
      ∀ (k : Type) [Field k] [Algebra c.F k] (ψ : Localization.Away ((p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂))) →+* k) (yy : Sp k ⟶ Xo'.XF c'),
        yy ≫ Y.j = spMap (ψ.comp (algebraMap R _)) ≫ ξ → ∃ fv : k,
          GVal Y r ν τ.1 s.sig yy (bcV Y.t (ψ.comp (algebraMap R _)) e) (fun i b => ψ (algebraMap R _ (U₁ (K₁ i) b)))
            (fun i b => ψ (algebraMap R _ (U₂ (K₂ i) b))) fv ∧
          ψ u = fv * ((ε : ℤ) : k) * ψ (algebraMap R _ (pairDet a₁ (U₁ ∘ K₁))) / ψ (algebraMap R _ (pairDet a₂ (U₂ ∘ K₂))) := by
  set q : R := (p : R) * (pairDet a₁ (U₁ ∘ K₁) * pairDet a₂ (U₂ ∘ K₂)) with hq
  have hu : IsUnit (algebraMap R (Localization.Away q) q) := IsLocalization.Away.algebraMap_isUnit q
  by_cases h0 : q = 0
  · refine ⟨1, fun k _ _ ψ _ _ => ?_⟩
    have := hu.map ψ
    rw [show algebraMap R (Localization.Away q) q = 0 from (congrArg _ h0).trans (map_zero _), map_zero] at this
    exact absurd this not_isUnit_zero
  have hle' : Submonoid.powers q ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors h0
  haveI : IsDomain (Localization.Away q) := IsLocalization.isDomain_localization hle'
  haveI : IsIntegrallyClosed (Localization.Away q) := isIntegrallyClosed_of_isLocalization _ _ hle'
  have hinj : Function.Injective (algebraMap R (Localization.Away q)) := IsLocalization.injective _ hle'
  let ρ := algebraMap R (Localization.Away q)
  have hu' : IsUnit ((p : Localization.Away q) * (ρ (pairDet a₁ (U₁ ∘ K₁)) * ρ (pairDet a₂ (U₂ ∘ K₂)))) := by
    rw [← map_natCast ρ, ← map_mul, ← map_mul]; exact hu
  have u₁ := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right hu')
  have u₂ := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_right hu')
  have mp : ∀ {m : ℕ} (a V : Fin m → Fin g → R), ρ (pairDet a V) = pairDet (fun i b => ρ (a i b)) fun i b => ρ (V i b) :=
    fun a V => by
      rw [pairDet, pairDet, RingHom.map_det]
      congr 1
      ext i j

      simp [map_sum]
  haveI : IsOpenImmersion (spMap ρ) := IsOpenImmersion.of_isLocalization q
  obtain ⟨f, hf⟩ := hG E H Dw l l' Xo Xo' c c' W Y r ν hle r₀ U x hL Z τ s la p Xw Fact.out hc (Localization.Away q)
    (spMap ρ ≫ ξ) (ρ.comp β) inferInstance (by rw [Category.assoc, hβ, spMap_spMap]) (isUnit_of_mul_isUnit_left hu')
    (by rw [bot_map hinj]; exact hξ) g (bcV Y.t ρ e) (fun i b => ρ (U₁ (K₁ i) b)) (fun i b => ρ (a₁ i b))
    (fun i b => ρ (U₂ (K₂ i) b)) (fun i b => ρ (a₂ i b)) (isTanBasis_bc he ρ)
    (fun S _ φ => by
      rw [sp_sp, bcV_bcV]
      exact ⟨fun i => (h₁ S (φ.comp ρ)).1 (K₁ i), fun i => (h₂ S (φ.comp ρ)).1 (K₂ i)⟩)
    (mp a₁ _ ▸ u₁) (mp a₂ _ ▸ u₂)
  refine ⟨f * Units.map (Int.castRingHom _).toMonoidHom ε * u₁.unit * u₂.unit⁻¹, fun k _ _ ψ yy hy => ⟨ψ f, ?_, ?_⟩⟩
  · have := hf k ψ yy (by rw [sp_sp]; exact hy)
    rwa [bcV_bcV] at this
  · rw [eq_div_iff (u₂.map ψ).ne_zero, ← map_mul]
    change ψ (_ * (u₂.unit : Localization.Away q)) = _
    rw [← Units.val_mul, inv_mul_cancel_right]
    simp [ρ]

end Local

section Charts

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens} [StarRing (𝓞 E)]


end Charts

section Top

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  {Y : Model Xo' c' (c'.V W).subtype} {r : Xo'.XF c' ⟶ Xo.XF c} {ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)}
  {hle : c.F ≤ c'.F} {r₀ : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀} {x : ℝ} {Z : Comp Xo c} {τ : Psi H}
  {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} [Fact p.Prime] {Xw : Y.X.Opens}

end Top



end GlobalTheory.FlatModel

end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.TrueGeo.SmallSec

namespace GlobalTheory.ProjSpace

section
variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem regAt_fnMap_of (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) {y : Y} {t : X.functionField}
    (h : RegAt (j y) t) : RegAt y (fnMap j hη t) := by
  obtain ⟨U, hx, s, rfl⟩ := h.exists_fnOf
  have hy : y ∈ j ⁻¹ᵁ U := hx
  rw [fnMap_fnOf j hη _ (gen_mem hy)]
  exact regAt_fnOf hy _ _

theorem fnOf_appLE (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X) {U : X.Opens} {V : Y.Opens}
    (e : V ≤ j ⁻¹ᵁ U) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ V) (a : Γ(X, U)) :
    fnOf V h' ((j.appLE U V e).hom a) = fnMap j hη (fnOf U h a) := by
  rw [fnMap_fnOf j hη h (e h')]
  exact fnOf_resG e h' (j.app U a)

theorem comp_genericPoint_specializes {Z : Scheme.{0}} [IsIntegral Z] (a : Z ⟶ Y) (b : Y ⟶ X)
    (ha : a (genericPoint Z) ⤳ genericPoint Y) (hb : b (genericPoint Y) ⤳ genericPoint X) :
    (a ≫ b) (genericPoint Z) ⤳ genericPoint X := by
  rw [Scheme.Hom.comp_apply]
  exact (ha.map b.continuous).trans hb

theorem fnMap_comp {Z : Scheme.{0}} [IsIntegral Z] (a : Z ⟶ Y) (b : Y ⟶ X)
    (ha : a (genericPoint Z) ⤳ genericPoint Y) (hb : b (genericPoint Y) ⤳ genericPoint X)
    (hab : (a ≫ b) (genericPoint Z) ⤳ genericPoint X) (t : X.functionField) :
    fnMap (a ≫ b) hab t = fnMap a ha (fnMap b hb t) := by
  obtain ⟨U, hx, s, rfl⟩ := (regAt_genericPoint t).exists_fnOf
  have h1 : genericPoint Y ∈ b ⁻¹ᵁ U := hb.mem_open U.isOpen hx
  have h2 : genericPoint Z ∈ a ⁻¹ᵁ (b ⁻¹ᵁ U) := ha.mem_open (b ⁻¹ᵁ U).isOpen h1
  rw [fnMap_fnOf b hb _ h1, fnMap_fnOf a ha _ h2, fnMap_fnOf (a ≫ b) hab _ h2, Scheme.Hom.comp_app]
  rfl

theorem fnMap_congr {a b : Y ⟶ X} (e : a = b) (ha : a (genericPoint Y) ⤳ genericPoint X)
    (hb : b (genericPoint Y) ⤳ genericPoint X) (t : X.functionField) : fnMap a ha t = fnMap b hb t := by
  subst e; rfl
end

theorem exists_ratCoords : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (U : Y.Opens) (hU : (U : Set Y).Nonempty)
    (φ : U.toScheme ⟶ PSpace F N),
    haveI : Nonempty U := hU.to_subtype
    haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      ∀ (u : U.toScheme) (k : Fin (N + 1)) (hk : u ∈ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k), w k ≠ 0 ∧ ∀ j,
        GlobalTheory.TrueGeo.SmallSec.fnMap U.ι (specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)) (w j / w k) =
          GlobalTheory.Cartier.fnOf (φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k) (GlobalTheory.Cartier.gen_mem hk)
            (GlobalTheory.ProjSpace.pullRatio φ _ k le_rfl j) := by
  intro F _ Y _ N U hU φ
  haveI : Nonempty U := hU.to_subtype
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hηU : U.ι (genericPoint U.toScheme) ⤳ genericPoint Y :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)
  obtain ⟨i₀, hi₀⟩ := exists_mem_chart F N (φ (genericPoint U.toScheme))
  have hg₀ : genericPoint U.toScheme ∈ φ ⁻¹ᵁ chart F N i₀ := hi₀
  choose w hw using fun j => fnMap_surjective U.ι hηU (fnOf _ hg₀ (pullRatio φ _ i₀ le_rfl j))
  refine ⟨w, i₀, ?_, fun u k hk => ?_⟩
  · apply (fnMap U.ι hηU).injective
    rw [hw, pullRatio_self, map_one, map_one]
  have hV : genericPoint U.toScheme ∈ φ ⁻¹ᵁ chart F N i₀ ⊓ φ ⁻¹ᵁ chart F N k := ⟨hg₀, gen_mem hk⟩
  have hmul : ∀ j, fnMap U.ι hηU (w j) =
      fnMap U.ι hηU (w k) * fnOf _ (gen_mem hk) (pullRatio φ _ k le_rfl j) := by
    intro j
    rw [hw, hw, ← fnOf_resG inf_le_left hV, ← fnOf_resG inf_le_left hV, ← fnOf_resG inf_le_right hV, ← map_mul,
      resG_pullRatio, resG_pullRatio, resG_pullRatio, pullRatio_mul_pullRatio]
  have hk0 : fnMap U.ι hηU (w k) ≠ 0 := by
    rw [hw, ← fnOf_resG inf_le_left hV, resG_pullRatio]
    refine ((unitAt_fnOf_iff hV hV _).2 ?_).ne_zero
    rw [basicOpen_pullRatio]
    exact ⟨hV, hV.2⟩
  refine ⟨fun h => hk0 (by rw [h, map_zero]), fun j => ?_⟩
  rw [map_div₀, hmul j, mul_div_cancel_left₀ _ hk0]

theorem exists_hom_of_ratCoords : ∀ (F : Type) [Field F] (N : ℕ) (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp F)
    (w : Fin (N + 1) → Y.functionField),
    (∀ y : Y, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ g : Y ⟶ PSpace F N, g ≫ PSpace.str F N = q ∧ ∀ (y : Y) (k : Fin (N + 1)), w k ≠ 0 →
      (∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
      ∃ (W : Y.Opens) (hy : y ∈ W) (hW : W ≤ g ⁻¹ᵁ GlobalTheory.ProjSpace.chart F N k),
        ∀ j, GlobalTheory.Cartier.fnOf W (GlobalTheory.Cartier.gen_mem hy) (GlobalTheory.ProjSpace.pullRatio g W k hW j) = w j / w k := by
  intro F _ N Y _ q w hw
  classical
  have hopen : ∀ k, IsOpen {y : Y | w k ≠ 0 ∧ ∀ j, RegAt y (w j / w k)} := fun k => by
    refine isOpen_iff_forall_mem_open.2 fun y ⟨h0, hy⟩ => ?_
    obtain ⟨W, hyW, hW⟩ := GlobalTheory.InvertIdeal.exists_common_open hy
    refine ⟨W, fun y' hy' => ⟨h0, fun j => ?_⟩, W.isOpen, hyW⟩
    obtain ⟨a, ha⟩ := hW j
    exact ha ▸ regAt_fnOf hy' _ a
  let U' : Fin (N + 1) → Y.Opens := fun k => ⟨_, hopen k⟩
  have hr : ∀ k j, ∃ a : Γ(Y, U' k), ∀ h, fnOf (U' k) h a = w j / w k := fun k j => by
    by_cases h : genericPoint Y ∈ U' k
    · obtain ⟨a, ha⟩ := exists_fnOf_eq h fun y hy => hy.2 j
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose r hr using hr
  have H : IsCoordFamily U' r :=
    { cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hw y)
      self := fun k => fn_ext fun h => by rw [hr, map_one, div_self h.1]
      mul := fun i j k => fn_ext fun h => by
        rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, hr, hr, hr]
        have hi : w i ≠ 0 := h.1.1
        have hj : w j ≠ 0 := h.2.1
        field_simp
      basicOpen_le := fun i j y hy => by
        have hyi : y ∈ U' i := Y.basicOpen_le _ hy
        have hu := (unitAt_fnOf_iff hyi (gen_mem hyi) (r i j)).2 hy
        rw [hr] at hu
        have hi0 : w i ≠ 0 := hyi.1
        have hj0 : w j ≠ 0 := fun h0 => hu.ne_zero (by rw [h0, zero_div])
        refine ⟨hj0, fun l => ?_⟩
        have := (hyi.2 l).mul hu.inv.regAt
        rwa [show w l / w i * (w j / w i)⁻¹ = w l / w j by field_simp] at this }
  refine ⟨H.toHom q, H.toHom_str q, fun y k hk0 hreg => ⟨U' k, ⟨hk0, hreg⟩, H.le_toHom_preimage q k, fun j => ?_⟩⟩
  rw [H.pullRatio_toHom q k j]
  exact hr k j _

theorem exists_ratCoords_extend : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (N : ℕ) (U : Y.Opens)
    (φ : U.toScheme ⟶ PSpace F N), φ ≫ PSpace.str F N = U.ι ≫ p → (U : Set Y).Nonempty →
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        (∀ y' : Y', ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
          (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k))) →
        ∃ g : Y' ⟶ PSpace F N, g ≫ PSpace.str F N = s ≫ p ∧ (s ⁻¹ᵁ U).ι ≫ g = (s ∣_ U) ≫ φ := by
  intro F _ Y _ p N U φ hφ hU
  haveI : Nonempty U := hU.to_subtype
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hηU : U.ι (genericPoint U.toScheme) ⤳ genericPoint Y :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion U.ι)
  obtain ⟨w, i₀, hw₀, hw⟩ := exists_ratCoords F Y N U hU φ
  have loc : ∀ (u : U.toScheme) k, u ∈ φ ⁻¹ᵁ chart F N k → w k ≠ 0 ∧ ∀ j, RegAt (U.ι u) (w j / w k) := by
    intro u k hk
    refine ⟨(hw u k hk).1, fun j => ?_⟩
    rw [← regAt_fnMap_iff U.ι hηU, (hw u k hk).2 j]
    exact regAt_fnOf hk _ _
  refine ⟨w, i₀, hw₀, fun y hy => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := exists_mem_chart F N (φ ⟨y, hy⟩)
    exact ⟨k, loc ⟨y, hy⟩ k hk⟩
  intro Y' _ s hη hY'
  obtain ⟨g, hg, hgW⟩ := exists_hom_of_ratCoords F N Y' (s ≫ p) (fun j => fnMap s (specializes_of_eq hη) (w j)) hY'
  refine ⟨g, hg, hom_ext ?_ fun z => ?_⟩
  · rw [Category.assoc, hg, Category.assoc, hφ, ← Category.assoc (s ∣_ U), morphismRestrict_ι, Category.assoc]
  haveI : Nonempty (s ⁻¹ᵁ U).toScheme := ⟨z⟩
  haveI : IsIntegral (s ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (s ⁻¹ᵁ U).ι
  have hu : U.ι ((s ∣_ U) z) = s ((s ⁻¹ᵁ U).ι z) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hηι : (s ⁻¹ᵁ U).ι (genericPoint (s ⁻¹ᵁ U).toScheme) ⤳ genericPoint Y' :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion _)
  have hηr : (s ∣_ U) (genericPoint (s ⁻¹ᵁ U).toScheme) ⤳ genericPoint U.toScheme := by
    refine specializes_of_eq (U.ι.isOpenEmbedding.injective ?_)
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply,
      genericPoint_eq_of_isOpenImmersion, hη, genericPoint_eq_of_isOpenImmersion]
  obtain ⟨k, hk⟩ := exists_mem_chart F N (φ ((s ∣_ U) z))
  obtain ⟨hk0, hreg⟩ := loc _ k hk
  have hreg' : ∀ j, RegAt ((s ⁻¹ᵁ U).ι z)
      (fnMap s (specializes_of_eq hη) (w j) / fnMap s (specializes_of_eq hη) (w k)) := fun j => by
    rw [← map_div₀]
    exact regAt_fnMap_of s _ (hu ▸ hreg j)
  obtain ⟨W, hzW, hW, hWj⟩ := hgW _ k ((map_ne_zero _).2 hk0) hreg'
  have hz : z ∈ (s ⁻¹ᵁ U).ι ⁻¹ᵁ W ⊓ (s ∣_ U) ⁻¹ᵁ (φ ⁻¹ᵁ chart F N k) := ⟨hzW, hk⟩
  refine ⟨_, hz, k, inf_le_left.trans ((s ⁻¹ᵁ U).ι.preimage_mono hW), inf_le_right, fun j => ?_⟩
  refine fnOf_injective _ (gen_mem hz) ?_
  rw [← appLE_pullRatio (φ := g) (hi := hW) (s ⁻¹ᵁ U).ι inf_le_left,
    ← appLE_pullRatio (φ := φ) (hi := le_rfl) (s ∣_ U) inf_le_right,
    fnOf_appLE _ hηι _ (gen_mem hzW), fnOf_appLE _ hηr _ (gen_mem hk), hWj, ← (hw _ k hk).2 j, ← map_div₀,
    ← fnMap_comp _ _ hηι (specializes_of_eq hη) (comp_genericPoint_specializes _ _ hηι (specializes_of_eq hη)),
    ← fnMap_comp _ _ hηr hηU (comp_genericPoint_specializes _ _ hηr hηU)]
  exact fnMap_congr (morphismRestrict_ι s U).symm _ _ _

end GlobalTheory.ProjSpace
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem toH1O_surjective_of_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) := by
  intro hH R _ A _ g hab hdim
  rw [Category.comp_id]
  have hsm : Smooth A.hom := hab.smooth
  have hsep : IsSeparated A.hom := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact A.hom := by haveI := hab.proper; infer_instance
  have hcmp := GlobalTheory.Published.CrystallineSmoothLift.bijective_cechDeRhamComparison_degreeOne
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations A.hom hsm hsep hqc
  have hsurj : Function.Surjective (GlobalTheory.CechDR.toHO1 A.hom) := (hH R A g hab hdim).2.2.2.2.1.2.2
  intro u
  obtain ⟨h, hh⟩ := hsurj (GlobalTheory.CechDR.cmpO A.hom u)
  obtain ⟨c, rfl⟩ := hcmp.2 h
  refine ⟨c, GlobalTheory.CechDR.cmpO_injective R A.left A.hom ?_⟩
  rw [← GlobalTheory.CechDR.structureSheaf_comparison_comm, hh]

end GlobalTheory.PtExt
end
end

section

set_option autoImplicit false

namespace GlobalTheory

theorem abelianDeRham_free_baseChange_rigid : GlobalTheory.Published.AbelianHodgeDeRham →
    GlobalTheory.Published.AbelianDeRham.Free ∧ GlobalTheory.Published.AbelianDeRham.BaseChange ∧
      GlobalTheory.Published.AbelianDeRham.Rigid := by
  intro hH
  have h : GlobalTheory.Published.AbelianDeRhamStructure ∧
      GlobalTheory.Published.CrystallineDeRham :=
    GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses
      GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH
  obtain ⟨⟨hfree, -, hbc⟩, hcrys⟩ := h
  have hF : GlobalTheory.Published.AbelianDeRham.Free := GlobalTheory.AbelianPrim.abelianDeRham_free hfree
  exact ⟨hF, hbc, GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hcrys⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KSRechart

theorem resG_appLE {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U : Y.Opens) {V V' : Z.Opens} (h : V ≤ m ⁻¹ᵁ U) (e : V' ≤ V)
    (r : Γ(Y, U)) : resG Z e ((m.appLE U V h).hom r) = (m.appLE U V' (e.trans h)).hom r := by
  show ((m.appLE U V h) ≫ Z.presheaf.map (homOfLE e).op).hom r = _
  rw [Scheme.Hom.appLE_map]

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart


private theorem valR_comp_eq_valR_app' {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (m : Z ⟶ X)
    (U : X.Opens) (O : Z.Opens) (h : O ≤ m ⁻¹ᵁ U) (hO : ⊤ ≤ x ⁻¹ᵁ O) (r : Γ(X, U)) :
    valR x O ((m.appLE U O h).hom r) = valR (x ≫ m) U r := by
  have hU : ⊤ ≤ (x ≫ m) ⁻¹ᵁ U := fun p hp => h (hO hp)
  unfold valR
  rw [dite_eq_left hO, dite_eq_left hU]
  congr 1
  show ((m.appLE U O h) ≫ x.appLE O ⊤ hO).hom r = _
  rw [Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart

theorem valR_appLE {X Z : Scheme.{0}} (m : Z ⟶ X) (U : X.affineOpens) {S : Type} [CommRing S] (φ : Γ(X, U.1) →+* S)
    (g₀ : Sp S ⟶ Z) (hg : g₀ ≫ m = spMap φ ≫ chart U) {O : Z.Opens} (h : O ≤ m ⁻¹ᵁ U.1) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (r : Γ(X, U.1)) : valR g₀ O ((m.appLE U.1 O h).hom r) = φ r := by
  rw [valR_comp_eq_valR_app' g₀ m U.1 O h hO r, hg]
  exact GlobalTheory.FlagEmb.QuotLine.valR_chart U.2 φ r

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart

end GlobalTheory.KSRechart
end

section

namespace GlobalTheory

theorem abelianDeRham_of_hodge_cube_dual_poincare :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianDeRham :=
  by
    intro hH hC hD hP
    obtain ⟨⟨hfree, hhodge, hbc⟩, hcrys⟩ :=
      GlobalTheory.T.crystallineDeRham_abelianStructure_of_statements
        GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH
    have hF : GlobalTheory.Published.AbelianDeRham.Free :=
      GlobalTheory.AbelianPrim.abelianDeRham_free hfree
    exact ⟨hF, hhodge, hbc,
      GlobalTheory.Published.AbelianDeRham.rigid_of_free_of_crystallineDeRham hF hcrys,
      GlobalTheory.T.abelianDeRham_poincareDuality_of_cube_dual hC hD hP hF⟩

end GlobalTheory
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem abelianSchemeLifts_of_abelianHodgeDeRham : AbelianHodgeDeRham → AbelianSchemeLifts :=
  abelianSchemeLifts_of_hodgeDeRham
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations

end GlobalTheory.LiftSys
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.abelianVariety_potential_semiAbelian_splitTorus : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G ∧ Nonempty (TorusExtension (GlobalTheory.SS.spFibre G))) := by
  first | exact @GlobalTheory.SS.potModel_semiAbelian_torusExtension | exact GlobalTheory.SS.potModel_semiAbelian_torusExtension | (intros; apply GlobalTheory.SS.potModel_semiAbelian_torusExtension <;> assumption)
end
