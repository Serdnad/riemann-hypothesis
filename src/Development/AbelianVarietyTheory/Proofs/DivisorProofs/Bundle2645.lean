module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle974
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle063
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle160
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle147
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle534
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdUniq

theorem exists_spMap' {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ c : A →+* B, spMap c = f :=
  ⟨(Spec.preimage f).hom, by simp [spMap]⟩

theorem pCrd_iff {o R : Type} [CommRing o] [CommRing R] {n : ℕ} (x : Sp R ⟶ PSpace o n) (c : o →+* R)
    (hx : x ≫ PSpace.str o n = spMap c) (v : Fin (n + 1) → R) :
    PCrd x v ↔ ∃ hv : Ideal.span (Set.range v) = ⊤, x = ProjSpace.pt c v hv := by
  have h := ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) c x (by rw [Category.comp_id]; exact hx) v
  have h2 := RepBC.secCoord_pull (ProjSpace.O1 o n) (ProjSpace.coord o n) (𝟙 _) x v
  rw [Category.comp_id] at h2
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Category.comp_id] at h
  exact h2.symm.trans h

theorem eq_of_pCrd {o R : Type} [CommRing o] [CommRing R] {n : ℕ} {x x' : Sp R ⟶ PSpace o n} {v : Fin (n + 1) → R}
    (hs : x ≫ PSpace.str o n = x' ≫ PSpace.str o n) (h : PCrd x v) (h' : PCrd x' v) : x = x' := by
  obtain ⟨c, hc⟩ := exists_spMap' (x ≫ PSpace.str o n)
  obtain ⟨hv, e⟩ := (pCrd_iff x c hc.symm v).1 h
  obtain ⟨hv', e'⟩ := (pCrd_iff x' c (hs ▸ hc.symm) v).1 h'
  rw [e, e']

theorem exists_ne_zero_of_pCrd {o K : Type} [CommRing o] [Field K] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v : Fin (n + 1) → K} (h : PCrd x v) : ∃ k, v k ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_spMap' (x ≫ PSpace.str o n)
  obtain ⟨hv, -⟩ := (pCrd_iff x c hc.symm v).1 h
  by_contra hn
  push_neg at hn
  have : Set.range v ⊆ {0} := by rintro _ ⟨k, rfl⟩; exact hn k
  have h0 : Ideal.span (Set.range v) = ⊥ := by
    rw [Ideal.span_eq_bot]; intro y hy; exact this hy
  rw [h0] at hv
  exact bot_ne_top hv

theorem scalar_of_pCrd {o K : Type} [CommRing o] [Field K] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v w : Fin (n + 1) → K} (hv : PCrd x v) (hw : PCrd x w) : ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j := by
  obtain ⟨u, hu⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hv).2.2 w hw
  exact ⟨u, u.ne_zero, hu⟩

theorem pCrd_of_map {o K K' : Type} [CommRing o] [Field K] [Field K'] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v : Fin (n + 1) → K} (i : K →+* K') (h : PCrd (spMap i ≫ x) (fun j => i (v j))) : PCrd x v := by
  obtain ⟨w, hw⟩ := FieldPoint.exists_secCoord o n K x
  have hw' := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw).1 K' i
  obtain ⟨u, hu⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw').2.2 _ h
  obtain ⟨k, hk⟩ := exists_ne_zero_of_pCrd h
  have hvk : v k ≠ 0 := fun e => hk (by simp only [e, map_zero])
  have hwk : w k ≠ 0 := fun e => hk (by rw [hu k]; simp only [e, map_zero, mul_zero])
  have hua : (u : K') = i (v k / w k) := by
    rw [map_div₀, eq_div_iff ((map_ne_zero i).2 hwk), hu k]
  have hvj : ∀ j, v j = (v k / w k) * w j := fun j => by
    apply i.injective
    rw [hu j, hua, map_mul]
  have hs := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw).2.1
    (Units.mk0 (v k / w k) (div_ne_zero hvk hwk))
  have e : (fun j => ((Units.mk0 (v k / w k) (div_ne_zero hvk hwk) : Kˣ) : K) * w j) = v :=
    funext fun j => (hvj j).symm
  rw [e] at hs
  exact hs

theorem main : (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x x' : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K), x ≫ PSpace.str o n = x' ≫ PSpace.str o n → PCrd x v → PCrd x' v → x = x') ∧ (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v w : Fin (n + 1) → K), PCrd x v → PCrd x w → ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j) ∧ ∀ (o K K' : Type) [CommRing o] [Field K] [Field K'] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (i : K →+* K'), PCrd (spMap i ≫ x) (fun j => i (v j)) → PCrd x v :=
  ⟨fun _ _ _ _ _ _ _ _ hs h h' => eq_of_pCrd hs h h',
   fun _ _ _ _ _ _ _ _ hv hw => scalar_of_pCrd hv hw,
   fun _ _ _ _ _ _ _ _ _ i h => pCrd_of_map i h⟩

end GlobalTheory.UMin.CrdUniq
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.GalTh

theorem sp_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap]; rw [← Spec.map_comp]; rfl

theorem sp_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp only [spMap]; exact Spec.map_id _

theorem sp_cancel {F K : Type} [Field F] [Field K] (i : F →+* K) {X : Scheme.{0}} (a b : Sp F ⟶ X)
    (h : spMap i ≫ a = spMap i ≫ b) : a = b := by
  haveI : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective a
  obtain ⟨⟨q, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField F X).symm.surjective b
  simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
  rw [← Category.assoc, ← Category.assoc, spMap, ← Spec.map_comp, ← Spec.map_comp] at h
  obtain ⟨rfl, e⟩ := GlobalTheory.SS.residue_embedding_unique _ _ h
  have : φ = ψ := by
    ext c
    have := congrArg (fun g => g.hom c) e
    simp at this
    exact i.injective this
  rw [this]

theorem exists_descend {Ω K : Type} [Field Ω] [Field K] [Algebra Ω K] (H : Subgroup (K ≃ₐ[Ω] K)) {X : Scheme.{0}}
    (p : Sp K ⟶ X) (hp : ∀ τ ∈ H, spMap (τ : K →+* K) ≫ p = p) :
    ∃ q : Sp (IntermediateField.fixedField H) ⟶ X, spMap (algebraMap (IntermediateField.fixedField H) K) ≫ q = p := by
  obtain ⟨E, h₁, h₂, -⟩ := GlobalTheory.SS.exists_fieldOfValues X K p
  refine (h₂ _ (algebraMap (IntermediateField.fixedField H) K)).1 fun c hc => ?_
  have hfix : c ∈ IntermediateField.fixedField H := (IntermediateField.mem_fixedField_iff _ _).2 fun τ hτ =>
    (h₁ (τ : K →+* K) (RingHom.id K)).1 (by rw [sp_id, Category.id_comp]; exact hp τ hτ) c hc
  exact ⟨⟨c, hfix⟩, rfl⟩

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}

theorem thList_transport (m : ℕ) {K : Type} [Field K] {T : Over S} (θ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T))
    {y y' : Sp K ⟶ S} (hy : y = y') (h : Over.mk y ⟶ T) (h' : Over.mk y' ⟶ T) (hh : h.left = h'.left)
    {N : ℕ} (pt : Fin N → (Over.mk y ⟶ G)) (c : Fin N → K)
    (H : ThList G L ρ m y (VVRank.pullS G _ h θ) pt c) :
    ∃ pt' : Fin N → (Over.mk y' ⟶ G), (∀ a, (pt' a).left = (pt a).left) ∧
      ThList G L ρ m y' (VVRank.pullS G _ h' θ) pt' c := by
  subst hy
  obtain rfl : h = h' := Over.OverMorphism.ext hh
  exact ⟨pt, fun _ => rfl, H⟩

theorem thList_comp (m : ℕ) {R K₁ K₂ : Type} [CommRing R] [Field K₁] [Field K₂] (i : R →+* K₁) (j : K₁ →+* K₂)
    (k : R →+* K₂) (hk : j.comp i = k) (x : Sp R ⟶ S) (θ : SecAt G L x) {N : ℕ}
    (pt : Fin N → (Over.mk (spMap j ≫ spMap i ≫ x) ⟶ G)) (c : Fin N → K₂)
    (H : ThList G L ρ m (spMap j ≫ spMap i ≫ x) (SecAt.pull G L (SecAt.pull G L θ i) j) pt c) :
    ∃ pt' : Fin N → (Over.mk (spMap k ≫ x) ⟶ G), (∀ a, (pt' a).left = (pt a).left) ∧
      ThList G L ρ m (spMap k ≫ x) (SecAt.pull G L θ k) pt' c := by
  unfold SecAt.pull at H ⊢
  rw [GlobalTheory.ThetaRuleCompare.pullS_comp] at H
  exact thList_transport m θ (by rw [← hk, sp_comp, Category.assoc]) _ _ (by simp [← hk, sp_comp]) pt c H

end

section
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}

theorem thList_exh {m : ℕ} {K : Type} [Field K] [IsAlgClosed K] {y : Sp K ⟶ S} {θ : SecAt G L y} {N : ℕ}
    {pt : Fin N → (Over.mk y ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m y θ pt c) (p : Over.mk y ⟶ G)
    (hp : p ^ (m ^ 2) = 1) : ∃ a, p = pt a := by
  let u : Over.mk (spMap (RingHom.id K) ≫ y) ⟶ Over.mk y := Over.homMk (spMap (RingHom.id K)) rfl
  obtain ⟨a, ha⟩ := H.2.2 K (RingHom.id K) (u ≫ p) (by rw [← MonObj.comp_pow, hp, MonObj.comp_one])
  refine ⟨a, Over.OverMorphism.ext ?_⟩
  simpa [u, sp_id] using ha

end

end GlobalTheory.UMin.GalTh
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

theorem exists_thG_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x) (p : Over.mk x ⟶ G), Odd m → (m : K) ≠ 0 → PolFib G L g x → p ^ (m ^ 2) = 1 → ∃ c : K, ThG G L ρ m θ p (GlobalTheory.ZH.fn c) := by
  intro S G _ _ L ρ hL hρ g m K _ _ x θ p hm hK hP hpm
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x).hom = (baseOver (Sp K)).hom ≫ x := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨q, hq, hqm⟩ := exists_torsion_down hp τ hτ p hpm
  obtain ⟨v, hv⟩ := ThetaPtExist.exists_isThetaPt hLaw K P m hm hK (fun _ : Unit => q) (fun _ => hqm)
  let c' : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (v ())
  have hvc : v = fun _ => GlobalTheory.Ex.fnOf c' := funext fun u =>
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply (v u)).symm
  rw [hvc] at hv
  obtain ⟨thP, hg, hth⟩ := exists_gen_thG_of_isThetaPt K P ρ' hρ' m Unit (fun _ => q) (fun _ => c') (fun _ => hqm) hv
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp τ hτ hw hL hL₁ thP
  have hgen := ThetaPtUp.isGenSec_up hp τ hτ hw hL hL₁ hrel hg
  have up := ThG.up hp τ hτ hw hL hL₁ hr hq hpm hrel (hth ())
  rw [hi] at up
  obtain ⟨r, hr'⟩ := hgen θ
  have e₁ : SecM.ofSec G θ = r • SecM.ofSec G th := Subtype.ext (funext hr')
  have q' := ThG.smul hL e₁ up
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (show Γ(Sp K, ⊤) from r) * c', ?_⟩
  convert q' using 1
  simp [GlobalTheory.ZH.fn, GlobalTheory.Ex.fnOf, c']

end GlobalTheory.UMin
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem hasDiv_of_hasDiv_symTup : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (N : ℕ)
    (c : Fin N → Ω), Geo.Tor.IsNormalScheme M.Z → M.HasDiv (symTup c) → M.HasDiv c := by
  intro k Ω _ _ _ M N c hn hd z
  obtain ⟨j, he, hdiv⟩ := hd z
  haveI := RatModel.isIntegrallyClosed_O hn z
  set D := N.factorial with hD
  set e := symTup c j with he'
  have hD1 : 1 ≤ D := Nat.factorial_pos N

  haveI : IsFractionRing (M.O z).toSubring Ω := inferInstanceAs (IsFractionRing (M.O z) Ω)
  haveI : IsIntegrallyClosed (M.O z).toSubring := inferInstanceAs (IsIntegrallyClosed (M.O z))
  haveI hcl : IsIntegrallyClosedIn (M.O z).toSubring Ω :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn Ω).1 inferInstance
  have h1 : ∀ a, c a ^ D / e ∈ M.O z := by
    intro a
    have hmem : c a ^ D / e ∈ ⨅ V : {V : ValuationSubring Ω // (M.O z).toSubring ≤ V.toSubring}, V.1.toSubring := by
      refine Subring.mem_iInf.2 fun V => ?_
      refine pow_div_mem_of_esymm_pow_div_mem Ω V.1 (Fin N) c D e he (fun i hi1 hi2 => ?_) a
      simp only [Fintype.card_fin] at hi2
      refine ⟨Nat.dvd_factorial hi1 hi2, V.2 ?_⟩
      have := hdiv ⟨i - 1, by omega⟩
      simp only [symTup, Nat.sub_add_cancel hi1] at this
      exact this
    rw [← Subring.eq_iInf_of_isIntegrallyClosedIn] at hmem
    exact hmem
  haveI : IsLocalRing (M.O z).toSubring := inferInstanceAs (IsLocalRing (M.O z))
  obtain ⟨a, ha, hea⟩ := exists_esymm_pow_div_mem_of_isLocalRing Ω (M.O z).toSubring (Fin N) c D ((j : ℕ) + 1) e hD1
    (by omega) (Nat.dvd_factorial (by omega) (by omega)) he rfl h1
  refine ⟨a, ha, fun b => ?_⟩
  have hpow : (c b / c a) ^ D ∈ M.O z := by
    have : (c b / c a) ^ D = (c b ^ D / e) * (e / c a ^ D) := by
      rw [div_pow, div_mul_div_cancel₀ he]
    rw [this]
    exact mul_mem (h1 b) hea
  have hint : IsIntegral (M.O z) (c b / c a) :=
    IsIntegral.of_pow (by omega) (isIntegral_algebraMap (R := M.O z) (x := ⟨_, hpow⟩))
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact hy ▸ y.2

end GlobalTheory.UMin
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.PrimCmp

theorem esymm_map_hom {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') (M : Multiset R) (j : ℕ) :
    (M.map i).esymm j = i (M.esymm j) := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s _ => ?_)
  simp only [Function.comp, map_multiset_prod]

theorem symTup_map {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun b => i (c b)) j := by
  unfold symTup
  rw [map_pow]
  congr 1
  have hm : Finset.univ.val.map (fun b => i (c b)) = (Finset.univ.val.map c).map i := by
    rw [Multiset.map_map]; rfl
  rw [hm, esymm_map_hom]

theorem esymm_map_mul {R : Type} [CommRing R] {A : Type} (t : R) (M : Multiset A) (f : A → R) (j : ℕ) :
    (M.map fun b => t * f b).esymm j = t ^ j * (M.map f).esymm j := by
  have : (M.map fun b => t * f b) = (M.map f).map (fun x => t * x) := by rw [Multiset.map_map]; rfl
  rw [this]
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s hs => ?_)
  have hc := (Multiset.mem_powersetCard.1 hs).2
  simp only [Function.comp]
  rw [Multiset.prod_map_mul]
  simp [hc]

theorem symTup_mul {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (t : R) (j : Fin N) :
    symTup (fun b => t * c b) j = t ^ N.factorial * symTup c j := by
  unfold symTup
  have h := esymm_map_mul t (Finset.univ.val) c ((j : ℕ) + 1)
  rw [h, mul_pow, ← pow_mul, Nat.mul_div_cancel' (Nat.dvd_factorial (Nat.succ_pos _) j.2)]

theorem mem_of_isIntegralElem {V K : Type} [CommRing V] [Field K] (i : V →+* K) (W : ValuationSubring K)
    (hW : ∀ v, i v ∈ W) {x : K} (hx : i.IsIntegralElem x) : x ∈ W := by
  obtain ⟨p, hm, hp⟩ := hx
  let φ : V →+* W := i.codRestrict W.toSubring hW
  have hφ : (algebraMap W K).comp φ = i := by ext v; rfl
  have hint : IsIntegral W x := ⟨p.map φ, hm.map φ, by rw [Polynomial.eval₂_map, hφ]; exact hp⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  exact y.2

theorem mem_of_pow_mem {K : Type} [Field K] (W : ValuationSubring K) {w : K} {k : ℕ} (hk : 1 ≤ k)
    (h : w ^ k ∈ W) : w ∈ W := by
  rw [← W.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff (by omega)).1 h

theorem mem_range_of_forall {V K : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K]
    (io : FractionRing V →+* K) (z : FractionRing V)
    (h : ∀ W : ValuationSubring K, (∀ v, io (algebraMap V (FractionRing V) v) ∈ W) → io z ∈ W) :
    z ∈ Set.range (algebraMap V (FractionRing V)) := by
  letI : Algebra V K := (io.comp (algebraMap V (FractionRing V))).toAlgebra
  have hic : IsIntegrallyClosedIn (integralClosure V K).toSubring K :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure V K) K)
  have h1 : io z ∈ (integralClosure V K).toSubring := by
    by_contra hn
    obtain ⟨W, hW, hzW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hn
    exact hzW (h W (fun v => hW ((integralClosure V K).algebraMap_mem v)))
  let f : FractionRing V →ₐ[V] K := { io with commutes' := fun _ => rfl }
  have h2 : IsIntegral V z := (isIntegral_algHom_iff f (f : FractionRing V →+* K).injective).1 h1
  exact IsIntegrallyClosed.isIntegral_iff.1 h2

end GlobalTheory.UMin.PrimCmp

namespace GlobalTheory.UMin.PrimCmp

theorem key {V K : Type} [CommRing V] [IsDomain V] [Field K] (io : FractionRing V →+* K) (N : ℕ) (c : Fin N → K) (a : K)
    (ha : a ≠ 0) (hP : Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a)) (e : Fin N → FractionRing V)
    (he : ∀ j, io (e j) = symTup c j) (j₀ : Fin N) (he0 : e j₀ ≠ 0)
    (hq : ∀ j, e j / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) (W : ValuationSubring K)
    (hW : ∀ v, io (algebraMap V (FractionRing V) v) ∈ W) :
    io (e j₀) / a ^ N.factorial ∈ W ∧ (io (e j₀) / a ^ N.factorial)⁻¹ ∈ W := by
  have hcW : ∀ b, c b / a ∈ W := fun b => mem_of_isIntegralElem _ W hW (hP.1 b)
  obtain ⟨b₀, hb0, hb0i⟩ := hP.2
  have hb0W : (c b₀ / a)⁻¹ ∈ W := mem_of_isIntegralElem _ W hW hb0i
  let y : Fin N → W := fun b => ⟨c b / a, hcW b⟩
  have hu : IsUnit (y b₀) := (Units.mkOfMulEqOne (y b₀) ⟨_, hb0W⟩ (Subtype.ext (show c b₀ / a * (c b₀ / a)⁻¹ = 1 from mul_inv_cancel₀ hb0))).isUnit
  let z : Fin N → W := fun b => y b * ↑hu.unit⁻¹
  have hz : z b₀ = 1 := by simp [z]
  obtain ⟨k, hk1, hkN, hku⟩ := GlobalTheory.exists_isUnit_esymm_of_eq_one W (Fin N) z b₀ hz
  have hyz : ∀ b, y b = y b₀ * z b := by
    intro b; simp only [z]; rw [mul_left_comm, IsUnit.mul_val_inv, _root_.mul_one]
  have hesy : IsUnit ((Finset.univ.val.map y).esymm k) := by
    have hm : Finset.univ.val.map y = Finset.univ.val.map (fun b => y b₀ * z b) :=
      Multiset.map_congr rfl fun b _ => hyz b
    rw [hm, esymm_map_mul]
    exact (hu.pow k).mul hku
  have hkN' : k ≤ N := by simpa using hkN
  let j₁ : Fin N := ⟨k - 1, by omega⟩
  have hsy : IsUnit (symTup y j₁) := by
    unfold symTup
    have : (j₁ : ℕ) + 1 = k := by simp only [j₁]; omega
    rw [this]
    exact hesy.pow _
  have hcoe : ∀ j, ((symTup y j : W) : K) = io (e j) / a ^ N.factorial := by
    intro j
    have h1 := symTup_map W.subtype y j
    rw [ValuationSubring.coe_subtype] at h1
    rw [h1]
    have h2 : (fun b => ((y b : W) : K)) = fun b => a⁻¹ * c b := by
      funext b; simp [y, div_eq_inv_mul]
    rw [h2, symTup_mul, he, inv_pow, inv_mul_eq_div]
  have ht : io (e j₀) / a ^ N.factorial ∈ W := hcoe j₀ ▸ (symTup y j₀).2
  obtain ⟨v, hv⟩ := hq j₁
  have hr : io (e j₁ / e j₀) ∈ W := by rw [← hv]; exact hW v
  have hio0 : io (e j₀) ≠ 0 := (map_ne_zero io).2 he0
  have hsplit : symTup y j₁ = ⟨_, hr⟩ * ⟨_, ht⟩ := by
    apply Subtype.ext
    rw [hcoe]
    show _ = io (e j₁ / e j₀) * (io (e j₀) / a ^ N.factorial)
    rw [map_div₀]
    field_simp
  rw [hsplit] at hsy
  have htu := isUnit_of_mul_isUnit_right hsy
  refine ⟨ht, ?_⟩
  have h3 : ((↑htu.unit⁻¹ : W) : K) * (io (e j₀) / a ^ N.factorial) = 1 := by
    have := congrArg Subtype.val (IsUnit.val_inv_mul htu)
    rw [MulMemClass.coe_mul, OneMemClass.coe_one] at this
    exact this
  rw [← eq_inv_of_mul_eq_one_left h3]
  exact (↑htu.unit⁻¹ : W).2

end GlobalTheory.UMin.PrimCmp

theorem GlobalTheory.UMin.prim_symTup_cmp : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [Field K] (io : FractionRing V →+* K) (N N' k : ℕ) (J : Type) (c : Fin N → K) (c' : Fin N' → K) (a : K) (e : Fin N → FractionRing V) (th : J → FractionRing V), a ≠ 0 → 1 ≤ k → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) → Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) → (∀ j, io (e j) = symTup c j) → (∀ x, ∃ b, c' x ^ k = io (th b) ^ k) → (∀ b, ∃ x, c' x ^ k = io (th b) ^ k) → ∀ j₀, e j₀ ≠ 0 → (∀ j, e j / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) → (∀ b, th b ^ N.factorial / e j₀ ∈ Set.range (algebraMap V (FractionRing V))) ∧ ∃ b, th b ≠ 0 ∧ e j₀ / th b ^ N.factorial ∈ Set.range (algebraMap V (FractionRing V)) := by
  intro V K _ _ _ _ io N N' k J c c' a e th ha hk hP hP' he hth1 hth2 j₀ he0 hq
  refine ⟨fun b => ?_, ?_⟩
  · apply GlobalTheory.UMin.PrimCmp.mem_range_of_forall io
    intro W hW
    obtain ⟨-, hti⟩ := GlobalTheory.UMin.PrimCmp.key io N c a ha hP e he j₀ he0 hq W hW
    obtain ⟨x, hx⟩ := hth2 b
    have hw : io (th b) / a ∈ W := by
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [div_pow, ← hx, ← div_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW (hP'.1 x)) k
    have hio0 : io (e j₀) ≠ 0 := (map_ne_zero io).2 he0
    have heq : io (th b ^ N.factorial / e j₀) = (io (th b) / a) ^ N.factorial * (io (e j₀) / a ^ N.factorial)⁻¹ := by
      rw [map_div₀, map_pow, div_pow, inv_div]
      field_simp
    rw [heq]
    exact mul_mem (pow_mem hw _) hti
  · obtain ⟨x₀, hx0, hx0i⟩ := hP'.2
    obtain ⟨b₁, hb1⟩ := hth1 x₀
    have hk0 : k ≠ 0 := by omega
    have hth0 : io (th b₁) ≠ 0 := by
      intro h0
      apply hx0
      have h2 : c' x₀ ^ k = 0 := by rw [hb1, h0, zero_pow hk0]
      simp [pow_eq_zero_iff hk0 |>.1 h2]
    refine ⟨b₁, fun h => hth0 (by rw [h, map_zero]), ?_⟩
    apply GlobalTheory.UMin.PrimCmp.mem_range_of_forall io
    intro W hW
    obtain ⟨ht, -⟩ := GlobalTheory.UMin.PrimCmp.key io N c a ha hP e he j₀ he0 hq W hW
    have hwi : (io (th b₁) / a)⁻¹ ∈ W := by
      refine GlobalTheory.UMin.PrimCmp.mem_of_pow_mem W hk ?_
      rw [inv_pow, div_pow, ← hb1, ← div_pow, ← inv_pow]
      exact pow_mem (GlobalTheory.UMin.PrimCmp.mem_of_isIntegralElem _ W hW hx0i) k
    have heq : io (e j₀ / th b₁ ^ N.factorial) = (io (e j₀) / a ^ N.factorial) * ((io (th b₁) / a)⁻¹) ^ N.factorial := by
      rw [map_div₀, map_pow, inv_div, div_pow]
      field_simp
    rw [heq]
    exact mul_mem ht (pow_mem hwi _)
end
