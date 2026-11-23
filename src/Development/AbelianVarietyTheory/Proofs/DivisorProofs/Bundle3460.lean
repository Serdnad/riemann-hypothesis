module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3459
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2690
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle129
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.PoincTop

theorem poinSt : PoinSt := by
  intro g hg n hn hodd F Z z i hth OZ hOZ hamp φ hφ
  obtain ⟨hproj, hnorm, hoi, hiz, hdense, W8, hW8, hthi⟩ := hth
  obtain ⟨d, J, hd, hJ, hval⟩ :=
    GlobalTheory.T.exists_fanOrder_ideal_thetaCompactification g hg n hn hodd F Z z i ⟨hproj, hnorm, hoi, hiz, hdense, W8, hW8, hthi⟩ φ hφ
  haveI := hoi
  let W : Z.Opens := i.opensRange
  have hWset : (W : Set Z) = Set.range i := by simp [W]
  obtain ⟨S, π, BD, hbl, hpS, hBD, hiso, hdS⟩ :=
    GlobalTheory.T.exists_normalised_blowup_cyclotomicAway_projective n Z z hproj (GlobalTheory.IsNormalScheme.pred Z) J W (by rw [hWset]; exact hdense)
      (fun x hx hxW => hJ x hx (by have h : x ∈ (W : Set Z) := hxW; rwa [hWset] at h))
  haveI := hiso
  let A : F.X ⟶ (π ⁻¹ᵁ W).toScheme := i.isoOpensRange.hom ≫ inv (π ∣_ W)
  let j : F.X ⟶ S := A ≫ (π ⁻¹ᵁ W).ι
  have hjπ : j ≫ π = i := by
    simp only [j, A, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    simp [W]
  have hrj : Set.range j = π ⁻¹' Set.range i := by
    have hA : Function.Surjective A := A.surjective
    change Set.range ((π ⁻¹ᵁ W).ι ∘ A) = _
    rw [Set.range_comp, hA.range_eq, Set.image_univ, Scheme.Opens.range_ι, ← hWset]
    rfl
  refine ⟨d, J, S, π, j, BD, hd, hJ, hval, hbl, hpS, inferInstance, ?_, hjπ, hrj.symm, hBD, ?_, ?_⟩
  · rw [hrj, ← hWset]; exact hdS
  · intro T ξ hξ
    obtain ⟨a, ha, hid⟩ := hval T (ξ ≫ π) (by rw [← Category.assoc, hξ, Category.assoc, hjπ])
    refine ⟨a, ha, ?_⟩
    rw [hBD, GlobalTheory.PullAlong.idlAlong_comap_eq]
    exact hid
  · obtain ⟨S₀, π₀, ν, U, hb, hνπ, hfin, -⟩ := hbl.2
    haveI : Algebra.FiniteType ℤ (cycAway n) := finiteType_cycAway n
    haveI : IsNoetherianRing (cycAway n) := Algebra.FiniteType.isNoetherianRing ℤ _
    obtain ⟨T₀, hT⟩ := GlobalTheory.T.ample_twist_normalisedBlowup_noetherian_domain (cycAway n) Z S₀ S z J π₀ ν BD hproj hb hfin
      (by rw [hνπ]; exact hBD) OZ hamp
    refine ⟨T₀, fun k hk => ?_⟩
    have h := hT k hk
    rwa [hνπ] at h

end GlobalTheory.PoincTop
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_tautological_chart_at_siegel_blowup_point : ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), MinAt5 F z i OZ → BlowAt F z i φ d π j BD → ∀ x : S, ∃ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) (_ : GrpObj G₁) (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ ∧ y ≫ j = jK C.R ≫ ξ ∧ ξ (closedPoint C.R) = x := by
  first | exact @GlobalTheory.TChart.exists_chart_at | exact GlobalTheory.TChart.exists_chart_at | (intros; apply GlobalTheory.TChart.exists_chart_at <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_pointRigid_tautological_chart_unitary_boundary : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (k : Type) (_ : Field k) (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S), IsTautB C ∧ C.y ≫ j = jK _ ≫ ξ ∧ ξ (closedPoint _) = x := by
  first | exact @GlobalTheory.UCanon.exists_tautB_chart_at | exact GlobalTheory.UCanon.exists_tautB_chart_at | (intros; apply GlobalTheory.UCanon.exists_tautB_chart_at <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFamAll

theorem exists_classify_affine {g n : ℕ} (hg : 1 ≤ g) (hn : 3 ≤ n) (hodd : Odd n) (F : SFam g n (zetaAway n))
    (R : Type) [CommRing R] (t : Sp R ⟶ Sp (cycAway n)) (d : SiegPre g n (zetaAway n) t) (hd : d.Principal) :
    ∃ f : Sp R ⟶ F.X, f ≫ F.s = t ∧ SiegPB d F.univ f := by
  obtain ⟨β, rfl⟩ := GlobalTheory.SiegelRingChange.exists_spMap t
  obtain ⟨R₀, β₀, c₀, hft, hβ, hp₀, hpb⟩ := GlobalTheory.T.principalSiegel_descends_finiteType_subring g n hn hodd R β d hd
  haveI : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  obtain ⟨f₀, hf₀, hpb₀⟩ := GlobalTheory.T.siegelFamily_classifies_noetherian g n hg hn hodd F R₀ β₀ c₀ hp₀
  refine ⟨spMap R₀.subtype ≫ f₀, ?_, GlobalTheory.TChart.AbLevel.siegPB_trans hpb hpb₀⟩
  rw [Category.assoc, hf₀, ← GlobalTheory.SiegelRingChange.spMap_comp', hβ]

theorem existsUnique_classify : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s'), c.Principal →
      ∃! f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  intro g n hg hn hodd F S s' c hc
  obtain ⟨f, hf, hpf⟩ := GlobalTheory.T.siegelFamily_classified_of_local g n hg hn hodd F S s' c hc (fun x => by
    let 𝒰 := S.affineOpenCover
    let j : Sp (𝒰.X (𝒰.idx x)) ⟶ S := 𝒰.f (𝒰.idx x)
    have hid : j ≫ s' = (j ≫ s') ≫ spMap (RingHom.id (cycAway n)) := by simp [spMap]
    have key := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) S (Sp (𝒰.X (𝒰.idx x))) s' (j ≫ s') j rfl hid
    obtain ⟨cV, hcV⟩ := key.1 c
    have hpV : cV.Principal := key.2.1 c cV hcV hc
    obtain ⟨fV, hfV, hpbV⟩ := exists_classify_affine hg hn hodd F (𝒰.X (𝒰.idx x)) (j ≫ s') cV hpV
    exact ⟨Sp (𝒰.X (𝒰.idx x)), j, cV, inferInstance, 𝒰.covers x, hcV, fV, hfV, hpbV⟩)
  exact ⟨f, ⟨hf, hpf⟩, fun f' hf' => GlobalTheory.T.siegelFamily_classifyingMap_unique g n hg hn hodd F S s' c f' f hf'.1 hf hf'.2 hpf⟩

end GlobalTheory.SiegFamAll
end
