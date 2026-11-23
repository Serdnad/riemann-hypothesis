module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle073
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelCoverField
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle044
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle107
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle108
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle103
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle094
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTateIsoOfPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsInducedLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

open GlobalTheory.ThetaObjPull GlobalTheory.PolBaseChange

theorem polFam_baseChange : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) (R' : Type) [CommRing R'] (ρ : R →+* R'), PolFam b Mat κ β v A L act Q → ∃ act' Q', PolFam b Mat κ (ρ.comp β) (fun a => ρ (v a)) ((Over.pullback (spMap ρ)).obj A) (L.pull (pullback.fst A.hom (spMap ρ))) act' Q' := by
  intro o _ g N' J b Mat κ R _ β v A _ L act Q R' _ ρ ⟨hab, hdim, hL, hrig, hsym, hamp, ⟨hhom, htor, hbij⟩, hfib⟩
  have h := isGrpPullback_pullback A (spMap ρ)
  have hL' := LB.isLB_pull hL (pullback.fst A.hom (spMap ρ))
  have hiso := lbIso_refl hL'
  obtain ⟨hab', hamp', -⟩ := pol_pull _ _ _ _ _ _ _ _ hL hL' hab h hiso
  choose pt hpt using fun i => exists_sec h (Q i)
  have hpt' : ∀ i, (pt i).left ≫ pullback.fst A.hom (spMap ρ) = spMap ρ ≫ (Q i).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have := hab.comm
  refine ⟨fun j => (Over.pullback (spMap ρ)).map (act j), pt, hab',
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hdim, hL', rigidified_pull h hrig,
    sym_pull h hsym, hamp' hamp, ⟨fun j => inferInstance, fun i => pushHom_injective h _ ?_,
      fun K _ _ x y hy => ?_⟩, fun K _ _ x s t ht => ?_⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (toBase (spMap ρ))) _ _).symm.trans (by rw [htor, map_one])
  · have key : ∀ c : Ix g N', pushHom h (Over.mk x) (Out.linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R')) ≫ pt i) (fun i => (c i).val)) =
        Out.linComb (fun i => (Over.homMk (x ≫ spMap ρ) (by simp) :
          Over.mk (x ≫ spMap ρ) ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) := fun c => by
      rw [map_linComb]
      congr 1
      funext i
      apply Over.OverMorphism.ext
      show (x ≫ (pt i).left) ≫ _ = (x ≫ spMap ρ) ≫ (Q i).left
      rw [Category.assoc, hpt', Category.assoc]
    have hy' : pushHom h (Over.mk x) y ^ N' = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc, hu⟩ := hbij K (x ≫ spMap ρ) (pushHom h (Over.mk x) y) hy'
    exact ⟨c, pushHom_injective h _ ((key c).trans hc), fun c' hc' => hu c' ((key c').symm.trans (congrArg _ hc'))⟩
  · obtain ⟨ψ, ⟨k₁, k₄, k₃⟩, k₂⟩ := hfib K (x.comp ρ) s t ((good_comp _ _ _).1 ht)
    rw [spMap_comp] at k₁ k₃
    have hp := h.1
    obtain ⟨F, hF, hw⟩ : ∃ F : t.A.left ⟶ ((Over.pullback (spMap ρ)).obj A).left,
        F ≫ pullback.fst A.hom (spMap ρ) = ψ ∧
        F ≫ ((Over.pullback (spMap ρ)).obj A).hom = t.A.hom ≫ spMap x :=
      ⟨hp.lift ψ (t.A.hom ≫ spMap x) (by rw [k₁.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
    subst hF
    have h₄ : ∀ j, ((Over.pullback (spMap ρ)).map (act j)).left ≫ pullback.fst A.hom (spMap ρ) =
        pullback.fst A.hom (spMap ρ) ≫ (act j).left := fun j => pullback.lift_fst _ _ _
    refine ⟨F, ⟨h.cancel k₁ hw, fun j => ?_, fun i => ?_⟩, ?_⟩
    · apply hp.hom_ext
      · rw [Category.assoc, k₄, Category.assoc, Category.assoc, h₄]
      · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]
    · apply hp.hom_ext
      · rw [Category.assoc, k₃, Category.assoc, Category.assoc, hpt']
      · have a₁ : (t.pt i ^ N').left ≫ t.A.hom = 𝟙 _ := Over.w (t.pt i ^ N')
        have a₂ : (pt i).left ≫ ((Over.pullback (spMap ρ)).obj A).hom = 𝟙 _ := Over.w (pt i)
        rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact LBIso.trans t.isLB (LB.isLB_pull hL _) (LB.isLB_pull hL' _) k₂ (lbIso_pull_comp hiso F).symm

end GlobalTheory.ZM.NearBuild
end
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.LevelCover

namespace GlobalTheory.LevCover

private theorem levStrRep_lemma (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {B : Type} [Field B] {b : Base l B} {S : Scheme.{0}} [IsLocallyNoetherian S]
    {s : S ⟶ Sp B} (o : Obj D l b s) (hpq : 1 ≤ D.p + D.q) (l₂ : Level H) (b₂ : Base l₂ B) (hd : l.Dvd l₂)
    (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) :
    ∃ (V : Over S) (χ θ : D.La → (V ⟶ o.t.G)), IsFinite V.hom ∧ Etale V.hom ∧ Surjective V.hom ∧
      LevStr o b₂ V χ θ ∧
      (∀ (T : Over S) (u u' : T ⟶ V), (∀ a, u ≫ χ a = u' ≫ χ a) → (∀ a, u ≫ θ a = u' ≫ θ a) → u = u') ∧
      ∀ (T : Over S) (χ' θ' : D.La → (T ⟶ o.t.G)), LevStr o b₂ T χ' θ' →
        ∃ h : T ⟶ V, (∀ a, h ≫ χ a = χ' a) ∧ ∀ a, h ≫ θ a = θ' a := by
  have hsim := SimAlg.sim_group E H D hpq
  obtain ⟨hfree, hfin⟩ := datum_free D
  refine exists_levStr_rep o l₂ b₂ hd hζ (fun g n k hn hk => hsim.1 g n k hn hk)
    (fun N f ν => exists_sim_lift E H D N f ν)
    (fun l' N ν => SimMult.exists_sim_trivial_of_mult SimAlg.sim_group exists_sim_lift E H D l' N ν) ?_ ?_
  · intro n hn
    have hu : IsUnit ((n : ℕ) : Γ(S, ⊤)) := by
      simpa using (b.unit n hn).map (fnOn s)
    obtain ⟨Z, et, hZ⟩ :=
      exists_finiteEtale_latticeTorsionHom S o.t.G n D.La (ObjDim.isAbelianScheme o) hu
    exact ⟨Z, et, hZ⟩
  · intro N _ T x y c hN hx hy hc
    exact PairingLocus.exists_clopen_of_isLocallyNoetherian hL S (GlobalTheory.Obj.toPolAV o) N T x y c hN hx hy hc

private theorem weilIs_iff_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (T' : Over S') (k : ℤ) (x y : T' ⟶ t'.G)
    (x₀ y₀ : Over.mk (T'.hom ≫ f) ⟶ t.G) (c : Γ(T'.left, ⊤)ˣ) (h₁ : x₀.left = x.left ≫ m.φ)
    (h₂ : y₀.left = y.left ≫ m.φ) : Out.WeilIs t'.G t'.PP.L k x y c ↔ Out.WeilIs t.G t.PP.L k x₀ y₀ c :=
  weilIs_grpPullback_of_comm S S' t.G t'.G f m.φ t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB m.cart (sabMap_lbIso m)
    T' k x y x₀ y₀ c h₁ h₂

private theorem lieMult_iff_of_sabMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) (k : Type) [Field k] (x : Sp k ⟶ S')
    (τ : 𝓞 E →+* k) (n : ℕ) : LieMult t'.act x τ n ↔ LieMult t.act (x ≫ f) τ n :=
  LiePull.lieMult_pull (𝓞 E) S S' t.G t'.G f m.φ t.act t'.act m.cart m.act k x τ n

theorem levelCover_noetherian (hL : Out.Laws) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsLocallyNoetherian S → 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂ : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ := by
  intro E _ _ _ H D l l₂ B _ b b₂ S s o hS hpq hd hρ hζ
  have := hS
  obtain ⟨V, χ, θ, hVf, hVe, hVs, hlev, hext, hex⟩ := levStrRep_lemma hL o hpq l₂ b₂ hd hζ
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l B B b b (RingHom.id B) S V.left s (V.hom ≫ s) V.hom rfl rfl
    (by rw [spMap_id', Category.comp_id]) o
  obtain ⟨o₂, m, hm, hχ, hθ⟩ := obj_of_levStr o hρ V o₁.t n₁.toSABMap (weilIs_iff_of_sabMap n₁.toSABMap)
    (fun k _ x τ n => lieMult_iff_of_sabMap n₁.toSABMap k x τ n) o₁.ample o₁.ktriv hlev
  refine ⟨V.left, V.hom, o₂, m, hVf, hVe, hVs, hm, ?_⟩
  intro T f o' m' hc
  obtain ⟨χ', θ', hlev', hχ', hθ'⟩ := levStr_of_obj o (Over.mk f) o' m' (weilIs_iff_of_sabMap m') hc.1 hc.2
  obtain ⟨g, hgχ, hgθ⟩ := hex (Over.mk f) χ' θ' hlev'
  have hg : g.left ≫ V.hom = f := by simpa using Over.w g
  obtain ⟨u, hu⟩ := sab_cancel m m' g.left hg

  have key : ∀ a, ((o'.eta a).left ≫ m'.φ = g.left ≫ (o₂.eta a).left ≫ m.φ) ∧
      ((o'.etaA a).left ≫ m'.φ = g.left ≫ (o₂.etaA a).left ≫ m.φ) := fun a => by
    constructor
    · rw [← hχ' a, ← hgχ a, Over.comp_left, hχ a]
    · rw [← hθ' a, ← hgθ a, Over.comp_left, hθ a]
  have hη : ∀ a, (o'.eta a).left ≫ u.φ = g.left ≫ (o₂.eta a).left := fun a =>
    sec_cancel u m (o'.eta a) (o₂.eta a) (by rw [hu]; exact (key a).1)
  have hηA : ∀ a, (o'.etaA a).left ≫ u.φ = g.left ≫ (o₂.etaA a).left := fun a =>
    sec_cancel u m (o'.etaA a) (o₂.etaA a) (by rw [hu]; exact (key a).2)
  refine ⟨g.left, ⟨hg, ⟨u, hη, hηA⟩, hu⟩, ?_⟩
  rintro h' ⟨hh', ⟨u', hu₁, hu₂⟩, hu'⟩
  have hu'' : u'.cm.F ≫ m.φ = m'.φ := hu'
  have hgg : (Over.homMk h' hh' : Over.mk f ⟶ V) = g := by
    apply hext
    · intro a
      ext1
      simp only [Over.comp_left, hχ a, Over.homMk_left]
      rw [← (key a).1, ← Category.assoc, ← hu₁ a, Category.assoc, hu'']
    · intro a
      ext1
      simp only [Over.comp_left, hθ a, Over.homMk_left]
      rw [← (key a).2, ← Category.assoc, ← hu₂ a, Category.assoc, hu'']
  rw [← hgg]
  rfl

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem levelMap_over_field_noetherian (hL : Out.Laws)
    (Xo : Moduli D l) (Xo₂ : Moduli D l₂) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) (r : Xo₂.X ⟶ Xo.X)
    (m : SABMap Xo₂.univ.t Xo.univ.t r)
    (hm₁ : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (hm₂ : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (F : Type) [Field F] (b : Base l F) (b₂ : Base l₂ F) (j : KA l →+* F) (j₂ : KA l₂ →+* F)
    (e₁ : j (baseKA l).ρ = b.ρ) (e₂ : j (baseKA l).ζ = b.ζ) (e₃ : j₂ (baseKA l₂).ρ = b₂.ρ)
    (e₄ : j₂ (baseKA l₂).ζ = b₂.ζ) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A))
    (rF : pullback Xo₂.s (spMap j₂) ⟶ pullback Xo.s (spMap j))
    (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r) (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _) :
    IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  have hsm0 : Smooth Xo.s := by
    have := Xo.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo.s
  have hsm0₂ : Smooth Xo₂.s := by
    have := Xo₂.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo₂.s
  have hsmX : Smooth (pullback.snd Xo.s (spMap j)) := inferInstance
  have hsmX₂ : Smooth (pullback.snd Xo₂.s (spMap j₂)) := inferInstance
  obtain ⟨rX, -, nX⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmX
  obtain ⟨rX₂, -, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmX₂

  obtain ⟨o, ⟨no⟩⟩ := obj_pull E H D l (KA l) F (baseKA l) b j Xo.X (pullback Xo.s (spMap j)) Xo.s
    (pullback.snd _ _) (pullback.fst _ _) e₁ e₂ pullback.condition Xo.univ
  obtain ⟨o₂, ⟨no₂⟩⟩ := obj_pull E H D l₂ (KA l₂) F (baseKA l₂) b₂ j₂ Xo₂.X (pullback Xo₂.s (spMap j₂)) Xo₂.s
    (rF ≫ pullback.snd _ _) (pullback.fst _ _) e₃ e₄ (by rw [h₂]; exact pullback.condition) Xo₂.univ
  have hno1 : ∀ a, (o.eta a).left ≫ no.toSABMap.φ = pullback.fst _ _ ≫ (Xo.univ.eta a).left := no.2
  have hno2 : ∀ a, (o.etaA a).left ≫ no.toSABMap.φ = pullback.fst _ _ ≫ (Xo.univ.etaA a).left := no.3
  have hno₂1 : ∀ a, (o₂.eta a).left ≫ no₂.toSABMap.φ = pullback.fst _ _ ≫ (Xo₂.univ.eta a).left := no₂.2
  have hno₂2 : ∀ a, (o₂.etaA a).left ≫ no₂.toSABMap.φ = pullback.fst _ _ ≫ (Xo₂.univ.etaA a).left := no₂.3
  have hRX : Represents o := represents_pullback ObjMaps.id_comp_cancel Xo j
    (fun S s o' hS => moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo F b j S s o' hS e₁ e₂) rfl o no
  have hRX₂ : Represents o₂ := represents_pullback ObjMaps.id_comp_cancel Xo₂ j₂
    (fun S s o' hS => moduli_rep_of_base ObjMaps.id_comp_cancel E H D l₂ Xo₂ F b₂ j₂ S s o' hS e₃ e₄) h₂ o₂ no₂

  obtain ⟨Y, π, oc, mc, hπf, hπe, hπs, hmc, huniv⟩ :=
    levelCover_noetherian hL E H D l l₂ F b b₂ _ (pullback.snd Xo.s (spMap j)) o nX hpq hd hρ hζ
  have hsmπ : Smooth π := inferInstance
  have hsmY : Smooth (π ≫ pullback.snd Xo.s (spMap j)) := inferInstance
  obtain ⟨rY, -, -⟩ := isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field F _ _ hsmY
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l F F b b (RingHom.id F) _ Y (pullback.snd _ _) (π ≫ pullback.snd _ _) π
    rfl rfl (by rw [spMap_id', Category.comp_id]) o

  obtain ⟨mcomp, hmcomp⟩ := sab_comp no₂.toSABMap m h₁.symm
  obtain ⟨m₂, hm₂'⟩ := sab_cancel no.toSABMap mcomp rF rfl
  have hm₂c : (∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m₂.φ = rF ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m₂.φ = rF ≫ (o.etaA a).left) := by
    constructor
    · intro a
      apply sec_cancel m₂ no.toSABMap
      rw [hm₂', hmcomp, ← Category.assoc, sec_pow _ _ _ (hno₂1 a), Category.assoc, hm₁ a, ← Category.assoc,
        ← h₁, Category.assoc, hno1 a]
    · intro a
      apply sec_cancel m₂ no.toSABMap
      rw [hm₂', hmcomp, ← Category.assoc, sec_pow _ _ _ (hno₂2 a), Category.assoc, hm₂ a, ← Category.assoc,
        ← h₁, Category.assoc, hno2 a]
  obtain ⟨h, hiso, hπ⟩ := iso_cover ObjMaps.id_comp_cancel (l₂.M / l.M) (l₂.A / l.A) o o₂ oc o₁ n₁ m₂ mc hm₂c hmc
    hRX hRX₂ rX₂ rY (obj_rigid_closed hL E H D l F F b b _ Y (pullback.snd _ _) (π ≫ pullback.snd _ _) o o₁ π
      (Or.inl rY)) huniv
  rw [← hπ]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end

theorem levelMap_finite_etale_surjective_of_laws (hL : Out.Laws) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo : Moduli D l) (Xo₂ : Moduli D l₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (r : Xo₂.X ⟶ Xo.X) (jK : KA l →+* KA l₂) (m : SABMap Xo₂.univ.t Xo.univ.t r), (∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ)) ∧ r ≫ Xo.s = Xo₂.s ≫ spMap jK ∧ (∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left) ∧ (∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left) → ∀ (c : Coeff l) (c₂ : Coeff l₂) (hc : c.F = c₂.F) (rF : Xo₂.XF c₂ ⟶ Xo.XF c), rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r → rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom → IsFinite rF ∧ Etale rF ∧ Surjective rF := by
  intro E _ _ _ H D l l₂ Xo Xo₂ hpq hd r jK m hr c c₂ hc rF h₁ h₂
  obtain ⟨-, -, hm₁, hm₂⟩ := hr
  obtain ⟨F, fin, conj, zm, le⟩ := c
  obtain ⟨F₂, fin₂, conj₂, zm₂, le₂⟩ := c₂
  dsimp only at hc
  subst hc
  rw [spMap_inclusion_self, Category.comp_id] at h₂
  exact levelMap_over_field_noetherian hL Xo Xo₂ hpq hd r m hm₁ hm₂ F (baseOf l F le) (baseOf l₂ F le₂)
    (IntermediateField.inclusion le).toRingHom (IntermediateField.inclusion le₂).toRingHom rfl rfl rfl rfl
    (baseOf_rho l l₂ F le le₂) (baseOf_zeta l l₂ F le le₂ hd.2.2) rF h₁ h₂

end GlobalTheory.LevCover
end
end

section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory


open PeriodTate in
theorem exists_tateIso_of_periodMap_genus : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (Q : D'.La →+ (Fin P.g → ℂ)), 1 ≤ D.p + D.q → (D'.p = D.p ∧ D'.q = D.q ∧ (∀ n m : ℕ, 0 < n → 0 < m → ∀ x, ∃ y, f (n * m) x = f n x + n • y) ∧ (∀ n : ℕ, 0 < n → (∀ x, (∃ y, f n x = n • y) ↔ ∃ y, x = n • y) ∧ ∀ x', ∃ x y, x' = f n x + n • y) ∧ ∀ n : ℕ, 0 < n → ∀ x x', (n : ℤ) ∣ D'.EF (f n x) (f n x') - ν n * D.EF x x') → u.IsAH Hm χ → Function.Injective Q → (∀ z, z ∈ u.Λ ↔ z ∈ Q.range) → (∀ x y, (hermForm Hm (Q x) (Q y)).im = D'.EF x y) → (∀ (a : 𝓞 E) (n : ℕ) x, u.ex ((n : ℂ)⁻¹ • Q (a • x)) = u.ex ((n : ℂ)⁻¹ • Q x) ≫ act.act a) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : ℂ →+* K), ∃ I : TateIso D K (Over.mk (spMap β) ⟶ P.A) (fun c y => y ≫ act.act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)), ∀ n : ℕ, 0 < n → (I.ζ n : K) = β (Complex.exp (-(2 * Real.pi * Complex.I) * (ν n : ℂ) / n)) ∧ ∀ x, (I.ev n x).left = spMap β ≫ (u.ex ((n : ℂ)⁻¹ • Q (f n x))).left := by
  intro hL hL2 hT hU E _ _ _ H D D' f ν Q u Hm χ act P hpq ⟨_, _, htow, hmod, hν⟩ hAH hinj hΛ hE hact k _ _ β
  obtain ⟨Ef, hEf, -, -, -, -, -, -, hW₀⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm hL hL2 hT hU Q u Hm χ hAH
  have hadd := u.ex_add
  have hsurj := u.ex_onto
  have hker : ∀ z, u.ex z = 1 ↔ z ∈ P.range := fun z => (u.ker z).trans (hΛ z)
  have hW : ∀ (n : ℕ) (a b : D'.La), 0 < n →
      Out.WeilIs Q.A Q.L n (u.ex ((n : ℂ)⁻¹ • P a)) (u.ex ((n : ℂ)⁻¹ • P b)) (unitOn (rt n (D'.EF a b))) := by
    intro n a b hn
    have h : Ef ⟨P a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨P b, (hΛ _).2 ⟨b, rfl⟩⟩ = D'.EF a b := by
      have := (hEf ⟨P a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨P b, (hΛ _).2 ⟨b, rfl⟩⟩).trans (hE a b)
      exact_mod_cast this
    exact hW₀ n ⟨P a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨P b, (hΛ _).2 ⟨b, rfl⟩⟩ _ hn (by rw [h, rt_val])
  generalize u.ex = e at hadd hsurj hker hW hact ⊢
  have : Nontrivial D.La := Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D.rank]; omega)
  obtain ⟨a₀, b₀, h₀⟩ := exists_pairing_one D
  have : Nontrivial D'.La := by
    refine ⟨f 2 a₀, 0, fun h => ?_⟩
    obtain ⟨c, hc⟩ := ((hmod 2 two_pos).1 a₀).1 ⟨0, by rw [h, smul_zero]⟩
    rw [hc, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h₀
    omega
  obtain ⟨a₁, b₁, h₁⟩ := exists_pairing_one D'
  have hcong : ∀ (n : ℕ) (a b c d : D'.La), (n : ℤ) ∣ D'.EF (a + n • c) (b + n • d) - D'.EF a b := by
    intro n a b c d
    refine ⟨D'.EF a d + D'.EF c b + n * D'.EF c d, ?_⟩
    simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  have hcop : ∀ n : ℕ, 0 < n → IsCoprime (ν n) n := by
    intro n hn
    obtain ⟨a, c, ha⟩ := (hmod n hn).2 a₁
    obtain ⟨b, d, hb⟩ := (hmod n hn).2 b₁
    obtain ⟨s, hs⟩ := hcong n (f n a) (f n b) c d
    obtain ⟨v, hv⟩ := hν n hn a b
    rw [← ha, ← hb, h₁] at hs
    exact ⟨D.EF a b, s + v, by linear_combination -hs - hv⟩
  have hνt : ∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n := by
    intro n m hn hm
    obtain ⟨c, hc⟩ := htow n m hn hm a₀
    obtain ⟨d, hd⟩ := htow n m hn hm b₀
    obtain ⟨s, hs⟩ := hcong n (f n a₀) (f n b₀) c d
    obtain ⟨v, hv⟩ := hν n hn a₀ b₀
    obtain ⟨w, hw⟩ := hν (n * m) (Nat.mul_pos hn hm) a₀ b₀
    rw [← hc, ← hd] at hs
    rw [h₀] at hv hw
    push_cast at hw
    exact ⟨s + v - m * w, by linear_combination hs + hv - hw⟩
  let e' : Multiplicative (Fin Q.g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ Q.A) :=
    MonoidHom.mk' (fun z => e z.toAdd) fun z w => hadd _ _
  have hpow : ∀ (n : ℕ) z, e z ^ n = e (n • z) := fun n z => (map_pow e' (Multiplicative.ofAdd z) n).symm
  let ρ := preHom (G := Q.A) (toUnit (Over.mk (spMap β)))
  have hρ : Function.Injective ρ := pre_injective β Q.A
  have hl : (toUnit (Over.mk (spMap β))).left = spMap β := by
    simpa using Over.w (toUnit (Over.mk (spMap β)))
  have hsm : ∀ n : ℕ, 0 < n → ∀ z : Fin Q.g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n hn z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
  have hsm' : ∀ n : ℕ, 0 < n → ∀ z : Fin Q.g → ℂ, (n : ℂ)⁻¹ • n • z = z := fun n hn z => by
    rw [smul_comm, hsm n hn]
  have hshift : ∀ n : ℕ, 0 < n → ∀ a c : D'.La, e ((n : ℂ)⁻¹ • P (a + n • c)) = e ((n : ℂ)⁻¹ • P a) := by
    intro n hn a c
    rw [map_add (f := _), smul_add, hadd, map_nsmul, hsm' n hn, (hker _).2 ⟨c, rfl⟩, _root_.mul_one]
  refine ⟨{ ζ := fun n => Units.map β.toMonoidHom (rt n (ν n))
            ζ_prim := fun n hn => (rt_prim hn (hcop n hn)).map_of_injective (Units.map_injective β.injective)
            ζ_pow := fun n m hn hm => by rw [← map_pow, rt_pow hm, rt_congr hn (hνt n m hn hm)]
            ev := fun n a => ρ (e ((n : ℂ)⁻¹ • P (f n a)))
            add := fun n a b => by rw [map_add (f := _), map_add (f := _), smul_add, hadd, map_mul]
            lin := fun n c a => ?_
            ker := fun n hn a => ?_
            onto := fun n hn x => ?_
            tower := fun n m hn hm a => ?_
            isom := fun n hn a b => ?_ }, fun n _ => ⟨rfl, fun a => ?_⟩⟩
  · show toUnit (Over.mk (spMap β)) ≫ _ = (toUnit (Over.mk (spMap β)) ≫ _) ≫ _
    rw [Category.assoc, ← hact, map_smul]
  · rw [map_eq_one_iff ρ hρ, hker, ← (hmod n hn).1 a]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, hinj (by rw [map_nsmul, hc, hsm n hn])⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, map_nsmul, hsm' n hn]⟩
  · constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := pre_onto hL.mulN β Q hn x hx
      obtain ⟨z, rfl⟩ := hsurj y
      rw [hpow, hker] at hy
      obtain ⟨a', ha'⟩ := hy
      obtain ⟨a, c, rfl⟩ := (hmod n hn).2 a'
      refine ⟨a, congrArg ρ ?_⟩
      rw [← hshift n hn _ c, ha', hsm' n hn]
    · rintro ⟨a, rfl⟩
      rw [← map_pow, hpow, hsm n hn, (hker _).2 ⟨_, rfl⟩, map_one]
  · obtain ⟨c, hc⟩ := htow n m hn hm a
    rw [← map_pow, hpow, Nat.cast_mul, mul_inv_rev, mul_smul, hsm m hm, hc, hshift n hn]
  · have h := CommPairing.weilIs_pull hL.globalFns Q.isAb Q.isLB (toUnit (Over.mk (spMap β)))
      (hW n (f n a) (f n b) hn)
    rw [unitOn_pull, rt_congr hn (hν n hn a b), rt_mul, map_zpow] at h
    exact h
  · exact congrArg (· ≫ (e ((n : ℂ)⁻¹ • P (f n a))).left) hl

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_nonzero_sec_lbPow_div : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left), N.IsLB → ∃ (n : ℕ) (s : (LB.div (lbPow P.L n) N).Sec), ∃ j, s.f j ≠ 0 := by
  first | exact @GlobalTheory.exists_sec_lbPow_div_ne_zero | exact GlobalTheory.exists_sec_lbPow_div_ne_zero | (intros; apply GlobalTheory.exists_sec_lbPow_div_ne_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem isQProjOver_of_isPullback_spMap {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') {Y Y' : Scheme.{0}}
    {s : Y ⟶ Sp R} {p : Y' ⟶ Y} {s' : Y' ⟶ Sp R'} (sq : IsPullback p s' s (spMap j)) (h : IsQProjOver s) :
    IsQProjOver s' := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have P := ProjSpace.isPullback_baseChange N j
  have w : (p ≫ i) ≫ PSpace.str R N = s' ≫ spMap j := by rw [Category.assoc]; exact sq.w
  have Q : IsPullback p (P.lift (p ≫ i) s' w) i (ProjSpace.baseChange N j) :=
    IsPullback.of_bot (by rw [P.lift_snd]; exact sq) (P.lift_fst _ _ w).symm P
  exact ⟨N, P.lift (p ≫ i) s' w, MorphismProperty.of_isPullback (P := @IsImmersion) Q hi,
    MorphismProperty.of_isPullback (P := @QuasiCompact) Q hq, P.lift_snd _ _ w⟩

theorem isQProjOver_comp_spMap_of_finiteType {R R' : Type} [CommRing R] [CommRing R'] {j : R →+* R'}
    (hj : j.FiniteType) {Y : Scheme.{0}} {s' : Y ⟶ Sp R'} (h : IsQProjOver s') : IsQProjOver (s' ≫ spMap j) := by
  obtain ⟨N, i, _, _, rfl⟩ := h
  have := isProper_str R' N
  have : LocallyOfFiniteType (spMap j) := HasRingHomProperty.Spec_iff.2 hj
  exact ((isAmple_projective_O_one R' N).pull_of_isImmersion i).isQProjOver _

theorem isQProjOver_baseChange_and_finite_restrict :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (j : R →+* R') (Y : Scheme.{0}) (s : Y ⟶ Sp R),
      (IsQProjOver s → IsQProjOver (pullback.snd s (spMap j))) ∧
        ∀ s' : Y ⟶ Sp R', j.Finite → IsQProjOver s' → IsQProjOver (s' ≫ spMap j) :=
  fun _ _ _ _ j _ _ => ⟨fun h => isQProjOver_of_isPullback_spMap j (IsPullback.of_hasPullback _ _) h,
    fun _ hj h => isQProjOver_comp_spMap_of_finiteType hj.finiteType h⟩

end GlobalTheory
end
