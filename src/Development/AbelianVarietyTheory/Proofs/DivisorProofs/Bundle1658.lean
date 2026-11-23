module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle012
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanPf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.SemistableReduction.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LevelFree

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LevPull

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem eta_injective (Xo : Moduli Dw l) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ Xo.X) (β : KA l →+* k)
    (hx : x ≫ Xo.s = spMap β) (a : Dw.La) (h : toUnit (Over.mk x) ≫ Xo.univ.eta a = 1) :
    a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨-, I, -, -, hI⟩ := Xo.univ.geom k x β hx
  have htop : l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) = ⊤ := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La) := by
    rw [htop]; trivial
  obtain ⟨a₂, h₂, a₁, h₁, rfl⟩ := Submodule.mem_sup.1 ha
  have e : toUnit (Over.mk x) ≫ Xo.univ.eta (a₂ + a₁) = toUnit (Over.mk x) ≫ Xo.univ.eta a₁ := by
    rw [Xo.univ.eta_add, Xo.univ.eta_ker a₂ h₂, _root_.one_mul]
  have e₁ : I.ev l.M a₁ = 1 := (hI a₁ h₁).symm.trans (e.symm.trans h)
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨b, rfl⟩ := (I.ker l.M hM a₁).1 e₁
  have hMm : (l.M : 𝓞 E) ∈ l.Mb := by
    have : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    have hle : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ l.Mb := Ideal.mul_le_left
    exact hle this
  refine Submodule.add_mem _ h₂ ?_
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hMm trivial

section Bridge

abbrev fib {X Y : Scheme.{0}} (G : Over X) (x : Y ⟶ X) : Over Y := (Over.pullback x).obj G

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

def pushAt {ρ : X ⟶ X} {F : G.left ⟶ G.left} (h : IsGrpPullback G G ρ F) (T : Over X) (c : T.left ⟶ X)
    (e : T.hom ≫ ρ = c) : (T ⟶ G) →* (Over.mk c ⟶ G) :=
  MonoidHom.mk' (fun u => Over.homMk (u.left ≫ F) (by
      subst e
      show (u.left ≫ F) ≫ G.hom = T.hom ≫ ρ
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w u])) (fun a b => by
    subst e
    exact Over.OverMorphism.ext (h.2 T a b _ _ rfl rfl).symm)

theorem one_left_congr {T : Scheme.{0}} {c c' : T ⟶ X} (h : c = c') :
    (1 : Over.mk c ⟶ G).left = (1 : Over.mk c' ⟶ G).left := by
  subst h; rfl

end Bridge

theorem sections_eq {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) [IsProper G.hom]
    {ρ ρ' : X ⟶ X} {F F' : G.left ⟶ G.left} (h : IsGrpPullback G G ρ F) (h' : IsGrpPullback G G ρ' F')
    {k : Type} [Field k] [CharZero k] (x : Sp k ⟶ X) (hx : x ≫ ρ = x ≫ ρ')
    (ht : ∀ w : overAt x (DualNumber k) ⟶ G, smT x 0 w = 1 → w.left ≫ F = w.left ≫ F')
    (s : Over.mk x ⟶ G) : s.left ≫ F = s.left ≫ F' := by
  have pA : IsGrpPullback (fib G x) G x (pullback.fst G.hom x) := isGrpPullback_pullback G x
  have pB : IsGrpPullback (fib G (x ≫ ρ)) G (x ≫ ρ) (pullback.fst G.hom (x ≫ ρ)) := isGrpPullback_pullback G (x ≫ ρ)
  have c₁ : IsGrpPullback (fib G x) G (x ≫ ρ) (pullback.fst G.hom x ≫ F) := IsGrpPullback.comp pA h
  have c₂ : IsGrpPullback (fib G x) G (x ≫ ρ) (pullback.fst G.hom x ≫ F') := hx ▸ IsGrpPullback.comp pA h'
  let f : fib G x ⟶ fib G (x ≫ ρ) := Over.homMk (pullback.lift (pullback.fst G.hom x ≫ F) (pullback.snd G.hom x) c₁.1.w) (pullback.lift_snd _ _ _)
  let f' : fib G x ⟶ fib G (x ≫ ρ) := Over.homMk (pullback.lift (pullback.fst G.hom x ≫ F') (pullback.snd G.hom x) c₂.1.w) (pullback.lift_snd _ _ _)
  have ef : f.left ≫ pullback.fst G.hom (x ≫ ρ) = pullback.fst G.hom x ≫ F := pullback.lift_fst _ _ _
  have ef' : f'.left ≫ pullback.fst G.hom (x ≫ ρ) = pullback.fst G.hom x ≫ F' := pullback.lift_fst _ _ _
  haveI : IsMonHom f := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₁ pB (𝟙 G) f (by simpa using ef)
  haveI : IsMonHom f' := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback c₂ pB (𝟙 G) f' (by simpa using ef')
  have hA : IsAbelianScheme (fib G x) := by
    haveI : IsProper (fib G x).hom := inferInstanceAs (IsProper (pullback.snd G.hom x))
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ (IsSemiAbelian.pullback x G hG)
  have hB : IsAbelianScheme (fib G (x ≫ ρ)) := by
    haveI : IsProper (fib G (x ≫ ρ)).hom := inferInstanceAs (IsProper (pullback.snd G.hom (x ≫ ρ)))
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ (IsSemiAbelian.pullback (x ≫ ρ) G hG)
  haveI : IsCommMonObj (fib G x) := hA.comm
  haveI : IsCommMonObj (fib G (x ≫ ρ)) := hB.comm
  have key : f = f' := by
    refine GlobalTheory.T.abelianScheme_hom_eq_of_tangent_eq k _ _ hA hB f f' fun v hv => ?_
    let w : overAt x (DualNumber k) ⟶ G := Over.homMk (v.left ≫ pullback.fst G.hom x) (by
      have e := Over.w v
      show (v.left ≫ pullback.fst G.hom x) ≫ G.hom = spMap (algebraMap k (DualNumber k)) ≫ x
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      have e' : v.left ≫ pullback.snd G.hom x = spMap (algebraMap k (DualNumber k)) ≫ 𝟙 (Sp k) := e
      rw [e', Category.comp_id])
    have hw : smT x 0 w = 1 := by
      apply Over.OverMorphism.ext
      have e₁ : (smT x 0 w).left = (smT (𝟙 (Sp k)) 0 v).left ≫ pullback.fst G.hom x := by
        simp only [smT_left, w, Over.homMk_left, Category.assoc]
      rw [e₁, hv]
      have e₂ := congrArg (fun z => z.left) (map_one (pushHom pA (overAt (𝟙 (Sp k)) (DualNumber k))))
      refine e₂.trans (one_left_congr ?_)
      simp
    have e := ht w hw
    apply Over.OverMorphism.ext
    refine pB.1.hom_ext ?_ ?_
    · simp only [Over.comp_left, Category.assoc]
      rw [ef, ef']
      simpa [w] using e
    · rw [Over.w, Over.w]
  let a : Over.mk (𝟙 (Sp k)) ⟶ fib G x := Over.homMk (pullback.lift s.left (𝟙 _) (by simpa using Over.w s)) (pullback.lift_snd _ _ _)
  have ea : a.left ≫ pullback.fst G.hom x = s.left := pullback.lift_fst _ _ _
  have e1 : a.left ≫ f.left ≫ pullback.fst G.hom (x ≫ ρ) = s.left ≫ F := by
    rw [ef, ← Category.assoc, ea]
  have e2 : a.left ≫ f'.left ≫ pullback.fst G.hom (x ≫ ρ) = s.left ≫ F' := by
    rw [ef', ← Category.assoc, ea]
  rw [← e1, ← e2, key]

theorem move_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La), IsLift lift → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y y' : FrPt Xo c k) (g g' : Gam Dw l), levR (lift g, LinearMap.id) y y' → levR (lift g', LinearMap.id) y y' → g = g' := by
  intro E _ _ _ H Dw l Xo c _ _ lift hl k _ _ _ y y' g g' h h'
  obtain ⟨ρ, ν, -, hm, hf⟩ := h
  obtain ⟨ρ', ν', -, hm', hf'⟩ := h'
  haveI : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  haveI : IsProper Xo.univ.t.G.hom := Xo.univ.proper
  have hx : y.x ≫ ρ = y.x ≫ ρ' := hf.1.symm.trans hf'.1
  have hu : ∀ τ i, y.u τ i ≫ ν.φ = y.u τ i ≫ ν'.φ := fun τ i => (hf.2.1 τ i).symm.trans (hf'.2.1 τ i)
  have ht : ∀ w : overAt y.x (DualNumber k) ⟶ Xo.univ.t.G, smT y.x 0 w = 1 → w.left ≫ ν.φ = w.left ≫ ν'.φ := by
    intro w hw
    have hT : IsTanAt y.x w.left := isTanAtG_of (t := Xo.univ.t) w hw
    obtain ⟨a, ⟨u, hu1, hu2⟩, -⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.FrTan.frTanBasis_holds Xo c k y w.left hT
    let P := pushAt ν.cart (overAt y.x (DualNumber k)) ((overAt y.x (DualNumber k)).hom ≫ ρ) rfl
    let P' := pushAt ν'.cart (overAt y.x (DualNumber k)) ((overAt y.x (DualNumber k)).hom ≫ ρ)
      (by simp only [Over.mk_hom, Category.assoc, hx])
    have e₁ : ∀ i, P (u i) = P' (u i) := fun i => by
      apply Over.OverMorphism.ext
      show (u i).left ≫ ν.φ = (u i).left ≫ ν'.φ
      rw [hu1, Category.assoc, Category.assoc, hu]
    have e₂ : P (List.ofFn u).prod = P' (List.ofFn u).prod := by
      rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      congr 2
      exact funext e₁
    have e₃ := congrArg (fun z => z.left) e₂
    have e₄ : ((List.ofFn u).prod).left ≫ ν.φ = ((List.ofFn u).prod).left ≫ ν'.φ := e₃
    rw [hu2] at e₄
    exact e₄
  have hs := sections_eq Xo.univ.t.semi ν.cart ν'.cart y.x hx ht
  have tl : (toUnit (Over.mk y.x)).left = y.x := by simpa using Over.w (toUnit (Over.mk y.x))
  have hη : ∀ a, toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a) = toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g' a) := by
    intro a
    have e₁ : (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a)).left ≫ ν.φ = y.x ≫ ρ ≫ (Xo.univ.eta a).left := by
      rw [Over.comp_left, tl, Category.assoc, ← hm.2.1 a]
    have e₂ : (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g' a)).left ≫ ν'.φ = y.x ≫ ρ' ≫ (Xo.univ.eta a).left := by
      rw [Over.comp_left, tl, Category.assoc, ← hm'.2.1 a]
    apply Over.OverMorphism.ext
    refine ν.cart.1.hom_ext ?_ ?_
    · rw [e₁, hs, e₂, ← Category.assoc, ← Category.assoc, hx]
    · rw [Over.w, Over.w]
  have hz : ∀ a, lift g a - lift g' a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := by
    intro a
    refine eta_injective Xo y.x ((algebraMap c.F k).comp (IntermediateField.inclusion c.le).toRingHom) y.x_over _ ?_
    have e : toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a) =
        (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g a - lift g' a)) * (toUnit (Over.mk y.x) ≫ Xo.univ.eta (lift g' a)) := by
      rw [← MonObj.comp_mul, ← Xo.univ.eta_add, sub_add_cancel]
    rw [hη a] at e
    exact (mul_eq_right.1 e.symm)
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have e₁ := LinearMap.congr_fun (hl g) a
  have e₂ := LinearMap.congr_fun (hl g') a
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe] at e₁ e₂
  rw [← e₁, ← e₂]
  exact (Submodule.Quotient.eq _).2 (hz a)

end GlobalTheory.LevelFree
end
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ZarGlue

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_pull {T Y : Over S} {N : LB (A ⊗ T).left} (hN : Fam A N) (y : Y ⟶ T) :
    Fam A (ev N (fst A Y) (snd A Y ≫ y)) := by
  have hL : (ev N (fst A Y) (snd A Y ≫ y)).IsLB := pull_isLB hN.isLB _
  refine ⟨hL, (isAdditive_iff hL).2 fun Z a a' t => ?_⟩
  rw [evc_ev hN.isLB _ _ hL, evc_ev hN.isLB _ _ hL, evc_ev hN.isLB _ _ hL]
  simp only [lift_fst, lift_snd_assoc]
  exact (isAdditive_iff hN.isLB).1 hN.add Z a a' (t ≫ y)


omit [GrpObj A] in
theorem hom_open_eq (V : S.Opens) {Y : Over S} (u u' : Y ⟶ Over.mk V.ι) : u = u' := by
  apply Over.OverMorphism.ext
  have h : u.left ≫ V.ι = u'.left ≫ V.ι := (Over.w u).trans (Over.w u').symm
  exact (cancel_mono V.ι).1 h


omit [GrpObj A] in
theorem exists_hom_open (V : S.Opens) (Y : Over S) (h : ∀ z, Y.hom z ∈ V) : Nonempty (Y ⟶ Over.mk V.ι) := by
  refine ⟨Over.homMk (IsOpenImmersion.lift V.ι Y.hom ?_) (IsOpenImmersion.lift_fac _ _ _)⟩
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact h z

theorem isChart_of_rep (V : S.Opens) {B : Over S} (b : B ⟶ Over.mk V.ι) {P : LB (A ⊗ B).left} (h : Rep A b P) :
    IsChart A P := by
  refine ⟨h.fam, ?_, ?_⟩
  · intro Y u u' hs
    have hA : (ev P (fst A Y) (snd A Y ≫ u)).IsLB := pull_isLB h.fam.isLB _
    have hB : (ev P (fst A Y) (snd A Y ≫ u')).IsLB := pull_isLB h.fam.isLB _
    obtain ⟨x, -, hx⟩ := h.univ Y (u ≫ b) _ (fam_pull h.fam u)
    rw [hx u ⟨rfl, LBIso.trans hA hB hA hs (LBIso.symm hs)⟩, hx u' ⟨hom_open_eq V _ _, hs⟩]
  · intro T N hN
    refine ⟨T.hom ⁻¹ᵁ V, fun Y y => ⟨?_, ?_⟩⟩
    · rintro ⟨u, -⟩ z
      have hb : b.left ≫ V.ι = B.hom := Over.w b
      have e : (u.left ≫ b.left) ≫ V.ι = y.left ≫ T.hom := by
        rw [Over.w y, Category.assoc, hb, Over.w u]
      have hmem : (y.left ≫ T.hom) z ∈ Set.range V.ι := ⟨(u.left ≫ b.left) z, by rw [← e]; rfl⟩
      rw [Scheme.Opens.range_ι] at hmem
      exact hmem
    · intro hz
      have hY : ∀ z, Y.hom z ∈ V := fun z => by
        rw [← Over.w y]
        exact hz z
      obtain ⟨t⟩ := exists_hom_open V Y hY
      obtain ⟨x, ⟨-, hx⟩, -⟩ := h.univ Y t _ (fam_pull hN y)
      exact ⟨x, hx⟩


omit [GrpObj A] in
theorem good_iso_comp {g : ℕ} {X X' Y : Scheme.{0}} (e : X' ⟶ X) [IsIso e] {f : X ⟶ Y}
    (h : GlobalTheory.DualCon.Good g f) : GlobalTheory.DualCon.Good g (e ≫ f) := ⟨MorphismProperty.RespectsIso.precomp @IsProper e f h.proper,
  by
    haveI := h.smooth
    have h0 : SmoothOfRelativeDimension (0 + g) (e ≫ f) := inferInstance
    rwa [zero_add] at h0,
  by
    haveI := h.conn
    have hsq : IsPullback e (e ≫ f) f (𝟙 Y) := IsPullback.of_horiz_isIso ⟨by simp⟩
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq h.conn⟩

theorem zariski_glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, HasRep A (g i) (Over.mk (V i).ι)) → ∃ (B : Over S) (P : LB (A ⊗ B).left), Rep A (toUnit B) P ∧ ∀ i, GlobalTheory.DualCon.Good (g i) (pullback.snd B.hom (V i).ι) := by
  intro S A _ hA Ix V g hcov hrep
  have hrep' : ∀ i, ∃ (B : Over S) (b : B ⟶ Over.mk (V i).ι) (P : LB (A ⊗ B).left),
      Rep A b P ∧ GlobalTheory.DualCon.Good (g i) b.left := hrep
  choose Bi bi Pi hRi hGi using hrep'
  obtain ⟨B, P, j, hR, -, -, -⟩ := GlobalTheory.T.glue_openCharts_additiveFamilies_representing S A hA Ix Bi Pi
    (fun i => isChart_of_rep (V i) (bi i) (hRi i)) (by
      intro K _ _ s N hN
      obtain ⟨i, hi⟩ := hcov (s (default : Sp K))
      have hs : ∀ z : Sp K, s z ∈ V i := fun z => by
        rw [Subsingleton.elim z default]
        exact hi
      obtain ⟨t⟩ := exists_hom_open (V i) (Over.mk s) hs
      obtain ⟨x, ⟨-, hx⟩, -⟩ := (hRi i).univ _ t N hN
      exact ⟨i, x, (same_id_iff hN.isLB (hRi i).fam.isLB x).2 hx⟩)
  refine ⟨B, P, hR, fun i => ?_⟩
  have hpb : IsPullback (fst B (Over.mk (V i).ι)) (snd B (Over.mk (V i).ι)) (toUnit B)
      (toUnit (Over.mk (V i).ι)) :=
    IsPullback.of_is_product' (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _)
      SemiCartesianMonoidalCategory.isTerminalTensorUnit
  have hR' := GlobalTheory.T.rep_ev_of_isPullback S A B (𝟙_ (Over S)) (Over.mk (V i).ι) (B ⊗ Over.mk (V i).ι) (toUnit B) P
    (toUnit _) (fst _ _) (snd _ _) hR hpb
  obtain ⟨e, he, -⟩ := GlobalTheory.T.representsAdditiveLineBundleFamilies_unique_iso S A _ _ _ (snd B (Over.mk (V i).ι)) _ (bi i) (Pi i) hR' (hRi i)
  haveI : IsIso e.hom.left := Functor.map_isIso (Over.forget _) e.hom
  have h2 := good_iso_comp e.hom.left (hGi i)
  rw [← Over.comp_left, he] at h2
  exact h2

end GlobalTheory.DualCon.ZarGlue
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSFloor

theorem coeff_le_of_bounded {E : Type} [Field E] {σ : Type} [Fintype σ] (k : MvPolynomial σ E)
    (s : E →+* ℂ) (B : ℝ) (hB : ∀ z : σ → ℂ, (∀ i, ‖z i‖ ≤ 1) → ‖eval₂ s z k‖ ≤ B) (m : σ →₀ ℕ) :
    ‖s (k.coeff m)‖ ≤ B := by

  obtain ⟨θ, hθ⟩ := (ReciprocityTheory.MultiplicativeHeights.Closed.torus_l2_cauchy_inequality σ (MvPolynomial.map s k)).2 m
  have hz : ∀ i, ‖ReciprocityTheory.MultiplicativeHeights.torusPoint θ i‖ ≤ 1 := by
    intro i
    simp [ReciprocityTheory.MultiplicativeHeights.torusPoint, Complex.norm_exp]
  rw [MvPolynomial.coeff_map, MvPolynomial.eval_map] at hθ
  exact hθ.trans (hB _ hz)

theorem floor : ∀ (E : Type) [Field E] [NumberField E] (σ : Type) [Fintype σ] (k : MvPolynomial σ E)
    (B : (E →+* ℂ) → ℝ), k ≠ 0 →
    (∀ (s : E →+* ℂ) (z : σ → ℂ), (∀ i, ‖z i‖ ≤ 1) → ‖eval₂ s z k‖ ≤ B s) →
    -mean E (fun s => Real.log (B s)) ≤ finPart k := by
  intro E _ _ σ _ k B hk hB
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hk
  refine le_trans (b := -mean E (fun s => Real.log ‖s (k.coeff m)‖)) ?_
    ((GlobalTheory.HSFinPart.finPart_props E σ σ).2.2 k m hm)
  rw [neg_le_neg_iff]
  unfold mean
  gcongr with τ _

  have hpos : 0 < ‖τ (k.coeff m)‖ := norm_pos_iff.mpr ((map_ne_zero τ).mpr hm)
  exact Real.log_le_log hpos (coeff_le_of_bounded k τ (B τ) (hB τ) m)

end GlobalTheory.HSFloor
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_primitive_deRham_class_torsion_character
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ) (hN : (p : R) ^ N = 0)
    (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A) (hP : AllPrim (dp0 R) (𝟙 _) A)
    (hs : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)))
    (G : PDivGroup p R) (t : G.TorsionTower A) (b : Fn0 A) (hb : IsTorsChar (p ^ N) b) :
    ∃ (c : primDR A) (d : Dat t c), ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      x ^ (p ^ N) = 1 → chi (p ^ N) d.g D x = b D x :=
  GlobalTheory.PtExt.exists_dat_chi_eq p R N hN A hA hP hs G t b hb
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_holomorphic_subAtlas_smooth_closedSubscheme : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (e : ℕ) (A : FinHolAtlas (e + 1) (CxPts p σ)), IsAlgAtlas A → SmoothOfRelativeDimension e q → ∃ B : FinHolAtlas e (Set.range (ptMap π hπ σ)), HoloMap B A Subtype.val ∧ ∀ (L : Fin e → MLine p σ) (v : CxPts p σ → ℝ), Continuous v → mInt B (fun i => (L i).φ.locPot.pullback Subtype.val continuous_subtype_val) (v ∘ Subtype.val) = Mix.int (fun i => (L i).pull π hπ) (fun y => v (ptMap π hπ σ y)) := by
  first | exact @GlobalTheory.Mix.exists_subAtlas | exact GlobalTheory.Mix.exists_subAtlas | (intros; apply GlobalTheory.Mix.exists_subAtlas <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSNef.PairFG

theorem exists_hom {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) (a b : ℤ)
    (M : HermLB p) (hM : P.Rep a b M) :
    ∃ φ : M.B.Sec →+ X.functionField, φ.range = P.H a b := by
  obtain ⟨ρ, hρ, hu, -⟩ := hM
  obtain ⟨e, he⟩ := RepDict.exists_quot M.isLB hρ
  have hcov {B : LB X} (hB : B.IsLB) (x : X) : ∃ c, x ∈ B.U c :=
    Opens.mem_iSup.1 (hB.cover.ge (Opens.mem_top _))
  obtain ⟨c₀, h₀⟩ := hcov M.isLB (genericPoint X)
  have hρ₀ := (ρ c₀).ne_zero
  let φ : M.B.Sec →+ X.functionField :=
    { toFun := e
      map_zero' := by
        refine mul_right_cancel₀ hρ₀ ?_
        rw [he 0 c₀ h₀, zero_mul]
        exact map_zero _
      map_add' := fun u v => by
        refine mul_right_cancel₀ hρ₀ ?_
        rw [he (u + v) c₀ h₀, add_mul, he u c₀ h₀, he v c₀ h₀]
        exact map_add _ _ _ }
  have hl (f : X.functionField) c i j :
      P.loc a b f i j * ((ρ c : X.functionField) / P.loc a b 1 i j) = f * ρ c := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    simp only [Pair.loc]
    field_simp
  have hl' (f : X.functionField) c i j :
      P.loc a b f i j = f * ρ c * ((ρ c : X.functionField) / P.loc a b 1 i j)⁻¹ := by
    have := (P.r i).ne_zero
    have := (P.r' j).ne_zero
    have := (ρ c).ne_zero
    simp only [Pair.loc]
    field_simp
  refine ⟨φ, le_antisymm ?_ fun f hf => ?_⟩
  · rintro _ ⟨u, rfl⟩ x i j hi hj
    obtain ⟨c, hc⟩ := hcov M.isLB x
    change RegAt x (P.loc a b (e u) i j)
    rw [hl' _ c, he u c (gen_mem hc)]
    exact (regAt_fnOf hc _ _).mul (hu x c i j hc hi hj).inv.regAt
  · obtain ⟨u, hu'⟩ := RepDict.exists_sec hρ (f := f) fun c x hc => by
      obtain ⟨i, hi⟩ := hcov P.L.isLB x
      obtain ⟨j, hj⟩ := hcov P.A.isLB x
      rw [← hl f c i j]
      exact (hf x i j hi hj).mul (hu x c i j hc hi hj).regAt
    exact ⟨u, mul_right_cancel₀ hρ₀ ((he u c₀ h₀).trans (hu' c₀ h₀))⟩

theorem h_fg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (a b : ℤ), (P.H a b).FG := by
  intro k _ X _ p D hX P a b
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_hermitianRepresentative_integerCombination k X p P a b
  obtain ⟨φ, hφ⟩ := exists_hom P a b M hM
  have := GlobalTheory.T.addGroupFG_lineBundleSections_arithmeticVariety k X p D hX M.B M.isLB
  rw [← hφ, AddMonoidHom.range_eq_map]
  obtain ⟨S, hS, hfin⟩ := AddGroup.fg_iff.mp this
  apply (AddSubgroup.fg_iff _).mpr
  refine ⟨(φ : M.B.Sec → X.functionField) '' S, ?_, hfin.image φ⟩
  rw [← AddMonoidHom.map_closure, hS]

end GlobalTheory.HSNef.PairFG
end
end
