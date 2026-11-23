module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

set_option autoImplicit false
noncomputable section
open GlobalTheory.Vanishing.H0 GlobalTheory.CompHS

namespace GlobalTheory.HSApp

theorem modif_generic_map {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) [IrreducibleSpace M.X] (η : Y) (hη : η ∈ U) (hg : IsGenericPoint η Set.univ) :
    genericPoint M.X ∈ M.opn ∧ M.σ (genericPoint M.X) = η := by
  have := M.iso
  have hne : (M.opn : Set M.X).Nonempty := M.dense.nonempty
  have hm : genericPoint M.X ∈ M.opn :=
    ((genericPoint_spec M.X).mem_open_set_iff M.opn.isOpen).2 (by simpa using hne)
  refine ⟨hm, ?_⟩
  obtain ⟨x, hx⟩ := (M.σ ∣_ U).surjective ⟨η, hη⟩
  have hx' : M.σ x.1 = η := (morphismRestrict_base_coe M.σ U x).symm.trans (congrArg Subtype.val hx)
  have hcl : η ∈ closure {M.σ (genericPoint M.X)} := by
    rw [← hx', ← Set.image_singleton]
    exact image_closure_subset_closure_image M.σ.continuous
      ⟨x.1, by rw [(genericPoint_spec M.X).def]; trivial, rfl⟩
  have hgen : IsGenericPoint (M.σ (genericPoint M.X)) Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hg.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hcl) isClosed_closure
  exact hgen.eq hg

theorem modif_residueFieldMap_surjective {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {U : Y.Opens} {D : ℕ}
    (M : Modif p U D) (z : M.X) (hz : z ∈ M.opn) : Function.Surjective (M.σ.residueFieldMap z).hom := by
  have := M.iso
  have : IsIso (M.σ.stalkMap z) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap M.σ U ⟨z, hz⟩)).1
      (((isIso_iff_isIso_stalkMap (M.σ ∣_ U)).1 M.iso).2 ⟨z, hz⟩)
  have hst : Function.Surjective (M.σ.stalkMap z).hom := (ConcreteCategory.bijective_of_isIso _).2
  intro y
  obtain ⟨a, rfl⟩ := M.X.residue_surjective z y
  obtain ⟨b, rfl⟩ := hst a
  exact ⟨Y.residue _ b, congr($(Scheme.residue_residueFieldMap M.σ z).hom b)⟩

theorem modif_residueFieldMap_germ {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {U : Y.Opens} {D : ℕ}
    {B : LB Y} {hB : B.IsLB} {W : Submodule F (H0 p B ⊤)} (M : Modif p U D)
    (Δ : Cartier ((baseIdeal hB W).comap M.σ)) {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : (F →+* ℂ) → V → ℝ} {Lt : Submodule (𝓞 F) V} (φ : V ≃ₗ[F] W) (f : LatFrame Nm Lt) (abelian₂ : ℝ)
    (hnb : NoBase hB W U) (z : M.X) (hz : z ∈ M.opn) (i : B.ι) (hi : M.σ z ∈ B.U i) :
    ∃ c : M.X.residueField z, c ≠ 0 ∧ ∀ w : W,
      (M.σ.residueFieldMap z).hom ((Y.residue (M.σ z)).hom (germ i (M.σ z) (memTop _) hi w.1)) =
        c * (M.sys Δ φ f abelian₂).toLinSys.val (Adelic.resPt z) (toSec (Δ.lift w)) := by
  set S := (M.sys Δ φ f abelian₂).toLinSys
  have hp : Adelic.ptOf (Adelic.resPt z) = z := Adelic.ptOf_resPt z
  have hj : z ∈ Δ.moving.U (S.chartAt (Adelic.ptOf (Adelic.resPt z))) :=
    (congrArg (fun y => y ∈ Δ.moving.U (S.chartAt (Adelic.ptOf (Adelic.resPt z)))) hp).mp
      (S.mem_chartAt (Adelic.ptOf (Adelic.resPt z)))
  set j := S.chartAt (Adelic.ptOf (Adelic.resPt z))
  have hi0 : M.σ z ∈ B.U (j.1 PUnit.unit) := mem_pull.1 hj.1
  have hu : IsUnit (ger z hj.2 (Δ.t.f j.2)) :=
    (isUnit_ger_iff _ hj.2).2 ((Δ.mem_nonzeroLocus z).2 (M.notMem_support hnb z (M.off_eq.ge hz)))
  refine ⟨(M.σ.residueFieldMap z).hom ((Y.residue (M.σ z)).hom (tr B (M.σ z) i (j.1 PUnit.unit)).val) *
    (M.X.residue z).hom (ger z hj.2 (Δ.t.f j.2)), mul_ne_zero ?_ ?_, fun w => ?_⟩
  · exact (map_ne_zero _).2 (((tr B (M.σ z) i (j.1 PUnit.unit)).isUnit.map (Y.residue (M.σ z)).hom).ne_zero)
  · exact (hu.map (M.X.residue z).hom).ne_zero
  have hv : S.val (Adelic.resPt z) (toSec (Δ.lift w)) = (M.X.residue z).hom (germ j z (memTop z) hj (Δ.lift w)) := by
    rw [Adelic.LinSys.val, Adelic.projSys.valR_resPt z _ hj, ← ger_toSec]
    rfl
  rw [hv, germ_change i (j.1 PUnit.unit) (M.σ z) (memTop _) hi hi0, map_mul, map_mul, mul_assoc]
  congr 1
  rw [← map_mul (M.X.residue z).hom, Δ.germ_lift w j z hj]
  refine Eq.trans ?_ (congrArg (M.X.residue z).hom
    (GlobalTheory.Vanishing.H0.germ_pull (p := p) M.σ le_top j.1 z (memTop z) hj.1 w.1)).symm
  exact congr($(Scheme.residue_residueFieldMap M.σ z).hom _)

theorem sys_birational_of_ratField {F : Type} [Field F] [NumberField F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {U : Y.Opens} {D : ℕ}
    {B : LB Y} {hB : B.IsLB} {W : Submodule F (H0 p B ⊤)} (M : Modif p U D)
    (Δ : Cartier ((baseIdeal hB W).comap M.σ)) {V : Type} [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : (F →+* ℂ) → V → ℝ} {Lt : Submodule (𝓞 F) V} (φ : V ≃ₗ[F] W) (f : LatFrame Nm Lt) (abelian₂ : ℝ)
    [IsIntegral M.X] (hnb : NoBase hB W U) (η : Y) (hη : η ∈ U) (hg : IsGenericPoint η Set.univ)
    (hr : ratField (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) η hη = ⊤) :
    (M.sys Δ φ f abelian₂).toLinSys.Birational := by
  classical
  obtain ⟨hmem, hσ⟩ := modif_generic_map M η hη hg
  subst hσ
  set S := (M.sys Δ φ f abelian₂).toLinSys with hS
  set z := genericPoint M.X with hz
  have hsurj := modif_residueFieldMap_surjective M z hmem
  have hbpf : S.BasePointFree := Δ.iSup_nonzeroLocus (f.b.map φ).span_eq
  obtain ⟨j0, hj0⟩ := Function.ne_iff.1 (hbpf.coords_ne_zero (Adelic.resPt z))
  have key : ∀ w : W, S.val (Adelic.resPt z) (toSec (Δ.lift w)) / S.coords (Adelic.resPt z) j0 ∈
      S.ratioField (Adelic.resPt z) := fun w => by
    set u := f.b.equivFun (φ.symm w)
    have e : toSec (Δ.lift w) = S.comb u := by
      refine (bijective_ofSec_top (p := M.str)).1 ?_
      rw [ofSec_toSec]
      refine Eq.trans ?_ (M.ofSec_comb Δ φ f abelian₂ u).symm
      simp [u]
    rw [e, S.val_comb, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (Subfield.subset_closure (Or.inl ⟨_, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨j, j0, rfl⟩))
  have hgen : ∀ r ∈ {r | ∃ (i : B.ι) (hi : M.σ z ∈ B.U i) (s s' : H0 p B U),
      s ∈ (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) ∧
      s' ∈ (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) ∧
      r = (Y.residue (M.σ z)).hom (germ i (M.σ z) hη hi s) / (Y.residue (M.σ z)).hom (germ i (M.σ z) hη hi s')},
      (M.σ.residueFieldMap z).hom r ∈ S.ratioField (Adelic.resPt z) := by
    rintro r ⟨i, hi, _, _, ⟨w, rfl⟩, ⟨w', rfl⟩, rfl⟩
    obtain ⟨c, hc, hcw⟩ := modif_residueFieldMap_germ M Δ φ f abelian₂ hnb z hmem i hi
    rw [germ_restr, germ_restr, map_div₀, hcw, hcw, mul_div_mul_left _ _ hc,
      ← div_div_div_cancel_right₀ hj0]
    exact div_mem (key w) (key w')
  have hle : ratField (Set.range fun w : W => (restr le_top w.1 : H0 p B U)) (M.σ z) hη ≤
      (S.ratioField (Adelic.resPt z)).comap (M.σ.residueFieldMap z).hom :=
    Subfield.closure_le.2 hgen
  refine ⟨z, genericPoint_spec M.X, eq_top_iff.2 fun x _ => ?_⟩
  obtain ⟨y, rfl⟩ := hsurj x
  exact hle (hr.symm ▸ Subfield.mem_top y)

theorem geo_second_birational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), RatGen X Z U P.u₂ → (h.geo f₁ f₂ th k).second.Birational := by
  intro E _ _ _ H Dw l Xo c Y X Z r U P R ω x D V dict h f₁ f₂ th k hR
  obtain ⟨η, hη, hgen, hrat⟩ := hR
  have : IsIntegral R.X := (h.geo f₁ f₂ th k).isIntegral
  refine sys_birational_of_ratField R.toModif R.Δ₂ h.ext₂.equiv f₂ k.abelian₂ h.free₂ η hη hgen ?_
  convert hrat using 2
  ext s
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨h.ext₂.equiv.symm w, by rw [← h.ext₂.restr_equiv, LinearEquiv.apply_symm_apply]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨h.ext₂.equiv g, h.ext₂.restr_equiv g⟩

end GlobalTheory.HSApp
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogCanonicalReflexive

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}

theorem fun_ext_ger_of_dense [IsReduced Y] {O W : Y.Opens} (hO : Dense (O : Set Y)) {a b : Γ(Y, W)}
    (h : ∀ z (hz : z ∈ W), z ∈ O → ger z hz a = ger z hz b) : a = b := by
  refine sub_eq_zero.1 (eq_zero_of_basicOpen_eq_bot _ ?_)
  by_contra hne
  obtain ⟨z, hz, hzO⟩ := hO.inter_open_nonempty (Y.basicOpen (a - b)) (Y.basicOpen (a - b)).isOpen
    ((Opens.ne_bot_iff_nonempty _).1 hne)
  have hzW : z ∈ W := Y.basicOpen_le _ hz
  have hu : IsUnit (ger z hzW (a - b)) := (Y.mem_basicOpen _ z hzW).1 hz
  rw [map_sub, h z hzW hzO, sub_self] at hu
  exact not_isUnit_zero hu

theorem exists_extend_of_dense [IsReduced Y] {O : Y.Opens} (hO : Dense (O : Set Y)) {N : LB Y} (hN : N.IsLB)
    (f : H0 p N O) (h : ∀ y, ∃ (W : Y.Opens) (_ : y ∈ W) (i : N.ι) (hi : W ≤ N.U i) (w : Γ(Y, W)),
      ∀ z (hz : z ∈ W) (ho : z ∈ O), ger z hz w = H0.germ i z ho (hi hz) f) :
    ∃ G : H0 p N ⊤, H0.restr le_top G = f := by
  choose W hW c hc w hw using h
  obtain ⟨G, hG⟩ := H0.exists_of_germs (p := p) (O := ⊤) hN W c (fun _ => le_top) hc
    (fun y _ => ⟨y, hW y⟩) w fun y t t' hy hy' => by
      have e : resG Y (inf_le_left : W t ⊓ W t' ≤ W t) (w t) =
          resG Y (inf_le_inf (hc t) (hc t')) (N.g (c t) (c t')).val *
            resG Y (inf_le_right : W t ⊓ W t' ≤ W t') (w t') :=
        fun_ext_ger_of_dense hO fun z hz ho => by
          rw [map_mul, ger_resG, ger_resG, ger_resG, hw t z hz.1 ho, hw t' z hz.2 ho,
            H0.germ_change (c t) (c t') z ho _ (hc t' hz.2), val_tr N z (memInf (hc t hz.1) (hc t' hz.2))]
      have e' := congrArg (ger y (memInf hy hy')) e
      rw [map_mul, ger_resG, ger_resG, ger_resG] at e'
      rw [val_tr N y (memInf (hc t hy) (hc t' hy'))]
      exact e'
  refine ⟨G, H0.ext_germ fun y hy => ⟨c y, hc y (hW y), ?_⟩⟩
  rw [H0.germ_restr, ← hw y y (hW y) hy]
  exact hG y y (hW y)

theorem exists_extend_mul_of_simplePole : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} [IsReduced Y] {O : Y.Opens}, Dense (O : Set Y) → ∀ {P B N : LB Y} (C : ProdChart P B N) (ω : H0 p P O), GlobalTheory.LogCanonicalReflexive.SimplePoleAlong O C ω → ∀ g : H0 p B ⊤, (∀ y, y ∉ O → ∀ i hi, H0.germ i y (memTop y) hi g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) → ∃ G : H0 p N ⊤, H0.restr le_top G = C.mul ω (H0.restr le_top g) := by
  intro k _ Y p _ O hO P B N C ω hω g hg
  refine exists_extend_of_dense hO C.isLB₃ _ fun y => ?_
  by_cases hy : y ∈ O
  · obtain ⟨t, -, -, hc⟩ := C.cover y
    exact ⟨O ⊓ N.U (C.c t), ⟨hy, hc⟩, C.c t, inf_le_right, H0.loc _ _, fun z hz ho => rfl⟩
  obtain ⟨V, hyV, τ, ha, hb, hc, t, u, -, -, hdiv, htu⟩ := hω y hy
  let gl : Γ(Y, V) := resG Y (le_inf le_top hb) (g.loc (C.b τ))
  have hgl (z) (hz : z ∈ V) : ger z hz gl = H0.germ (C.b τ) z (memTop z) (hb hz) g := ger_resG _ _ _ _
  clear_value gl
  obtain ⟨h, hh⟩ := hdiv V le_rfl gl (fun z hz ho => hgl z hz ▸ hg z ho _ _) y hyV
  obtain ⟨W₁, hy₁, h₁, rfl⟩ := Y.presheaf.exists_germ_eq h
  have e : ger y (memInf hyV hy₁) (resG Y inf_le_left gl) =
      ger y (memInf hyV hy₁) (resG Y inf_le_left t * resG Y inf_le_right h₁) := by
    rw [map_mul, ger_resG, ger_resG, ger_resG]
    exact hh
  obtain ⟨W, hyW, i₁, i₂, e'⟩ := Y.presheaf.germ_eq y _ _ _ _ e
  have hWV : W ≤ V := i₁.le.trans inf_le_left
  have hW₁ : W ≤ W₁ := i₁.le.trans inf_le_right
  refine ⟨W, hyW, C.c τ, hWV.trans hc, resG Y hWV u * resG Y hW₁ h₁, fun z hz ho => ?_⟩
  have e₂ : ger z hz (resG Y i₁.le (resG Y inf_le_left gl)) =
      ger z hz (resG Y i₂.le (resG Y inf_le_left t * resG Y inf_le_right h₁)) := congrArg (ger z hz) e'
  rw [ger_resG, ger_resG, ger_resG, map_mul, ger_resG, ger_resG, hgl] at e₂
  rw [C.germ_mul _ _ τ z ho (ha (hWV hz)) (hb (hWV hz)), H0.germ_restr, map_mul, ger_resG, ger_resG,
    ← htu z (hWV hz) ho]
  refine Eq.trans ?_ (congrArg (_ * ·) e₂.symm)
  ring

end GlobalTheory.LogCanonicalReflexive
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogCanonicalReflexive

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}

theorem fun_eq_of_dense [IsReduced Y] {O : Y.Opens} (hd : Dense (O : Set Y)) {W : Y.Opens} {a b : Γ(Y, W)}
    (h : ∀ z (hz : z ∈ W), z ∈ O → ger z hz a = ger z hz b) : a = b := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot (a - b) ?_
  by_contra hne
  obtain ⟨z, hz', hz⟩ := hd.inter_open_nonempty _ (Y.basicOpen (a - b)).isOpen
    (Set.nonempty_iff_ne_empty.2 fun e => hne (Opens.ext e))
  have hm := Y.basicOpen_le _ hz'
  have hu : IsUnit (ger z hm (a - b)) := (Y.mem_basicOpen _ z hm).1 hz'
  rw [map_sub, h z hm hz, sub_self] at hu
  exact not_isUnit_zero hu

theorem glue_of_dense [IsReduced Y] {O : Y.Opens} (hd : Dense (O : Set Y)) {B : LB Y} (hB : B.IsLB)
    {ι : Type} (V : ι → Y.Opens) (c : ι → B.ι) (hc : ∀ s, V s ≤ B.U (c s)) (cover : ∀ y, ∃ s, y ∈ V s)
    (u : ∀ s, Γ(Y, V s)) (f : H0 p B O)
    (hu : ∀ s z (h : z ∈ V s) (hz : z ∈ O), ger z h (u s) = H0.germ (c s) z hz (hc s h) f) :
    ∃ g : H0 p B ⊤, (∀ s z (h : z ∈ V s), H0.germ (c s) z (memTop z) (hc s h) g = ger z h (u s)) ∧
      H0.restr le_top g = f := by
  obtain ⟨g, hg⟩ := H0.exists_of_germs (p := p) (O := ⊤) hB V c (fun _ => le_top) hc (fun y _ => cover y) u
    fun z s s' h h' => by
      have hW : V s ⊓ V s' ≤ B.U (c s) ⊓ B.U (c s') := fun x hx => ⟨hc s hx.1, hc s' hx.2⟩
      have e : resG Y (inf_le_left : V s ⊓ V s' ≤ V s) (u s) =
          resG Y hW (B.g (c s) (c s')).val * resG Y (inf_le_right : V s ⊓ V s' ≤ V s') (u s') :=
        fun_eq_of_dense hd fun x hx hxO => by
          rw [map_mul, ger_resG, ger_resG, ger_resG, hu s x _ hxO, hu s' x _ hxO, ← val_tr B x (hW hx)]
          exact H0.germ_change _ _ x hxO _ _ f
      have e' := congrArg (ger z (show z ∈ V s ⊓ V s' from ⟨h, h'⟩)) e
      rwa [map_mul, ger_resG, ger_resG, ger_resG, ← val_tr B z (hW ⟨h, h'⟩)] at e'
  refine ⟨g, fun s z h => hg s z h, H0.ext_germ fun y hy => ?_⟩
  obtain ⟨s, hs⟩ := cover y
  exact ⟨c s, hc s hs, by rw [H0.germ_restr, hg s y hs, hu s y hs hy]⟩

theorem extends_vanishing_of_mul [IsReduced Y] {O : Y.Opens} (hd : Dense (O : Set Y)) {P B N : LB Y}
    (C : ProdChart P B N) (ω : H0 p P O) (hω : SimplePoleAlong O C ω) (G : H0 p N ⊤) (f : H0 p B O)
    (hG : H0.restr le_top G = C.mul ω f) :
    ∃ g : H0 p B ⊤, (∀ y, y ∉ O → ∀ i hi,
      H0.germ i y (memTop y) hi g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) ∧ H0.restr le_top g = f := by
  choose V hyV τ ha hb hc t u ht hu _ htu using hω
  have hU (y : Y) (hy : y ∉ O) : IsUnit (u y hy) :=
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z hz => hu y hy z hz
  let w (y : Y) (hy : y ∉ O) : Γ(Y, V y hy) :=
    t y hy * (hU y hy).unit⁻¹.val *
      resG Y (le_inf le_top (hc y hy) : V y hy ≤ ⊤ ⊓ N.U (C.c (τ y hy))) (G.loc (C.c (τ y hy)))
  have hw (y : Y) (hy : y ∉ O) (z : Y) (hz : z ∈ V y hy) : ger z hz (w y hy) =
      ger z hz (t y hy) * ger z hz (hU y hy).unit⁻¹.val * H0.germ (C.c (τ y hy)) z (memTop z) (hc y hy hz) G := by
    simp only [w, map_mul, ger_resG]
    rfl
  let VV : C.τ ⊕ {y : Y // y ∉ O} → Y.Opens := fun s => match s with
    | .inl i => O ⊓ B.U (C.b i)
    | .inr y => V y.1 y.2
  let cc : C.τ ⊕ {y : Y // y ∉ O} → B.ι := fun s => match s with
    | .inl i => C.b i
    | .inr y => C.b (τ y.1 y.2)
  have hcc : ∀ s, VV s ≤ B.U (cc s) := fun s => match s with
    | .inl _ => inf_le_right
    | .inr y => hb y.1 y.2
  let uu : ∀ s, Γ(Y, VV s) := fun s => match s with
    | .inl i => f.loc (C.b i)
    | .inr y => w y.1 y.2
  have cover : ∀ y, ∃ s, y ∈ VV s := fun y => by
    by_cases hy : y ∈ O
    · obtain ⟨i, -, hi, -⟩ := C.cover y
      exact ⟨.inl i, hy, hi⟩
    · exact ⟨.inr ⟨y, hy⟩, hyV y hy⟩
  have huu : ∀ s z (h : z ∈ VV s) (hz : z ∈ O), ger z h (uu s) = H0.germ (cc s) z hz (hcc s h) f := by
    rintro (i | ⟨y, hy⟩) z h hz
    · rfl
    · change ger z h (w y hy) = H0.germ (C.b (τ y hy)) z hz (hb y hy h) f
      have e2 : ger z h (u y hy) * ger z h (hU y hy).unit⁻¹.val = 1 := by
        rw [← map_mul, IsUnit.mul_val_inv, map_one]
      have e1 := htu y hy z h hz
      rw [hw, ← H0.germ_restr le_top _ z hz, hG, C.germ_mul ω f (τ y hy) z hz (ha y hy h) (hb y hy h)]
      linear_combination (ger z h (hU y hy).unit⁻¹.val * H0.germ (C.b (τ y hy)) z hz (hb y hy h) f) * e1 +
        H0.germ (C.b (τ y hy)) z hz (hb y hy h) f * e2
  obtain ⟨g, hg, hgf⟩ := glue_of_dense hd C.isLB₂ VV cc hcc cover uu f huu
  refine ⟨g, fun y hy i hi => ?_, hgf⟩
  have e : H0.germ (C.b (τ y hy)) y (memTop y) (hb y hy (hyV y hy)) g = ger y (hyV y hy) (w y hy) :=
    hg (.inr ⟨y, hy⟩) y (hyV y hy)
  rw [H0.germ_change i (C.b (τ y hy)) y (memTop y) hi (hb y hy (hyV y hy)), e, hw, mul_assoc]
  refine Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ ?_)
  exact (IsLocalRing.mem_maximalIdeal _).2 fun hu' => hy ((ht y hy y (hyV y hy)).1 hu')

end GlobalTheory.LogCanonicalReflexive
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefStep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


open Classical in
def stepEx (σ : E →+* ℂ) (j : ℕ) : Ix Dw → ℤ :=
  fun ix => ix.elim 0 fun p => if p.1 = σ ∧ (p.2 : ℕ) < j then 1 else 0


open Classical in
theorem exOf_tailWt (τ : Psi H) (k : ℕ) (hk : Dw.p ≤ k) :
    AllWt.exOf Dw (GlobalTheory.NefWt.tailWt τ k) 0 = stepEx (conjEmb τ.1) (Dw.p + Dw.q - 1 - k) := by
  refine FlagMod.exOf_ext rfl (fun τ' i hi => ?_) (fun τ' i hi => ?_)
  · have h1 : ¬ (τ' = τ ∧ k < (i : ℕ)) := fun h => by
      have := i.2; have := FlagMod.mult_of_mem (Dw := Dw) τ'; omega
    have h2 : ¬ (τ'.1 = conjEmb τ.1 ∧ (i : ℕ) < Dw.p + Dw.q - 1 - k) := fun h =>
      GlobalTheory.AllWt.conj_not_mem τ (h.1 ▸ τ'.2)
    simp only [GlobalTheory.NefWt.tailWt, stepEx, Option.elim, if_neg h1, if_neg h2]
  · have hq := FlagMod.mult_conj (Dw := Dw) τ'
    have hi' := i.2
    by_cases e : τ' = τ
    · subst e
      have : k < Dw.p + (Dw.q - 1 - (i : ℕ)) ↔ (i : ℕ) < Dw.p + Dw.q - 1 - k := by omega
      by_cases h : (i : ℕ) < Dw.p + Dw.q - 1 - k
      · simp [GlobalTheory.NefWt.tailWt, stepEx, h, this.2 h]
      · simp [GlobalTheory.NefWt.tailWt, stepEx, h, mt this.1 h]
    · have hc : conjEmb τ'.1 ≠ conjEmb τ.1 := fun h => e (Subtype.ext (by
        rw [← GlobalTheory.AllWt.conjEmb_conjEmb τ'.1, h, GlobalTheory.AllWt.conjEmb_conjEmb]))
      simp [GlobalTheory.NefWt.tailWt, stepEx, e, hc]


open Classical in
theorem exOf_headWt (τ : Psi H) (k : ℕ) (hk : k < Dw.p) :
    AllWt.exOf Dw (GlobalTheory.NefWt.headWt τ k) 0 = stepEx τ.1 (k + 1) := by
  refine FlagMod.exOf_ext rfl (fun τ' i hi => ?_) (fun τ' i hi => ?_)
  · by_cases e : τ' = τ
    · subst e
      by_cases h : (i : ℕ) ≤ k
      · simp [GlobalTheory.NefWt.headWt, stepEx, h, Nat.lt_succ_of_le h]
      · simp [GlobalTheory.NefWt.headWt, stepEx, h, show ¬ (i : ℕ) < k + 1 by omega]
    · have hc : τ'.1 ≠ τ.1 := fun h => e (Subtype.ext h)
      simp [GlobalTheory.NefWt.headWt, stepEx, e, hc]
  · have hq := FlagMod.mult_conj (Dw := Dw) τ'
    have h1 : ¬ (τ' = τ ∧ Dw.p + (Dw.q - 1 - (i : ℕ)) ≤ k) := fun h => by omega
    have h2 : ¬ (conjEmb τ'.1 = τ.1 ∧ (i : ℕ) < k + 1) := fun h =>
      GlobalTheory.AllWt.conj_not_mem τ' (h.1 ▸ τ.2)
    simp only [GlobalTheory.NefWt.headWt, stepEx, Option.elim, if_neg h1, if_neg h2, neg_zero]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagMod.FlagCover Y)
  (Z : Comp Xo c)

theorem L₀_tailWt (τ : Psi H) (k : ℕ) (hk : Dw.p ≤ k) :
    L₀ X Z (GlobalTheory.NefWt.tailWt τ k) = LL₀ X Z (stepEx (conjEmb τ.1) (Dw.p + Dw.q - 1 - k)) :=
  congrArg (LL₀ X Z) (exOf_tailWt τ k hk)

theorem L₀_headWt (τ : Psi H) (k : ℕ) (hk : k < Dw.p) :
    L₀ X Z (GlobalTheory.NefWt.headWt τ k) = LL₀ X Z (stepEx τ.1 (k + 1)) :=
  congrArg (LL₀ X Z) (exOf_headWt τ k hk)

end GlobalTheory.NefStep
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def stalkAlg (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) : c.F →+* (X₀ TF.Y Z).presheaf.stalk x :=
  ((X₀ TF.Y Z).presheaf.germ ⊤ x trivial).hom.comp (algX (s₀ TF.Y Z) ⊤)

def stalkHom (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).presheaf.stalk x :=
  ((X₀ TF.Y Z).presheaf.germ ((barComp TF.Y Z).ι ⁻¹ᵁ U.1) x hx).hom.comp ((barComp TF.Y Z).ι.app U.1).hom

theorem algebraMap_comp_stalkAlg (TF : TorFlag Xo c) (Z : Comp Xo c) [IsIntegral (X₀ TF.Y Z)] (x : X₀ TF.Y Z) :
    (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField).comp (stalkAlg TF Z x) =
      GlobalTheory.Cartier.constFn (s₀ TF.Y Z) :=
  RingHom.ext fun a => GlobalTheory.Cartier.algebraMap_germ (U := ⊤) trivial _

end GlobalTheory.LogKSDiv
end
end
