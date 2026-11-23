module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPointMemTensorLatticeIffIntegralCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2152
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle227
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.inertPoint_mem_tensorLattice_iff_integral_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F))
    (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (A : GL (Fin n) (w.adicCompletion E)) (Bm : GL (Fin d) (w.adicCompletion E)),
    IsFrameAt w X.L A → IsFrameAt w Y.L Bm → ∀ x,
      (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion E)) ↔
        kap hw h (A : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Bm : Matrix (Fin d) (Fin d) (w.adicCompletion E)) x ∈ latAtV X Y v := by
  first | exact @GlobalTheory.InertLat.kap_mem_latAtV_iff | exact GlobalTheory.InertLat.kap_mem_latAtV_iff | (intros; apply GlobalTheory.InertLat.kap_mem_latAtV_iff <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj toProj_str toProj_preimage_chart O1 coord coord_f chart pullRatio secRatio_on
  pullRatio_toProj_on appLE_resG appLE_appLE appLE_of_eq)

theorem lin_f {R : Type} [CommRing R] {m N : ℕ} (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R) (j : Fin (m + 1))
    (i : Fin (N + 1)) :
    (lin a j).f i = ∑ n, GlobalTheory.AbLaw.cst (PSpace.str R N) (chart R N i) (a j n) * GlobalTheory.ProjSpace.ratio R N i n := by
  refine (GlobalTheory.LinChange.sum_f (H := O1 R N) _ i).trans (Finset.sum_congr rfl fun n _ => ?_)
  refine (GlobalTheory.LB.smul_f (L := O1 R N) _ _ i).trans ?_
  rw [GlobalTheory.LinChange.resG_cst]
  exact congrArg (_ * ·) (coord_f R N n i)

end GlobalTheory.SpanVA

theorem GlobalTheory.SpanVA.toProj_eq_liftDom_proj : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (hs : ⨆ i, nonzeroLocus (s i) = ⊤) (ht : ⨆ j, nonzeroLocus (t j) = ⊤) (hst : ∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) (h : GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.SpanVA.dom a = ⊤), GlobalTheory.ProjSpace.toProj f s hs = GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ≫ GlobalTheory.SpanVA.proj a := by
  intro R _ X f H m N s t a _ hs ht hst h
  have hg : GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ≫ (GlobalTheory.SpanVA.dom a).ι ≫ PSpace.str R N = f := by
    rw [← Category.assoc, GlobalTheory.SpanVA.liftDom_fac, GlobalTheory.ProjSpace.toProj_str]
  have e := GlobalTheory.ProjSpace.toProj_eq_comp_of_locally (f := (GlobalTheory.SpanVA.dom a).ι ≫ PSpace.str R N)
    (GlobalTheory.SpanVA.iSup_nonzeroLocus_secPull_lin a) (GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h)
    (t := s) hs ?_
  · rw [hg] at e
    exact e
  intro z
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (ht.ge (Set.mem_univ z))
  obtain ⟨l, hl⟩ := GlobalTheory.exists_chart_of_mem_nonzeroLocus hi
  have hW : nonzeroLocus (t i) ⊓ H.U l ≤ GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N i :=
    inf_le_left.trans (GlobalTheory.ProjSpace.toProj_preimage_chart f t ht i).ge
  have hk : nonzeroLocus (t i) ⊓ H.U l ≤ GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h ⁻¹ᵁ
      ((GlobalTheory.ProjSpace.O1 R N).pull (GlobalTheory.SpanVA.dom a).ι).U (fun _ => i) := by
    refine hW.trans (le_of_eq ?_)
    erw [GlobalTheory.Cartier.pull_U]
    rw [← Scheme.Hom.comp_preimage, GlobalTheory.SpanVA.liftDom_fac]
    rfl
  refine ⟨nonzeroLocus (t i) ⊓ H.U l, ⟨hi, hl⟩, fun _ => i, hk, l, inf_le_right, ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X inf_le_right ((t i).f l),
    fun j => ?_⟩
  have key : ((GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h).appLE _ _ hk).hom
      ((GlobalTheory.Cartier.secPull (GlobalTheory.SpanVA.lin a j) (GlobalTheory.SpanVA.dom a).ι).f (fun _ => i)) =
      ((GlobalTheory.ProjSpace.toProj f t ht).appLE (GlobalTheory.ProjSpace.chart R N i) _ hW).hom ((GlobalTheory.SpanVA.lin a j).f i) := by
    show ((GlobalTheory.SpanVA.liftDom a (GlobalTheory.ProjSpace.toProj f t ht) h).appLE _ _ hk).hom
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG _ _ (((GlobalTheory.SpanVA.dom a).ι.app _).hom ((GlobalTheory.SpanVA.lin a j).f i))) = _
    rw [GlobalTheory.ProjSpace.appLE_resG, Scheme.Hom.app_eq_appLE, GlobalTheory.ProjSpace.appLE_appLE]
    exact congrArg (fun ψ => ψ.hom ((GlobalTheory.SpanVA.lin a j).f i))
      (GlobalTheory.ProjSpace.appLE_of_eq (GlobalTheory.SpanVA.liftDom_fac a _ h) (GlobalTheory.ProjSpace.chart R N i) _ _ hW)

  rw [key, GlobalTheory.SpanVA.lin_f, map_sum, hst j, GlobalTheory.LinChange.sum_f, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [GlobalTheory.LB.smul_f, map_mul, map_mul, GlobalTheory.LinChange.resG_cst, GlobalTheory.LinChange.resG_cst]
  erw [GlobalTheory.LinChange.appLE_cst (PSpace.str R N) (GlobalTheory.ProjSpace.toProj f t ht) hW (a j n)]
  rw [GlobalTheory.ProjSpace.toProj_str]
  change _ = _ * (_ * GlobalTheory.ProjSpace.pullRatio (GlobalTheory.ProjSpace.toProj f t ht) _ i hW n)
  rw [GlobalTheory.ProjSpace.pullRatio_toProj_on, GlobalTheory.ProjSpace.secRatio_on (t i) (t n) l inf_le_left inf_le_right]
  ring
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj O1 coord)

theorem comb_f {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ} (g : X ⟶ Sp R) (c : Fin n → R)
    (t : Fin n → H.Sec) (k : H.ι) :
    (∑ j, GlobalTheory.AbLaw.cst g ⊤ (c j) • t j).f k = ∑ j, GlobalTheory.AbLaw.cst g (H.U k) (c j) * (t j).f k := by
  rw [GlobalTheory.LinChange.sum_f]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.LB.smul_f, GlobalTheory.LinChange.resG_cst]

theorem secPull_comb_f {R : Type} [CommRing R] {X Y : Scheme.{0}} {L : LB X} {n : ℕ} (p : X ⟶ Sp R)
    (c : Fin n → R) (t : Fin n → L.Sec) (φ : Y ⟶ X) (q : (L.pull φ).ι) :
    (GlobalTheory.Cartier.secPull (∑ j, GlobalTheory.AbLaw.cst p ⊤ (c j) • t j) φ).f q =
      ∑ j, GlobalTheory.AbLaw.cst (φ ≫ p) ((L.pull φ).U q) (c j) * (GlobalTheory.Cartier.secPull (t j) φ).f q := by
  have hc : ∀ (U : X.Opens) (r : R),
      (φ.app U).hom (GlobalTheory.AbLaw.cst p U r) = GlobalTheory.AbLaw.cst (φ ≫ p) (φ ⁻¹ᵁ U) r := fun U r => by
    rw [Scheme.Hom.app_eq_appLE]
    exact GlobalTheory.LinChange.appLE_cst p φ le_rfl r
  dsimp only [GlobalTheory.Cartier.secPull]

  rw [comb_f, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, hc, GlobalTheory.LinChange.resG_cst]

end GlobalTheory.SpanVA


open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus) in
theorem GlobalTheory.SpanVA.toProj_preimage_nonzeroLocus_lin : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (ht : ⨆ j, nonzeroLocus (t j) = ⊤), (∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) → ∀ i, GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ nonzeroLocus (GlobalTheory.SpanVA.lin a i) = nonzeroLocus (s i) := by
  intro R _ X f H m N s t a hH ht hst i
  rw [← GlobalTheory.Cartier.nonzeroLocus_secPull]
  refine GlobalTheory.Cartier.SecMaps.nonzeroLocus_eq (pull_isLB (GlobalTheory.ProjSpace.O1_isLB R N) _) hH
    (w := GlobalTheory.ProjSpace.toProjIso f t ht) ?_
  rintro ⟨k, q⟩
  have hc := fun j => GlobalTheory.ProjSpace.secMaps_toProjIso f t ht j (k, q)
  change resG X _ ((s i).f k) = _ * resG X _ ((GlobalTheory.Cartier.secPull (GlobalTheory.SpanVA.lin a i) (GlobalTheory.ProjSpace.toProj f t ht)).f q)
  rw [GlobalTheory.SpanVA.lin]

  rw [hst i, GlobalTheory.SpanVA.comb_f, GlobalTheory.SpanVA.secPull_comb_f, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, GlobalTheory.LinChange.resG_cst, GlobalTheory.LinChange.resG_cst, hc j, GlobalTheory.ProjSpace.toProj_str]
  ring
end
end

section

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Merge

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

def comap {Tp Tp' : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (f : Tp' → Tp) : OMDat C R i Tp' (fun t => tup (f t)) where
  c' := O.c'
  hle := O.hle
  jL := O.jL
  hV := O.hV
  c0' := O.c0'
  lev := O.lev
  dδ := fun t => O.dδ (f t)
  Cl' := fun t => O.Cl' (f t)
  fCl := fun t => O.fCl (f t)
  bad := fun t => O.bad (f t)
  Lh := fun t => O.Lh (f t)
  La := fun t => O.La (f t)
  Nc := fun t => O.Nc (f t)
  gam := fun t => O.gam (f t)
  vol := fun t => O.vol (f t)
  ep := fun t => O.ep (f t)
  B := fun t => O.B (f t)
  epF := fun t => O.epF (f t)
  io := O.io
  hw := O.hw
  φ := fun t => O.φ (f t)
  w := fun t => O.w (f t)
  U₂ := fun t => O.U₂ (f t)
  dict₂ := fun t => O.dict₂ (f t)
  xi := fun t => O.xi (f t)
  thAd := fun t => O.thAd (f t)
  Plc := fun t => O.Plc (f t)

theorem pins_comap {Tp Tp' : Type} {tup : Tp → T0} {O : OMDat C R i Tp tup} (f : Tp' → Tp) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) : (comap O f).Pins κ v₀ ι x₀ :=
  ⟨h.lift, fun t => h.tuple (f t), h.act, fun t => h.bad (f t), fun t => h.reps (f t), fun t => h.ep (f t), h.io,
    fun t => h.w (f t), fun t => h.cov (f t), h.cxi.imp fun _ hc => ⟨hc.1, fun t => hc.2 (f t)⟩, fun t => h.model₂ (f t)⟩

variable {J : Type} {tup : J → T0} (src : ∀ j, OMDat C R i Unit (fun _ => tup j)) (c₃ : Coeff C.Q.l) (h₃ : C.Q.c.F ≤ c₃.F)
  (hs : ∀ j, (src j).c'.F ≤ c₃.F) (jL₃ : D.what₂.LL →+* c₃.F) (hV₃ : C.V ((i : ℕ) + 1) (sOv C c₃ h₃) = Wc D i)
  (c0₃ : VsV D i c₃.F →ₛₗ[inC c₃] (R.cV i).W)
  (lev : G → (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (C.Q.Dw ((i : ℕ) + 1)).La)
  (io₃ : VsV D i c₃.F →ₗ[c₃.F] MvPolynomial (LtN (C.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) c₃.F) (hw₃ : VsV D i c₃.F)
  (u : J → c₃.F) (h : ∀ j, (src j).Cl' () → GA D (Vc D i)) (v₀ : (R.MW i (sg0 D A)).Vec)

def merge : OMDat C R i J tup where
  c' := c₃
  hle := h₃
  jL := jL₃
  hV := hV₃
  c0' := c0₃
  lev := lev
  dδ := fun j => covBC (hs j) ((src j).dδ ()) (u j)
  Cl' := fun j => (src j).Cl' ()
  fCl := fun j => (src j).fCl ()
  bad := fun j => (src j).bad ()
  Lh := fun j => (src j).Lh ()
  La := fun j => (src j).La ()
  Nc := fun j => (src j).Nc ()
  gam := fun j => (src j).gam ()
  vol := fun j => incF _ c₃ (hs j) ((src j).vol ())
  ep := fun j k => incF _ c₃ (hs j) ((src j).ep () k)
  B := fun j I => incF _ c₃ (hs j) ((src j).B () I)
  epF := fun j L => incF _ c₃ (hs j) ((src j).epF () L)
  io := io₃
  hw := hw₃
  φ := fun j x => incF _ c₃ (hs j) ((src j).φ () x)
  w := fun j k q => incF _ c₃ (hs j) ((src j).w () k q)
  U₂ := fun j => covUnf (hs j) ((src j).dδ ()) (u j) ((src j).U₂ ())
  dict₂ := fun j => (src j).dict₂ ()
  xi := fun j => (src j).xi ()
  thAd := fun j => thAdOf R i (tup j) (h j) c0₃ v₀
  Plc := fun j x => ∃ x₀, Place R i (tup j) (h j) c0₃ (jVx R i (tup j) x₀) x

theorem repsR_map {K K' : Type} [Field K] [Field K'] (j : K →+* K') {t : T0} {Cl : Type} {h : Cl → GA D (Vc D i)} {bad J' Lh gam}
    {vol : K} (hr : RepsR R i t h bad J' Lh gam vol) : RepsR R i t h bad J' Lh gam (j vol) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
  exact ⟨h1, h2, h3, h4, by rw [h5, map_inv₀, map_natCast], h6⟩


end Merge

end GlobalTheory.OneMapAll
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

open IsDedekindDomain

namespace GlobalTheory.InertiaUnram

theorem valuationSubring_valuation_lt_one_iff {L : Type} [Field L] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation L Γ) (x : L) : v.valuationSubring.valuation x < 1 ↔ v x < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
    Valuation.mem_valuationSubring_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [map_inv₀, not_le]
    constructor
    · rintro (h | h)
      · exact absurd h hx
      · exact (one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).1 h
    · intro h
      exact Or.inr ((one_lt_inv₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hx))).2 h)

theorem mem_iff_valuation_le_one (L S : Type) [Field L] [CommRing S] [IsDomain S] [IsDedekindDomain S]
    [Algebra S L] [IsFractionRing S L] (W : ValuationSubring L) (hS : ∀ s : S, algebraMap S L s ∈ W)
    (P : HeightOneSpectrum S) (hP : P.asIdeal = GlobalTheory.ProlongConj.primeBelow S W hS) (x : L) :
    x ∈ W ↔ P.valuation L x ≤ 1 := by
  have hS' : ∀ s : S, algebraMap S L s ∈ (P.valuation L).valuationSubring := fun s =>
    (Valuation.mem_valuationSubring_iff _ _).2 (P.valuation_le_one s)
  have key : ∀ s : S, W.valuation (algebraMap S L s) < 1 ↔
      (P.valuation L).valuationSubring.valuation (algebraMap S L s) < 1 := by
    intro s
    rw [valuationSubring_valuation_lt_one_iff, ← GlobalTheory.ProlongConj.mem_primeBelow S hS, ← hP]
    exact (P.valuation_lt_one_iff_mem s).symm
  have hW : W = (P.valuation L).valuationSubring :=
    le_antisymm (GlobalTheory.ProlongConj.le_of_valuation_lt_one_iff S hS hS' key)
      (GlobalTheory.ProlongConj.le_of_valuation_lt_one_iff S hS' hS fun s => (key s).symm)
  rw [hW, Valuation.mem_valuationSubring_iff]

theorem mem_inertia_of_mem_inertia (K L S : Type) [Field K] [Field L] [Algebra K L] [CommRing S] [IsDomain S]
    [IsDedekindDomain S] [Algebra S L] [IsFractionRing S L] [MulSemiringAction (L ≃ₐ[K] L) S]
    (hact : ∀ (g : L ≃ₐ[K] L) (s : S), algebraMap S L (g • s) = g (algebraMap S L s))
    (P : HeightOneSpectrum S) (W : ValuationSubring L) (hW : ∀ x, x ∈ W ↔ P.valuation L x ≤ 1)
    (σ : L ≃ₐ[K] L) (hσ : σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L)) : σ ∈ inertia K W := by
  set v := P.valuation L with hv
  have hWeq : W = v.valuationSubring := by
    ext x
    rw [hW, Valuation.mem_valuationSubring_iff]
  have hS : ∀ s : S, algebraMap S L s ∈ W := fun s => (hW _).2 (P.valuation_le_one s)
  have aux : ∀ τ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), ∀ x, v x ≤ 1 → v (τ x) ≤ 1 ∧ v (τ x - x) < 1 := by
    intro τ hτ x hx
    have hτ' := AddSubgroup.mem_inertia.mp hτ
    obtain ⟨s, t, hs1, e⟩ := GlobalTheory.ProlongConj.exists_den S W hS ((hW x).2 hx)
    have hsP : s ∉ P.asIdeal := by
      intro hm
      have h1 : W.valuation (algebraMap S L s) < 1 := by
        rw [hWeq, valuationSubring_valuation_lt_one_iff]
        exact (P.valuation_lt_one_iff_mem s).2 hm
      rw [hs1] at h1
      exact lt_irrefl _ h1
    have va : v (algebraMap S L s) = 1 :=
      le_antisymm (P.valuation_le_one s) (not_lt.1 fun h => hsP ((P.valuation_lt_one_iff_mem s).1 h))
    have hdiff : ∀ u : S, v (τ (algebraMap S L u) - algebraMap S L u) < 1 := by
      intro u
      rw [← hact, ← map_sub]
      exact (P.valuation_lt_one_iff_mem _).2 (hτ' u)
    have va' : v (τ (algebraMap S L s)) = 1 := by
      have h := Valuation.map_add_eq_of_lt_right v (x := τ (algebraMap S L s) - algebraMap S L s)
        (y := algebraMap S L s) (by rw [va]; exact hdiff s)
      rw [sub_add_cancel, va] at h
      exact h
    have hs0 : algebraMap S L s ≠ 0 := fun h => by rw [h, map_zero] at va; exact zero_ne_one va
    have hs0' : τ (algebraMap S L s) ≠ 0 := fun h => by rw [h, map_zero] at va'; exact zero_ne_one va'
    have hx' : x = algebraMap S L t / algebraMap S L s := by rw [← e]; field_simp
    have hτx : τ x = τ (algebraMap S L t) / τ (algebraMap S L s) := by rw [hx', map_div₀]
    constructor
    · rw [hτx, map_div₀, va', div_one, ← hact]
      exact P.valuation_le_one _
    · have : τ x - x = ((τ (algebraMap S L t) - algebraMap S L t) * algebraMap S L s -
          algebraMap S L t * (τ (algebraMap S L s) - algebraMap S L s)) /
          (τ (algebraMap S L s) * algebraMap S L s) := by
        rw [hτx, hx']; field_simp; ring
      rw [this, map_div₀, map_mul v (τ _), va, va', _root_.mul_one, div_one]
      refine Valuation.map_sub_lt v ?_ ?_
      · rw [map_mul, va, _root_.mul_one]; exact hdiff t
      · rw [map_mul]
        calc v (algebraMap S L t) * v (τ (algebraMap S L s) - algebraMap S L s)
            ≤ 1 * v (τ (algebraMap S L s) - algebraMap S L s) :=
              mul_le_mul_left (P.valuation_le_one t) _
          _ < 1 := by rw [_root_.one_mul]; exact hdiff s
  rw [mem_inertia_iff]
  refine ⟨?_, fun x hx => ?_⟩
  · ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, hW, hW]
    constructor
    · intro h
      have h2 := (aux σ hσ _ h).1
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h2
    · intro h
      exact (aux σ⁻¹ (inv_mem hσ) x h).1
  · rw [hWeq, valuationSubring_valuation_lt_one_iff]
    exact (aux σ hσ x ((hW x).1 hx)).2

theorem valuation_le_of_fixed (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L] [SMulCommClass (L ≃ₐ[K] L) R L]
    [IsDedekindDomain (integralClosure R L)] [IsFractionRing (integralClosure R L) L]
    (P : HeightOneSpectrum (integralClosure R L)) (π : R) (hπ : Irreducible π) (y : L)
    (hy : ∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ y = y) (hlt : P.valuation L y < 1) :
    P.valuation L y ≤ P.valuation L (algebraMap K L (algebraMap R K π)) := by
  rw [GlobalTheory.T.valuation_uniformizer_integralClosure_eq_exp_neg_ramificationIdx R K L P π hπ, ← GlobalTheory.T.card_inertia_eq_ramificationIdx_of_perfect_residue R K L P]
  exact GlobalTheory.T.valuation_le_exp_neg_card_inertia_of_inertia_fixed R K L P y hy hlt

theorem div_uniformiser_mem : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (W : ValuationSubring L), IsAbove R K W.toSubring →
    ∀ π : R, Irreducible π → ∀ y : L, (∀ τ ∈ inertia K W, τ y = y) → y ∈ W.nonunits →
    y / algebraMap K L (algebraMap R K π) ∈ W := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ W hW π hπ y hy hyW
  letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hc : SMulCommClass (L ≃ₐ[K] L) R L := ⟨fun g r x => by
    rw [← IsScalarTower.algebraMap_smul K r x, ← IsScalarTower.algebraMap_smul K r (g • x)]
    exact map_smul g _ _⟩
  haveI : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  haveI : IsFractionRing (integralClosure R L) L := integralClosure.isFractionRing_of_finite_extension K L
  have hR : ∀ r : R, algebraMap R L r ∈ W := by
    intro r
    have : algebraMap R K r ∈ W.toSubring.comap (algebraMap K L) := by rw [hW]; exact ⟨r, rfl⟩
    exact this
  have hS : ∀ s : integralClosure R L, algebraMap (integralClosure R L) L s ∈ W :=
    fun s => GlobalTheory.ProlongConj.mem_of_isIntegral W hR s.2
  set c : L := algebraMap K L (algebraMap R K π) with hc_def
  have hc0 : c ≠ 0 := by
    rw [hc_def, map_ne_zero_iff _ (algebraMap K L).injective,
      map_ne_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero
  have hcW : W.valuation c < 1 := by
    rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]
    right
    intro hinv
    have h1 : (algebraMap R K π)⁻¹ ∈ W.toSubring.comap (algebraMap K L) := by
      change algebraMap K L _ ∈ W
      rw [map_inv₀]; exact hinv
    rw [hW] at h1
    obtain ⟨s, hs⟩ := h1
    apply hπ.not_isUnit
    refine IsUnit.of_mul_eq_one s (IsFractionRing.injective R K ?_)
    rw [map_mul, hs, map_one, mul_inv_cancel₀]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).1 (by rw [← hc_def]; exact hc0)
  set P0 := GlobalTheory.ProlongConj.primeBelow (integralClosure R L) W hS
  have hP0 : P0 ≠ ⊥ := by
    intro h
    have hm : algebraMap R (integralClosure R L) π ∈ P0 := by
      rw [GlobalTheory.ProlongConj.mem_primeBelow, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R K L]
      exact hcW
    rw [h, Ideal.mem_bot] at hm
    apply hc0
    rw [hc_def, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R (integralClosure R L) L, hm,
      map_zero]
  let P : HeightOneSpectrum (integralClosure R L) := ⟨P0, inferInstance, hP0⟩
  have hWv := mem_iff_valuation_le_one L (integralClosure R L) W hS P rfl
  have hI : ∀ σ ∈ P.asIdeal.inertia (L ≃ₐ[K] L), σ ∈ inertia K W :=
    mem_inertia_of_mem_inertia K L (integralClosure R L) (fun _ _ => rfl) P W hWv
  have hlt : P.valuation L y < 1 := by
    rcases (ValuationSubring.mem_nonunits_iff_or W).1 hyW with h | h
    · rw [h, map_zero]; exact zero_lt_one
    · by_contra hge
      push_neg at hge
      apply h
      rw [hWv, map_inv₀]
      have h1 : P.valuation L y ≤ 1 := (hWv y).1 ((W.valuation_le_one_iff y).1 (le_of_lt (W.mem_nonunits_iff.1 hyW)))
      rw [le_antisymm h1 hge, inv_one]
  have key := valuation_le_of_fixed R K L P π hπ y (fun σ hσ => hy σ (hI σ hσ)) hlt
  rw [hWv, map_div₀]
  have hv0 : P.valuation L c ≠ 0 := (Valuation.ne_zero_iff _).2 hc0
  rw [div_le_one₀ (zero_lt_iff.2 hv0)]
  exact key

end GlobalTheory.InertiaUnram
end
