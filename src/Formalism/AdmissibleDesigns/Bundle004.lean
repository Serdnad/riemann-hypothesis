module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle224
public import Formalism.AdmissibleDesigns.GlobalIndexTheoremPlacesOfRNAdm
public import Formalism.AdmissibleDesigns.CoboundaryMemFiniteClasses
public import Formalism.AdicCompletionExports.AdicCompleteRingEquiv.IsAdicCompleteOfRingEquiv
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.AdmissibleDesigns.Bundle003
public import Formalism.AdmissibleDesigns.SelfGood
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions.N Topology

namespace Formalism.MainNotions.N.K.Norm

section Adic

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [IsTopologicalRing O]

theorem mem_pow_of_mul {c : O} (hc : c ≠ 0) : ∃ k : ℕ, ∀ (n : ℕ) (y : O),
    c * y ∈ (IsLocalRing.maximalIdeal O) ^ (n + k) → y ∈ (IsLocalRing.maximalIdeal O) ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine ⟨k, fun n y hy => ?_⟩
  have hm := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [hm, Ideal.span_singleton_pow] at hy ⊢
  rw [mul_assoc, Ideal.unit_mul_mem_iff_mem _ u.isUnit, Ideal.mem_span_singleton, pow_add, mul_comm (ϖ ^ n)] at hy
  rw [Ideal.mem_span_singleton]
  exact (mul_dvd_mul_iff_left (pow_ne_zero k hϖ.ne_zero)).1 hy

theorem continuous_of_mul {X : Type} [TopologicalSpace X] (hadic : IsAdic (IsLocalRing.maximalIdeal O))
    {c : O} (hc : c ≠ 0) {f : X → O} (hf : Continuous fun x => c * f x) : Continuous f := by
  apply GlobalTheory.BlockJumpsCompare.continuous_of_mul <;> assumption

end Adic

section Rec

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem map_smul_toK' (c : D.nd.O i) (A : MatN D.nd i) :
    (c • A).map (toK D.nd i) = toK D.nd i c • A.map (toK D.nd i) := by
  ext a b
  simp [Matrix.smul_apply]

theorem exists_integral_mul (M : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) :
    ∃ (b : D.nd.O i) (M0 : MatN D.nd i), b ≠ 0 ∧ M0.map (toK D.nd i) = b • M := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (D.nd.O i)) Finset.univ
    (fun ab : Fin D.R.nV × Fin D.R.nV => M ab.1 ab.2)
  choose M0 hM0 using fun ab : Fin D.R.nV × Fin D.R.nV => hb ab (Finset.mem_univ _)
  refine ⟨b, fun a c => M0 (a, c), nonZeroDivisors.coe_ne_zero b, ?_⟩
  ext a c
  simp only [Matrix.smul_apply]
  exact hM0 (a, c)

theorem rhoCont_of (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) : RhoCont i ρ π := by
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := conjK_self i r ρ π hd
  have hA : ∀ g, (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = P * (rO D.nd i r π g).map (toK D.nd i) * Q := by
    intro g
    have h := hconj g
    beta_reduce at h
    rw [h, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  obtain ⟨b1, P0, hb1, hP0⟩ := exists_integral_mul i P
  obtain ⟨b2, Q0, hb2, hQ0⟩ := exists_integral_mul i Q
  have hid : ∀ g, (b1 * b2) • rO D.nd i (rN i r ρ π) π g = P0 * rO D.nd i r π g * Q0 := by
    intro g
    apply Matrix.map_injective (toK_inj i)
    show ((b1 * b2) • rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = (P0 * rO D.nd i r π g * Q0).map (toK D.nd i)
    rw [Matrix.map_mul, Matrix.map_mul, hP0, hQ0, map_smul_toK', hA, map_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, mul_comm (toK D.nd i b1), ← map_mul]
    exact algebraMap_smul (KK D.nd i) (b2 * b1) _
  have hcont : Continuous fun g => (b1 * b2) • rO D.nd i (rN i r ρ π) π g := by
    simp only [hid]
    exact (continuous_const.matrix_mul (hc π)).matrix_mul continuous_const
  have hne : b1 * b2 ≠ 0 := mul_ne_zero hb1 hb2
  unfold RhoCont
  refine continuous_pi fun a => continuous_pi fun b => ?_
  refine continuous_of_mul (D.nd.O_adic i) hne ?_
  have h2 : Continuous fun g => ((b1 * b2) • rO D.nd i (rN i r ρ π) π g) (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) :=
    (continuous_apply_apply _ _).comp hcont
  refine h2.congr (fun g => ?_)
  change (b1 * b2) * rO D.nd i (rN i r ρ π) π g (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) = _
  rw [(normAt_rN i r ρ π).2.2 g a b]

end Rec

end Formalism.MainNotions.N.K.Norm
end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Len

variable {R S : Type} [CommRing R] [CommRing S] (σ : R ≃+* S)

theorem length_le_semi {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →+ N) (hf : Function.Injective f) (hs : ∀ (a : R) (m : M), f (a • m) = σ a • f m) :
    Module.length R M ≤ Module.length S N := by
  classical
  rw [Module.length_eq_height, Module.length_eq_height]
  let F : Submodule R M → Submodule S N := fun p =>
    { carrier := f '' p
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, p.add_mem hx hy, map_add f x y⟩
      zero_mem' := ⟨0, p.zero_mem, map_zero f⟩
      smul_mem' := by
        rintro s _ ⟨x, hx, rfl⟩
        refine ⟨σ.symm s • x, p.smul_mem _ hx, ?_⟩
        rw [hs, RingEquiv.apply_symm_apply] }
  have hF : StrictMono F := by
    intro p q hpq
    rw [SetLike.lt_iff_le_and_exists] at hpq ⊢
    obtain ⟨hle, x, hxq, hxp⟩ := hpq
    refine ⟨?_, f x, ⟨x, hxq, rfl⟩, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hle hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact hxp (hf hyx ▸ hy)
  exact (Order.height_le_height_apply_of_strictMono F hF ⊤).trans (Order.height_mono le_top)

theorem length_quot_eq (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = Module.length S (S ⧸ Ideal.span {σ a}) := by
  classical
  have hJ : Ideal.span {σ a} = (Ideal.span {a}).map (σ : R →+* S) := by
    simp [Ideal.map_span]
  let e := Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {σ a}) σ hJ
  have he : ∀ (r : R) (x : R ⧸ Ideal.span {a}), e (r • x) = σ r • e x := by
    intro r x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [e, Ideal.quotientEquiv_apply, Algebra.smul_def, Ideal.quotientMap_mk, Ideal.Quotient.algebraMap_eq]
  refine le_antisymm (length_le_semi σ e.toAddEquiv.toAddMonoidHom e.injective he) ?_
  refine length_le_semi σ.symm e.symm.toAddEquiv.toAddMonoidHom e.symm.injective ?_
  intro s y
  apply e.injective
  show e (e.symm (s • y)) = e (σ.symm s • e.symm y)
  rw [he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

end Len

section QRec

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL] {e : ℕ}

abbrev QrecS (Ce : TwLat PD LL O e) (cB : ℕ) : Submodule O (G → Ce.V ⧸ Ce.L.T) :=
  divisibleCocycles Ce.L ⊓ (HfD PD Ce.L).comap (((PD.p : O) ^ cB) • LinearMap.id)

abbrev Qrec (Ce : TwLat PD LL O e) (cB : ℕ) : Type :=
  ↥(QrecS PD Ce cB) ⧸ (divisibleCocycles Ce.L ⊓ HfD PD Ce.L).comap (QrecS PD Ce cB).subtype

def LenMap {O' : Type} [CommRing O'] (σ : O' ≃+* O) (X : Type) [AddCommGroup X] [Module O' X]
    (Ce : TwLat PD LL O e) (cB : ℕ) : Prop :=
  ∃ f : X →+ Qrec PD Ce cB, Function.Injective f ∧ ∀ (a : O') (x : X), f (a • x) = σ a • f x

theorem len_gen {t cB : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (het : e < t) (Ce : TwLat PD LL O e)
    {O' : Type} [CommRing O'] (σ : O' ≃+* O) {X : Type} [AddCommGroup X] [Module O' X]
    (h : LenMap PD σ X Ce cB) :
    Module.length O' X ≤ ((finrank Qp K : ℕ∞) + 1) * (cB : ℕ∞) * lenOl PD (O := O) := by
  obtain ⟨f, hf, hs⟩ := h
  refine (length_le_semi σ f hf hs).trans ?_
  cases Ce
  exact (hTB.2 e het _ _ _ (by assumption) (by assumption)).2.2

end QRec

section RecLen

open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def TBDict2 (cB : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
      ∃ (Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL))
        (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1)),
        YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
        PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd ∧
        YLoc (O := D.nd.O i) (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) ∧
        LenMap (Br.PD D.loc D.nbr i w hw) (selfO i hw) (Qcore i dc Dd c (idx i dc w) cB) Cd.Ce cB



private theorem lenMap_Qcore (cB : ℕ) (hd : TBDict2 i dc r π Dd cB) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hwrow : w ∈ dc.row)
    (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) :
    ∃ Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1),
      LenMap (Br.PD D.loc D.nbr i w hw) (selfO i hw) (Qcore i dc Dd c (idx i dc w) cB) Cd.Ce cB :=
  (hd w hw hwrow c hc).elim fun _ h => h.elim fun Cd h' => ⟨Cd, h'.2.2.2⟩

theorem tbDict_of (cB : ℕ) (h : TBDict2 i dc r π Dd cB) : TBDict i dc r π Dd := by
  unfold TBDict2 at h
  unfold TBDict
  intro w hw hrow c hc
  obtain ⟨Y, Cd, h1, h2, h3, -⟩ := h w hw hrow c hc
  exact ⟨Y, Cd, h1, h2, h3⟩



theorem tbLen_w (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hd : TBDict2 i dc r π Dd cB) {w : HeightOneSpectrum (𝓞 D.host.E)} (hwrow : w ∈ dc.row)
    (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) : TBLenAt i dc Dd cB (idx i dc w) c := by
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := (dc.cover w).1 (Or.inl hwrow)
  have hpl : w ∈ plSet i dc := by simp [plSet, hwrow]
  unfold TrivialBoundAtRows at hTB
  unfold TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility at hTie
  obtain ⟨Cd, hL⟩ := lenMap_Qcore (hd := hd) (hw := hw) (hwrow := hwrow) (c := c) (hc := hc)
  have het : (c : ℕ) - 1 < D.R.t := by have := c.isLt; omega
  have hdeg := (hTie w hw).2.2
  unfold Br.DegW at hdeg

  have aux : ∀ {R' S' : Type} [CommRing R'] [CommRing S'] (σ' : R' ≃+* S') (n : ℕ),
      Module.length R' (R' ⧸ Ideal.span {(n : R')}) = Module.length S' (S' ⧸ Ideal.span {(n : S')}) := by
    intro R' S' _ _ σ' n
    rw [length_quot_eq σ', map_natCast]
  unfold TBLenAt
  refine le_trans (len_gen (Br.PD D.loc D.nbr i w hw) (hTB w hw hwrow) het Cd.Ce (selfO i hw) hL) (le_of_eq ?_)
  rw [plOf_idx (h := hpl), ← hdeg]
  unfold lenOl
  rw [Br.PD_p, ← aux (selfO i hw) (D.nd.l i)]
  ring

theorem tbLen_of (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hd : TBDict2 i dc r π Dd cB) : TBLen i dc Dd cB := by
  unfold TBLen
  intro n hn c hc
  unfold rowsN at hn
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hn
  exact tbLen_w (hTB := hTB) (hTie := hTie) (hd := hd) (hwrow := hw) (c := c) (hc := hc)

theorem trivial_bound_target_of_dict (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hd : TBDict2 i dc r π Dd cB) : TBTarget i dc Dd cB :=
  tbTarget_of (hTB := hTB) (hd := tbDict_of (h := hd)) (hlen := tbLen_of (hTB := hTB) (hTie := hTie) (hd := hd))

end RecLen

end Formalism.MainNotions.N.K.TB

end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Classical

namespace Formalism.MainNotions.N.KBKa

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.MainNotions.N.KHf

section Cyc

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycZ_eq_χQ (g : ↥(GK Bw.Kw)) :
    ((ReciprocityTheory.Gal.cycZ (F := E) (Ω := Ω) l ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]) : ℚ_[l]) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := by
  set x : ℚ_[l] := ((ReciprocityTheory.Gal.cycZ (F := E) (Ω := Ω) l ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]) : ℚ_[l])
    with hx
  set x' : ℚ_[l] := ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) with hx'
  have key : ∀ m : ℕ, ‖x - x'‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    haveI : NeZero ((l ^ m : ℕ) : Ω) := ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    obtain ⟨ζ', hζ'⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hζ : IsPrimitiveRoot (Bw.j ζ') (l ^ m) := hζ'.map_of_injective Bw.j.injective
    obtain ⟨a, ha, hxa⟩ := Formalism.AdicCompletionExports.isCycG_cycZ l E Ω ℤ_[l] (RingHom.id _)
      ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) m ζ' hζ'.pow_eq_one
    obtain ⟨a', hxa', ha'⟩ := P.χQ_cyc (g : GQ l) m (Bw.j ζ') hζ.pow_eq_one
    have hg : (g : GQ l) (Bw.j ζ') = Bw.j ζ' ^ a := by
      have h0 := Bw.e_comm (Br.ι Bw g) ζ'
      have he : Bw.e (Br.ι Bw g) = g := Bw.e.apply_symm_apply g
      rw [he] at h0
      rw [h0, ha, map_pow]
    have h1 : a ≡ a' [MOD l ^ m] := by
      have h0 := hg.symm.trans ha'
      have hf : IsOfFinOrder (Bw.j ζ') :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨l ^ m, pow_pos (Fact.out : l.Prime).pos m, hζ.pow_eq_one⟩
      rwa [hf.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h0
    have hxa2 : ‖x - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      change ((ReciprocityTheory.Gal.cycZ (F := E) (Ω := Ω) l ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]) - (a : ℤ_[l]))
        ∈ Ideal.span {(l : ℤ_[l]) ^ m} at hxa
      have h0 := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 hxa
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h0
      exact h0
    have h2 : ‖((a : ℚ_[l]) - (a' : ℚ_[l]))‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      have h3 : ((l ^ m : ℕ) : ℤ) ∣ (a : ℤ) - (a' : ℤ) := Nat.modEq_iff_dvd.1 h1.symm
      have h4 := (Padic.norm_int_le_pow_iff_dvd ((a : ℤ) - a') m).2 (by exact_mod_cast h3)
      simpa using h4
    have h4 : x - x' = (x - a) + ((a - a') + -(x' - a')) := by ring
    rw [h4]
    exact (Padic.nonarchimedean _ _).trans (max_le hxa2 ((Padic.nonarchimedean _ _).trans
      (max_le h2 (by rwa [norm_neg]))))
  have hlim : Filter.Tendsto (fun m : ℕ => (l : ℝ) ^ (-(m : ℤ))) Filter.atTop (nhds 0) := by
    have h5 : ∀ m : ℕ, (l : ℝ) ^ (-(m : ℤ)) = ((l : ℝ)⁻¹) ^ m := fun m => by
      rw [zpow_neg, zpow_natCast, inv_pow]
    simp only [h5]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt))
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' hlim key))

end Cyc

section TopPi

variable {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace (FractionRing O)]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)
  (n : Type) [Fintype n]

end TopPi

section RecC

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  {VT VT' : Type}
  [AddCommGroup VT] [Module (D.nd.O i) VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul (D.nd.O i) VT] [Module (FractionRing (D.nd.O i)) VT]
  [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VT]
  [AddCommGroup VT'] [Module (D.nd.O i) VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul (D.nd.O i) VT'] [Module (FractionRing (D.nd.O i)) VT']
  [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VT']

theorem cycMatch_rec {w : ℕ} (hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i))
    (Dw : Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) VT VT')
    (hε : ∀ g : ↥(Γn i dc w), Dw.ε g = epsU D.nd i (g : GE D.nd)) :
    CycMatch Dw (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) (Br.PD D.loc D.nbr i _ hn) := by
  intro g
  rw [hε]
  have hP := cycZ_eq_χQ (D.nbr i _ hn) (D.loc (D.nd.l i)) g
  have hχ := (D.loc (D.nd.l i)).PD_χ (D.nbr i _ hn).Kw g
  simp only [eK, RingEquiv.ofBijective_apply, Br.toLLK, IsFractionRing.lift_algebraMap, LocBridge.toLL,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, epsU, Glob.epsO, MonoidHom.comp_apply,
    Units.coe_map, MonoidHom.coe_coe, cycLL, Br.PD, RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    LocBridge.eO_alg]
  rw [← IsScalarTower.algebraMap_apply, hχ, ← hP]
  first
  | exact IsScalarTower.algebraMap_apply ℤ_[D.nd.l i] ℚ_[D.nd.l i] _ _
  | rfl

end RecC

section RecD

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))

theorem rowIn_of {w : ℕ} (hε : ∀ g : ↥(Γn i dc w), (Dat w).ε g = epsU D.nd i (g : GE D.nd))
    (ht : ∀ hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
      HomeoK (eK (D.nbr i _ hn)) ∧ TopMatch (eK (D.nbr i _ hn)) (VT w) ∧ TopMatch (eK (D.nbr i _ hn)) (VT' w))
    (hdr : ∀ hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
      IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn)) (Dat w).ρT (Br.iota D.nbr i _ hn))) :
    RowIn i dc VT VT' Dat w := by
  intro hn
  obtain ⟨h1, h2, h3⟩ := ht hn
  exact ⟨h1, h2, h3, cycMatch_rec i dc hn (Dat w) hε, hdr hn⟩

end RecD

end Formalism.MainNotions.N.KBKa
end
end

section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)

theorem trivialBoundAtRows_of_admTB (cB : ℕ) (hG : SelfGood i) (h : Formalism.MainNotions.EmbeddingTypes.admTB i r π dc cB) : TrivialBoundAtRows i dc r π cB :=
  fun w hw hrow => h w hw hrow (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (hG w hw)

end Formalism.MainNotions.N.K.TB

end
end
