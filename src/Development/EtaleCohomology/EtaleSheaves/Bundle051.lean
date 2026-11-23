module

public import Development.EtaleCohomology.EtaleSheaves.Bundle035
public import Development.EtaleCohomology.EtaleSheaves.Bundle039
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Development.EtaleCohomology.EtaleSheaves.Bundle040
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.E.longPfSes
open LateralTheory.E.CxDescPf

variable {R : Type} [CommRing R]

theorem eF (N : ℕ) (i : ℤ) (h : -(N : ℤ) ≤ i) : (ComplexShape.embeddingUpIntGE (-(N : ℤ))).f (i + N).toNat = i := by
  show -(N : ℤ) + (((i + N).toNat : ℕ) : ℤ) = i; omega

def trX (K : Cx R) (N : ℕ) (i : ℤ) (h : -(N : ℤ) ≤ i) : (tr K N).X i ≅ K.X i := K.stupidTruncXIso _ (eF N i h)

theorem trZ (K : Cx R) (N : ℕ) (i : ℤ) (h : i < -(N : ℤ)) : IsZero ((tr K N).X i) :=
  K.isZero_stupidTrunc_X _ i (by intro k; show -(N : ℤ) + (k : ℤ) ≠ i; omega)

theorem tr_d (K : Cx R) (N : ℕ) (i j : ℤ) (hi : -(N : ℤ) ≤ i) (hj : -(N : ℤ) ≤ j) :
    (tr K N).d i j = (trX K N i hi).hom ≫ K.d i j ≫ (trX K N j hj).inv := by
  have h1 := eF N i hi
  have h2 := eF N j hj
  simp only [trX, HomologicalComplex.stupidTruncXIso, tr, HomologicalComplex.stupidTrunc, Iso.trans_hom, Iso.trans_inv,
    eqToIso.hom, eqToIso.inv, Category.assoc]
  rw [HomologicalComplex.extend_d_eq _ _ h1 h2, HomologicalComplex.restriction_d_eq _ _ h1 h2]
  simp [HomologicalComplex.restrictionXIso]

theorem trm_f {K L : Cx R} (g : K ⟶ L) (N : ℕ) (i : ℤ) (h : -(N : ℤ) ≤ i) :
    (trm g N).f i = (trX K N i h).hom ≫ g.f i ≫ (trX L N i h).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom g _ (eF N i h)

abbrev Sg (K : Cx R) (N : ℕ) : Cx R :=
  (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).obj (K.X (-((N + 1 : ℕ) : ℤ)))

theorem SgZ (K : Cx R) (N : ℕ) (i : ℤ) (h : i ≠ -((N + 1 : ℕ) : ℤ)) : IsZero ((Sg K N).X i) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ h

def ιf (K : Cx R) (N : ℕ) (i : ℤ) : (tr K N).X i ⟶ (tr K (N + 1)).X i :=
  if h : -(N : ℤ) ≤ i then (trX K N i h).hom ≫ (trX K (N + 1) i (by push_cast; omega)).inv else 0

def ι (K : Cx R) (N : ℕ) : tr K N ⟶ tr K (N + 1) where
  f := ιf K N
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases h : -(N : ℤ) ≤ i
    · have hj : -(N : ℤ) ≤ j := by omega
      rw [ιf, dite_eq_left h, ιf, dite_eq_left hj, tr_d K N i j h hj, tr_d K (N + 1) i j (by push_cast; omega) (by push_cast; omega)]
      simp
    · rw [ιf, dite_eq_right h, zero_comp]
      exact (trZ K N i (by omega)).eq_of_src _ _

def pf (K : Cx R) (N : ℕ) (i : ℤ) : (tr K (N + 1)).X i ⟶ (Sg K N).X i :=
  if h : i = -((N + 1 : ℕ) : ℤ) then
    (trX K (N + 1) i (by omega)).hom ≫ eqToHom (by rw [h]) ≫
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) _ (K.X (-((N + 1 : ℕ) : ℤ))) i h).inv
  else 0

def pp (K : Cx R) (N : ℕ) : tr K (N + 1) ⟶ Sg K N where
  f := pf K N
  comm' i j hij := by
    have hij' : i + 1 = j := hij
    by_cases hj : j = -((N + 1 : ℕ) : ℤ)
    · exact (trZ K (N + 1) i (by push_cast at hj ⊢; omega)).eq_of_src _ _
    · exact (SgZ K N j hj).eq_of_tgt _ _

theorem ιp (K : Cx R) (N : ℕ) : ι K N ≫ pp K N = 0 := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  by_cases h : -(N : ℤ) ≤ i
  · exact (SgZ K N i (by push_cast; omega)).eq_of_tgt _ _
  · show ιf K N i ≫ _ = 0
    rw [ιf, dite_eq_right h, zero_comp]

theorem nat1 {K L : Cx R} (g : K ⟶ L) (N : ℕ) : ι K N ≫ trm g (N + 1) = trm g N ≫ ι L N := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  by_cases h : -(N : ℤ) ≤ i
  · show ιf K N i ≫ _ = _ ≫ ιf L N i
    rw [ιf, dite_eq_left h, ιf, dite_eq_left h, trm_f g N i h, trm_f g (N + 1) i (by push_cast; omega)]
    simp
  · exact (trZ K N i (by omega)).eq_of_src _ _

theorem nat2 {K L : Cx R} (g : K ⟶ L) (N : ℕ) :
    pp K N ≫ (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ))) =
      trm g (N + 1) ≫ pp L N := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  by_cases h : i = -((N + 1 : ℕ) : ℤ)
  · subst h
    show pf K N _ ≫ _ = _ ≫ pf L N _
    rw [pf, dite_eq_left rfl, pf, dite_eq_left rfl, trm_f g (N + 1) _ (by omega)]
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleObjXSelf]
  · exact (SgZ L N i h).eq_of_tgt _ _

theorem sesK (K : Cx R) (N : ℕ) : (ShortComplex.mk (ι K N) (pp K N) (ιp K N)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases h : -(N : ℤ) ≤ i
  · have hz : IsZero ((Sg K N).X i) := SgZ K N i (by push_cast; omega)
    have : IsIso (ιf K N i) := by rw [ιf, dite_eq_left h]; infer_instance
    have hI : IsIso ((ShortComplex.mk (ι K N) (pp K N) (ιp K N)).map (HomologicalComplex.eval _ _ i)).f := this
    refine ShortComplex.ShortExact.mk' ?_ inferInstance (hz.epi _)
    rw [ShortComplex.exact_iff_epi _ (hz.eq_of_tgt _ _)]
    infer_instance
  · by_cases h' : i = -((N + 1 : ℕ) : ℤ)
    · have hz : IsZero ((tr K N).X i) := trZ K N i (by omega)
      have : IsIso (pf K N i) := by subst h'; rw [pf, dite_eq_left rfl]; exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance (Iso.isIso_inv _))
      have hI : IsIso ((ShortComplex.mk (ι K N) (pp K N) (ιp K N)).map (HomologicalComplex.eval _ _ i)).g := this
      refine ShortComplex.ShortExact.mk' ?_ (hz.mono _) inferInstance
      rw [ShortComplex.exact_iff_mono _ (hz.eq_of_src _ _)]
      infer_instance
    · have hz2 : IsZero ((tr K (N + 1)).X i) := trZ K (N + 1) i (by push_cast at h' ⊢; omega)
      have hz1 : IsZero ((tr K N).X i) := trZ K N i (by omega)
      exact ShortComplex.ShortExact.mk' (ShortComplex.exact_of_isZero_X₂ _ hz2) (hz1.mono _) ((SgZ K N i h').epi _)

theorem ses : LateralTheory.E.longPf.Ses := fun _ _ N =>
  ⟨fun K => ι K N, fun K => pp K N, fun K => ιp K N, fun K => sesK K N, fun g => ⟨nat1 g N, nat2 g N⟩⟩

theorem long_of (hLES : LateralTheory.E.longPf.LES) : LateralTheory.E.CxDescPf.long := LateralTheory.E.longPf.long_of hLES ses

end LateralTheory.E.longPfSes
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.ChowGraphCut

theorem iterLine_isProper {P S : Scheme.{0}} {q : P ⟶ S} (h : IterLine q) : IsProper q := by
  induction h with
  | iso e he => exact inferInstance
  | comp l k hl _ ih =>
    have := hl.1
    exact inferInstance

def Cover : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact p],
  Nonempty X → ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ j, IsAffineOpen (U j)) ∧ (∀ j, (U j : Set X).Nonempty) ∧
    ∀ x : X, ∃ j, x ∈ U j

def Embed : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType p]
  (V : X.Opens), IsAffineOpen V → ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A)) (W : P.Opens)
    (e : V.toScheme ⟶ W.toScheme), IterLine q ∧ IsClosedImmersion e ∧ e ≫ W.ι ≫ q = V.ι ≫ p

def IterComp : Prop := ∀ {P T S : Scheme.{0}} (l : P ⟶ T) (k : T ⟶ S), IterLine l → IterLine k → IterLine (l ≫ k)

def Prod : Prop := ∀ {S : Scheme.{0}} (n : ℕ) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S), (∀ j, IterLine (qj j)) →
  ∃ (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j), IterLine q ∧ (∀ j, π j ≫ qj j = q) ∧
    ∀ {T : Scheme.{0}} (t : T ⟶ S) (f : ∀ j, T ⟶ Pj j), (∀ j, f j ≫ qj j = t) →
      ∃! g : T ⟶ P, g ≫ q = t ∧ ∀ j, g ≫ π j = f j

def Core : Prop := ∀ {S X₁ : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁], IsIntegral X₁ →
  ∀ (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ j, (U j : Set X₁).Nonempty) → (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    (∀ {T : Scheme.{0}} (t : T ⟶ S) (f : ∀ j, T ⟶ Pj j), (∀ j, f j ≫ qj j = t) →
      ∃! g : T ⟶ P, g ≫ q = t ∧ ∀ j, g ≫ π j = f j) →
    ∃ (X' : Scheme.{0}) (i : X' ⟶ pullback p₁ q) (V : X₁.Opens) (s : V.toScheme ⟶ X'),
      IsClosedImmersion i ∧ IsClosedImmersion (i ≫ pullback.snd p₁ q) ∧ (V : Set X₁).Nonempty ∧
      s ≫ i ≫ pullback.fst p₁ q = V.ι

theorem goal_of (hC : Cover) (hE : Embed) (hP : Prod) (hK : Core) : ChowGraph := by
  intro A _ X₁ p₁ _ hX
  have := hX
  obtain ⟨n, U, hUa, hUn, hUc⟩ := hC A p₁ inferInstance
  choose Pj qj W e hq he hc using fun j => hE A p₁ (U j) (hUa j)
  obtain ⟨P, q, π, hq', hπ, hUP⟩ := hP n Pj qj hq
  have hsep : ∀ j, IsSeparated (qj j) := fun j => by
    have := iterLine_isProper (hq j)
    infer_instance
  obtain ⟨X', i, V, s, h1, h2, h3, h4⟩ := hK p₁ hX n U Pj qj W e P q π hUn hUc hsep he hc hπ hUP
  exact ⟨P, q, X', i, V, s, hq', h1, h2, h3, h4⟩

end LateralTheory.E.ChowGraphCut

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.IterBCPf

theorem iterLine_of_isPullback {S P : Scheme.{0}} {q : P ⟶ S} (hq : IterLine q) :
    ∀ {X P' : Scheme.{0}} {a : P' ⟶ P} {q' : P' ⟶ X} {g : X ⟶ S}, IsPullback a q' q g → IterLine q' := by
  induction hq with
  | iso e he =>
    intro X P' a q' g w
    exact IterLine.iso _ (w.isIso_snd_of_isIso he)
  | comp l k hl hk ih =>
    intro X P' a q' g w
    have hb : IsPullback (pullback.fst k g) (pullback.snd k g) k g := IsPullback.of_hasPullback k g
    let m : P' ⟶ pullback k g := pullback.lift (a ≫ l) q' (by rw [Category.assoc]; exact w.w)
    have hm : q' = m ≫ pullback.snd k g := (pullback.lift_snd _ _ _).symm
    have ht : IsPullback a m l (pullback.fst k g) := by
      refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm hb
      rw [← hm]; exact w
    rw [hm]
    exact IterLine.comp m _ (IsLine.bc hl ht) (ih hb)

theorem IterBC_of : IterBC := by
  intro P S X q g hq
  exact iterLine_of_isPullback hq (IsPullback.of_hasPullback g q).flip

end LateralTheory.E.IterBCPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineExPf

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev 𝒜 := MvPolynomial.homogeneousSubmodule (Fin 2) ℤ

lemma zero_surj : Function.Surjective (algebraMap ℤ (𝒜 0)) := by
  rintro ⟨x, hx⟩
  refine ⟨AddMonoidAlgebra.coeff x 0, ?_⟩
  apply Subtype.ext
  have h : MvPolynomial.IsHomogeneous x 0 := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hx
  by_cases h0 : x = 0
  · subst h0; simp
  · have := h.totalDegree h0
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at this
    change ((algebraMap ℤ (𝒜 0) _ : 𝒜 0) : MvPolynomial (Fin 2) ℤ) = x
    refine Eq.trans ?_ this.symm
    simp
    rfl

instance ft : Algebra.FiniteType (𝒜 0) (MvPolynomial (Fin 2) ℤ) :=
  Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝒜 0) (MvPolynomial (Fin 2) ℤ)

lemma proj_proper : IsProper (Proj.toSpecZero 𝒜) := inferInstance

lemma projective_line_over_integers_isProper : IsProper (terminal.from P1) := by
  have h1 : IsProper (Proj.toSpecZero 𝒜) := proj_proper
  have h2 : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝒜 0)))) :=
    IsClosedImmersion.spec_of_surjective _ zero_surj
  have e : terminal.from P1 = Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝒜 0))) ≫
      terminal.from (Spec (CommRingCat.of ℤ)) := terminal.hom_ext _ _
  have : IsIso (terminal.from (Spec (CommRingCat.of ℤ))) :=
    ⟨⟨specZIsTerminal.from _, specZIsTerminal.hom_ext _ _, terminal.hom_ext _ _⟩⟩
  have h3 : IsProper (terminal.from (Spec (CommRingCat.of ℤ))) := by
    have : IsClosedImmersion (terminal.from (Spec (CommRingCat.of ℤ))) := inferInstance
    infer_instance
  have h2' : IsProper (Spec.map (CommRingCat.ofHom (algebraMap ℤ (𝒜 0)))) := inferInstance
  rw [e]
  exact MorphismProperty.comp_mem @IsProper _ _ h1 (MorphismProperty.comp_mem @IsProper _ _ h2' h3)

theorem LineEx_of : LateralTheory.E.ChowLCut.LineEx := by
  intro S
  refine ⟨pullback (terminal.from P1) (terminal.from S), pullback.snd _ _, ?_, pullback.fst _ _,
    IsPullback.of_hasPullback _ _⟩
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) projective_line_over_integers_isProper

end LateralTheory.E.LineExPf

end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.ZarIndPf

namespace LateralTheory.E.InjStepPf

def TwoStep : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i n : ℤ,
  (∀ U : S.Opens, IsCompact (U : Set S) → Bij q i (n - 1) f p U) →
  ∀ (U V W : S.Opens) (hV : V ≤ U) (hW : W ≤ U), IsCompact (V : Set S) → IsCompact (W : Set S) →
  ∀ x : Ht q (sch.obj (overO p U)) n i, pull _ (sch.map (fO f p U)) _ _ x = 0 →
  pull _ (sch.map (resO p hV)) _ _ x = 0 → pull _ (sch.map (resO p hW)) _ _ x = 0 →
  pull _ (sch.map (resO p (sup_le hV hW))) _ _ x = 0

def EmptyH : Prop := Hyp → ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (U : S.Opens), (U : Set S) = ∅ →
  ∀ (i n : ℤ) (x : Ht q (sch.obj (overO p U)) n i), x = 0

variable {X S : Scheme.{0}}

theorem resO_comp (p : X ⟶ S) {V W U : S.Opens} (h1 : V ≤ W) (h2 : W ≤ U) :
    resO p h1 ≫ resO p h2 = resO p (h1.trans h2) := by
  apply pullback.hom_ext <;> simp only [resO, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc, pullback.lift_snd_assoc, Scheme.homOfLE_homOfLE, Category.comp_id]

theorem resO_refl (p : X ⟶ S) (U : S.Opens) : resO p (le_refl U) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [resO]

theorem dies_mono {q : ℕ} {i n : ℤ} (p : X ⟶ S) {V W U : S.Opens} (h1 : V ≤ W) (h2 : W ≤ U)
    (x : Ht q (sch.obj (overO p U)) n i) (hx : pull _ (sch.map (resO p h2)) _ _ x = 0) :
    pull _ (sch.map (resO p (h1.trans h2))) _ _ x = 0 := by
  rw [← resO_comp p h1 h2, Functor.map_comp, pull_comp, hx, map_zero]

def OverMV : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (i m : ℤ) (V W : S.Opens),
  ∃ (δX : Ht q (sch.obj (overO p (V ⊓ W))) m i →+ Ht q (sch.obj (overO p (V ⊔ W))) (m + 1) i)
    (δY : Ht q (sch.obj (overO (f ≫ p) (V ⊓ W))) m i →+ Ht q (sch.obj (overO (f ≫ p) (V ⊔ W))) (m + 1) i),
  (∀ x, pull _ (sch.map (resO p (le_sup_left : V ≤ V ⊔ W))) _ _ x = 0 →
      pull _ (sch.map (resO p (le_sup_right : W ≤ V ⊔ W))) _ _ x = 0 → ∃ w, δX w = x) ∧
  (∀ a b, δX (pull _ (sch.map (resO p (inf_le_left : V ⊓ W ≤ V))) _ _ a -
      pull _ (sch.map (resO p (inf_le_right : V ⊓ W ≤ W))) _ _ b) = 0) ∧
  (∀ w, δY w = 0 → ∃ a b, w = pull _ (sch.map (resO (f ≫ p) (inf_le_left : V ⊓ W ≤ V))) _ _ a -
      pull _ (sch.map (resO (f ≫ p) (inf_le_right : V ⊓ W ≤ W))) _ _ b) ∧
  ∀ w, δY (pull _ (sch.map (fO f p (V ⊓ W))) _ _ w) = pull _ (sch.map (fO f p (V ⊔ W))) _ _ (δX w)

theorem fO_res {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO (f ≫ p) h ≫ fO f p U = fO f p V ≫ resO p h := by
  apply pullback.hom_ext <;> simp only [resO, fO, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
    pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id, Category.id_comp]

theorem pull_fO_res {q : ℕ} {i n : ℤ} {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U)
    (x : Ht q (sch.obj (overO p U)) n i) :
    pull _ (sch.map (fO f p V)) _ _ (pull _ (sch.map (resO p h)) _ _ x) =
      pull _ (sch.map (resO (f ≫ p) h)) _ _ (pull _ (sch.map (fO f p U)) _ _ x) := by
  rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, fO_res]

theorem pull_res_res {q : ℕ} {i n : ℤ} (p : X ⟶ S) {V W U : S.Opens} (h1 : V ≤ W) (h2 : W ≤ U)
    (x : Ht q (sch.obj (overO p U)) n i) :
    pull _ (sch.map (resO p h1)) _ _ (pull _ (sch.map (resO p h2)) _ _ x) = pull _ (sch.map (resO p (h1.trans h2))) _ _ x := by
  rw [← pull_comp, ← Functor.map_comp, resO_comp]

theorem TwoStep_of (hO : OverMV) : TwoStep := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hb U V W hV hW hVc hWc x hx hdV hdW
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have hb' : ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i m f p U := by simpa using hb
  obtain ⟨δX, δY, e1, e2, e3, e4⟩ := hO hM hH q f p i m V W
  set x' := pull _ (sch.map (resO p (sup_le hV hW))) _ _ x with hx'
  have d1 : pull _ (sch.map (resO p (le_sup_left : V ≤ V ⊔ W))) _ _ x' = 0 := by
    rw [hx', pull_res_res]; exact hdV
  have d2 : pull _ (sch.map (resO p (le_sup_right : W ≤ V ⊔ W))) _ _ x' = 0 := by
    rw [hx', pull_res_res]; exact hdW
  obtain ⟨w, hw⟩ := e1 x' d1 d2
  have fx' : pull _ (sch.map (fO f p (V ⊔ W))) _ _ x' = 0 := by
    rw [hx', pull_fO_res, hx, map_zero]
  have hδ : δY (pull _ (sch.map (fO f p (V ⊓ W))) _ _ w) = 0 := by rw [e4, hw, fx']
  obtain ⟨a', b', hab⟩ := e3 _ hδ
  obtain ⟨a, rfl⟩ := (hb' V hVc).2 a'
  obtain ⟨b, rfl⟩ := (hb' W hWc).2 b'
  have hI : IsCompact ((V ⊓ W : S.Opens) : Set S) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ V.isOpen hVc W.isOpen hWc
  have hw2 : w = pull _ (sch.map (resO p (inf_le_left : V ⊓ W ≤ V))) _ _ a -
      pull _ (sch.map (resO p (inf_le_right : V ⊓ W ≤ W))) _ _ b := by
    apply (hb' _ hI).1
    rw [hab, map_sub, pull_fO_res, pull_fO_res]
  rw [← hw, hw2, e2]

theorem InjStep_of (hT : TwoStep) (hE : EmptyH) : InjStep := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hg hb U hU
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_cases hne : (U : Set S) = ∅
  · exact hE hH q p U hne i n x
  obtain ⟨s0, hs0⟩ := Set.nonempty_iff_ne_empty.2 hne

  have loc : ∀ s ∈ (U : Set S), ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ IsCompact (V : Set S) ∧
      pull _ (sch.map (resO p h)) _ _ x = 0 := by
    intro s hs
    obtain ⟨V, hVU, hsV, hd⟩ := (hg s).1 U hs x hx
    obtain ⟨V', hV'B, hsV', hV'V⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens) hsV
    exact ⟨V', hV'V.trans hVU, hsV', IsAffineOpen.isCompact hV'B, dies_mono p hV'V hVU x hd⟩
  let P : Set S → Prop := fun T => ∃ (V : S.Opens) (h : V ≤ U), T ⊆ V ∧ IsCompact (V : Set S) ∧
      pull _ (sch.map (resO p h)) _ _ x = 0
  have hP : P (U : Set S) := by
    refine hU.induction_on (p := P) ?_ ?_ ?_ ?_
    · obtain ⟨V, h, _, hc, hd⟩ := loc s0 hs0
      exact ⟨V, h, Set.empty_subset _, hc, hd⟩
    · intro s t hst ⟨V, h, htV, hc, hd⟩
      exact ⟨V, h, hst.trans htV, hc, hd⟩
    · intro s t ⟨V, h, hsV, hc, hd⟩ ⟨W, h', htW, hc', hd'⟩
      refine ⟨V ⊔ W, sup_le h h', ?_, ?_, hT hM hH q f p hq i n hb U V W h h' hc hc' x hx hd hd'⟩
      · exact Set.union_subset_union hsV htW
      · simpa using hc.union hc'
    · intro s hs
      obtain ⟨V, h, hsV, hc, hd⟩ := loc s hs
      exact ⟨V, mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds hsV), V, h, subset_rfl, hc, hd⟩
  obtain ⟨V, h, hUV, _, hd⟩ := hP
  have hVU : V = U := le_antisymm h hUV
  subst hVU
  simpa [resO_refl, pull_id] using hd

end LateralTheory.E.InjStepPf
end
end

section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.RelNormPf

open AlgebraicGeometry.Scheme.Hom in
theorem closedAt_preimage {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g]
    (U : S.Opens) (hU : IsAffineOpen U) : ClosedAt g.toNormalization (g.fromNormalization ⁻¹ᵁ U) := by
  intro b hb
  letI := (g.app U).hom.toAlgebra
  have hle : g ⁻¹ᵁ U ≤ g.toNormalization ⁻¹ᵁ g.fromNormalization ⁻¹ᵁ U := by
    simp [← Scheme.Hom.comp_preimage]
  have hle' : g.toNormalization ⁻¹ᵁ g.fromNormalization ⁻¹ᵁ U ≤ g ⁻¹ᵁ U := by
    simp [← Scheme.Hom.comp_preimage]
  set ρ := Z.presheaf.map (homOfLE hle).op with hρ
  have key := g.normalizationObjIso_hom_val hU
  have hρinj : Function.Injective ρ := by
    intro u v huv
    have := congrArg (Z.presheaf.map (homOfLE hle').op) huv
    have h1 : (homOfLE hle).op ≫ (homOfLE hle').op = 𝟙 (Opposite.op (g.toNormalization ⁻¹ᵁ g.fromNormalization ⁻¹ᵁ U)) :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    simpa [hρ, ← CommRingCat.comp_apply, ← Functor.map_comp, h1] using this

  have hint : IsIntegral (integralClosure Γ(S, U) Γ(Z, g ⁻¹ᵁ U)) (ρ b) := by
    obtain ⟨p, hm, hp⟩ := hb
    refine ⟨p.map (g.normalizationObjIso hU).hom.hom, hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (integralClosure Γ(S, U) Γ(Z, g ⁻¹ᵁ U)) Γ(Z, g ⁻¹ᵁ U)).comp
        (g.normalizationObjIso hU).hom.hom = ρ.hom.comp (g.toNormalization.app _).hom := by
      have := congrArg CommRingCat.Hom.hom key
      rw [Scheme.Hom.appLE] at this
      exact this
    rw [e, ← Polynomial.hom_eval₂, hp, map_zero]
  have hmem : ρ b ∈ (⊥ : Subalgebra (integralClosure Γ(S, U) Γ(Z, g ⁻¹ᵁ U)) Γ(Z, g ⁻¹ᵁ U)) := by
    rw [← integralClosure_idem]; exact hint
  obtain ⟨z, hz⟩ := Algebra.mem_bot.mp hmem
  refine ⟨(g.normalizationObjIso hU).inv z, hρinj ?_⟩
  have := congrArg (fun φ => φ ((g.normalizationObjIso hU).inv z)) (congrArg CommRingCat.Hom.hom key)
  simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply] at this
  rw [← this, ← hz]
  simp

end LateralTheory.E.RelNormPf
end
end
