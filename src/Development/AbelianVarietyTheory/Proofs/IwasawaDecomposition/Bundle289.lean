module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle202
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle259
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle258
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle278
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle187
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle296
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegreeRootDiscrBoundKummerFieldOfPowerIdealRoots
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.Mem.GJInhab

open Formalism.BasicNotions NumberField IsDedekindDomain

def baseVol (B : Base) (cd : CDHaar) (W : @HSpace B.host.E _ _ B.host.cmStar) : ℝ :=
  letI := B.host.cmStar
  GlobalTheory.Mem.Vol.trueVol B.sp.cm (fun τ : Tau B.R => B.host.emb τ.1) cd W

theorem baseVol_pos (B : Base) (cd : CDHaar) (W : @HSpace B.host.E _ _ B.host.cmStar) : 0 < baseVol B cd W :=
  letI := B.host.cmStar
  GlobalTheory.Mem.Vol.trueVol_pos B.sp.cm (fun τ : Tau B.R => B.host.emb τ.1) cd W

def noJet {R : Ranks} (H : Host R) : ThetaJet R H where
  Sit := Empty
  loc := fun i => i.elim
  l_inert := fun i => i.elim
  jOf := fun i => i.elim
  j_mem := fun i => i.elim
  N0_eq := fun i => i.elim
  N1_eq_exponentN1 := fun i => i.elim
  Sit1 := Empty
  loc1 := fun i => i.elim
  l_inert1 := fun i => i.elim
  j1Of := fun i => i.elim
  firstJetIndex_mem_range := fun i => i.elim
  firstJet_lowerRank_eq := fun i => i.elim
  firstJet_upperRank_eq := fun i => i.elim

def oneJet {R : Ranks} (H : Host R) (hm : 1 ≤ R.m) (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l)
    (hc : H.cls l = .signal ∨ H.cls l = .inertClass) : ThetaJet R H where
  Sit := Unit
  loc := fun _ =>
    haveI : Fact l.Prime := ⟨hl⟩
    { l := l
      five_le_l := h5
      d := 2
      d_even := even_two
      two_le_d := le_rfl
      N0 := R.N 0
      N1 := R.N 1
      Th := 1 }
  l_inert := fun _ => hc
  jOf := fun _ => 1
  j_mem := fun _ => ⟨le_rfl, hm⟩
  N0_eq := fun _ => rfl
  N1_eq_exponentN1 := fun _ => rfl
  Sit1 := Empty
  loc1 := fun i => i.elim
  l_inert1 := fun i => i.elim
  j1Of := fun i => i.elim
  firstJetIndex_mem_range := fun i => i.elim
  firstJet_lowerRank_eq := fun i => i.elim
  firstJet_upperRank_eq := fun i => i.elim

theorem exists_noJet (B : Base) (C : Cols B) (cd : CDHaar) :
    ∃ J : GJStage B C, J.cd = cd ∧ J.vol = baseVol B J.cd ∧ J.jet = noJet B.host ∧
      ∀ u w h, (J.gat u w h).FinClasses := by
  obtain ⟨J, hv, hcd, hj, -, hf⟩ := GJModel.exists_of_jet B C (baseVol B cd) (baseVol_pos B cd) cd
    (noJet B.host) (GJModel.gxOne B) (fun i => i.elim) (fun i => i.elim)
  exact ⟨J, hcd, by rw [hv, hcd], hj, hf⟩

theorem exists_oneJet (B : Base) (C : Cols B) (cd : CDHaar) (hm : 1 ≤ B.R.m) (u : B.Word)
    (h0 : Nonempty ((C.mem u).C.cls 0)) (h1 : Nonempty ((C.mem u).C.cls 1))
    (l : ℕ) (hl : l.Prime) (h5 : 5 ≤ l) (hc : B.host.cls l = .signal ∨ B.host.cls l = .inertClass) :
    ∃ J : GJStage B C, J.cd = cd ∧ J.vol = baseVol B J.cd ∧ J.jet = oneJet B.host hm l hl h5 hc ∧
      (∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 ∧
        B.places.resChar (J.jetW i) = l) ∧
      ∀ u w h, (J.gat u w h).FinClasses := by
  obtain ⟨J, hv, hcd, hj, -, hf⟩ := GJModel.exists_of_jet B C (baseVol B cd) (baseVol_pos B cd) cd
    (oneJet B.host hm l hl h5 hc) (GJModel.gxOne B) (fun _ => ⟨u, h0, h1⟩) (fun i => i.elim)
  have key : ∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 := by
    rw [hj]
    exact ⟨(), rfl, rfl, rfl⟩
  obtain ⟨i, hi1, hil, hid⟩ := key
  exact ⟨J, hcd, by rw [hv, hcd], hj, ⟨i, hi1, hil, hid, (J.jetW_l i).trans hil⟩, hf⟩

theorem nonempty_stage (B : Base) (C : Cols B) : Nonempty (GJStage B C) := by
  obtain ⟨cd⟩ := GlobalTheory.T.nonempty_compactDualHaar
  obtain ⟨J, -⟩ := exists_noJet B C cd
  exact ⟨J⟩

theorem inhabited_stage (B : Base) (C : Cols B) :
    (∃ J : GJStage B C, J.vol = baseVol B J.cd) ∧
    (1 ≤ B.R.m → Nonempty ((C.mem B.u₀).C.cls 0) → Nonempty ((C.mem B.u₀).C.cls 1) →
      ∀ l : ℕ, l.Prime → 5 ≤ l → (B.host.cls l = .signal ∨ B.host.cls l = .inertClass) →
        ∃ J : GJStage B C, J.vol = baseVol B J.cd ∧ Nonempty J.jet.Sit ∧
          ∃ i : J.jet.Sit, J.jet.jOf i = 1 ∧ (J.jet.loc i).l = l ∧ (J.jet.loc i).d = 2 ∧
            B.places.resChar (J.jetW i) = l) ∧
    (Nonempty ((C.mem B.u₀).C.cls 0) → Nonempty ((C.mem B.u₀).C.cls 1) →
      ∃ J : GJStage B C, J.vol = baseVol B J.cd ∧ Nonempty J.jet.Sit) := by
  obtain ⟨cd⟩ := GlobalTheory.T.nonempty_compactDualHaar
  refine ⟨?_, fun hm h0 h1 l hl h5 hc => ?_, fun h0 h1 => ?_⟩
  · obtain ⟨J, -, hv, -⟩ := exists_noJet B C cd
    exact ⟨J, hv⟩
  · obtain ⟨J, -, hv, -, ⟨i, hi⟩, -⟩ := exists_oneJet B C cd hm B.u₀ h0 h1 l hl h5 hc
    exact ⟨J, hv, ⟨i⟩, i, hi⟩
  · obtain ⟨l, hl, h5, hc⟩ := GJModel.exists_inert B.host
    have hm := B.R.two_le_m
    obtain ⟨J, -, hv, -, ⟨i, -⟩, -⟩ := exists_oneJet B C cd (by omega) B.u₀ h0 h1 l hl h5 hc
    exact ⟨J, hv, ⟨i⟩⟩

end GlobalTheory.Mem.GJInhab

end
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

theorem _root_.GlobalTheory.T.base_fields_definite_laws : ∀ B : Base, B.fields.AbelianUnramifiedExtensionConditions ∧ B.fields.f = B.R.f := by
  first | exact @GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws | exact GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws | (intros; apply GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws <;> assumption)
end

section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem.DatLaws


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.Mem.DatLaws.dat_ok : ∀ (B : _root_.GlobalTheory.Mem.Base)
    (X : _root_.GlobalTheory.Mem.PreX B.toPre)
    (Ch : _root_.Formalism.L2.Col.Chars B.fields (B.primes X) B.R.m),
    Ch.Ok → Ch.FromHecke B.wts B.embLL →
      (B.dat X Ch).Ok := by
  intro B X Ch hCh hH
  constructor
  case fields => exact _root_.GlobalTheory.Mem.FieldsLaws.fields_ok B
  case fieldsConditions => exact (_root_.GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1
  case embeddingStarConj => exact _root_.GlobalTheory.Mem.Base.baseData_embedding_conj B X Ch
  case f_eq => exact (_root_.GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).2
  case primes => exact (_root_.GlobalTheory.BasePrimes.primes_ok B X).1
  case piG_cong => exact (_root_.GlobalTheory.BasePrimes.primes_ok B X).2
  case cond => exact _root_.GlobalTheory.Mem.Base.fields_isCond B X
  case chars => exact hCh
  case hecke => exact hH
  case wts => exact _root_.GlobalTheory.Mem.Base.wts_isOk B
  case e_even => exact _root_.GlobalTheory.Mem.Base.dat_e_even B X Ch
  case sizes => exact _root_.GlobalTheory.Mem.Base.primes_sizes B X

end GlobalTheory.Mem.DatLaws
end

section

noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem linearIndependent_semilinear_of_basis {K : Type} [Field K] (e : K →+* ℂ) {V : Type} [AddCommGroup V]
    [Module K V] {W : Type} [AddCommGroup W] [Module ℂ W] (j : V →ₛₗ[e] W) {ι κ : Type}
    (b : Module.Basis ι K V) (hb : LinearIndependent ℂ (fun i => j (b i))) (v : κ → V)
    (hv : LinearIndependent K v) : LinearIndependent ℂ (fun i => j (v i)) := by
  classical
  set S : Submodule ℂ W := Submodule.span ℂ (Set.range fun i => j (b i)) with hS
  have hmem : ∀ x, j x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact S.add_mem hy hz
    | smul a y _ hy => rw [map_smulₛₗ]; exact S.smul_mem _ hy
  let j' : V →ₛₗ[e] S := j.codRestrict S hmem
  have h1 : LinearIndependent ℂ (fun i => j' (b i)) :=
    LinearIndependent.of_comp S.subtype hb
  have h2 : Submodule.span ℂ (Set.range fun i => j' (b i)) = ⊤ := by
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    rfl
  let b' := Module.Basis.extend (hv.linearIndepOn_id)
  have h3 := (GlobalTheory.semilinear_basis_image_indep_of_basis K e V S j' ι _ b b' ⟨h1, h2⟩).1
  have h4 := h3.map' S.subtype S.ker_subtype
  let f : κ → (hv.linearIndepOn_id).extend (Set.subset_univ _) := fun i =>
    ⟨v i, (hv.linearIndepOn_id).subset_extend _ ⟨i, rfl⟩⟩
  have hf : Function.Injective f := fun a c h => hv.injective (congrArg Subtype.val h)
  have h5 := h4.comp f hf
  have h6 : (fun i => j (v i)) = (⇑S.subtype ∘ fun i => j' (b' i)) ∘ f := by
    funext i
    simp [b', f, j', Module.Basis.extend_apply_self]
  rw [h6]
  exact h5

def coordForm {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (c : Fin n → W) : (Fin n → K) →ₛₗ[e] W where
  toFun x := ∑ i, e (x i) • c i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, mul_smul]

theorem coordForm_basisFun {K : Type} [Field K] (e : K →+* ℂ) {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (c : Fin n → W) (i : Fin n) : coordForm e c (Pi.basisFun K (Fin n) i) = c i := by
  classical
  show ∑ k, e (Pi.basisFun K (Fin n) i k) • c k = c i
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [hk]
  · simp

def ramForm {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) :
    (C.fm u).ramSub →ₛₗ[B.embLL] W.Mu u where
  toFun x := (W.eMu u).symm ⟨(C.fm u).emb 0 x, x.2⟩
  map_add' x y := by
    rw [← map_add (f := _)]; congr 1; ext1; simp
  map_smul' a x := by
    rw [← map_smul]; congr 1; ext1; simp [map_smulₛₗ]

theorem eMu_ramForm {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) (x : (C.fm u).ramSub) :
    ((W.eMu u (ramForm W u x) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) =
      (C.fm u).emb 0 x := by
  show ((W.eMu u ((W.eMu u).symm _) : (C.mem u).A.Mram) : (C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) = _
  rw [LinearEquiv.apply_symm_apply]

theorem ramForm_basis {B : Base} {C : Cols B} (W : RowsRest B C) (u : B.Word) {κ : Type}
    (b : Module.Basis κ B.LL (C.fm u).ramSub) :
    LinearIndependent ℂ (fun i => ramForm W u (b i)) ∧
      Submodule.span ℂ (Set.range (fun i => ramForm W u (b i))) = ⊤ := by
  let g : W.Mu u →ₗ[ℂ] ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) :=
    (C.mem u).A.Mram.subtype ∘ₗ (W.eMu u).toLinearMap
  have hg : ∀ x, g (ramForm W u x) = (C.fm u).emb 0 x := eMu_ramForm W u
  have hginj : Function.Injective g := (C.mem u).A.Mram.injective_subtype.comp (W.eMu u).injective
  constructor
  · apply LinearIndependent.of_comp g
    have := linearIndependent_semilinear_of_basis B.embLL ((C.fm u).emb 0) ((C.fm u).lat 0).b
      ((C.fm u).emb_basis 0).1 (fun i => ((b i : (C.fm u).ramSub) : ((C.fm u).lat 0).V))
      (b.linearIndependent.map' (C.fm u).ramSub.subtype (Submodule.ker_subtype _))
    have h6 : (⇑g ∘ fun i => ramForm W u (b i)) =
        fun i => (C.fm u).emb 0 ((b i : (C.fm u).ramSub) : ((C.fm u).lat 0).V) := funext fun i => hg _
    rw [h6]
    exact this
  · set S := Submodule.span ℂ (Set.range (fun i => ramForm W u (b i))) with hS
    have hmem : ∀ x, ramForm W u x ∈ S := by
      intro x
      have hx : x ∈ Submodule.span B.LL (Set.range b) := by rw [b.span_eq]; trivial
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact S.add_mem hy hz
      | smul a y _ hy => rw [map_smulₛₗ]; exact S.smul_mem _ hy
    rw [eq_top_iff]
    intro φ _
    have h1 : g φ ∈ (C.mem u).A.Mram := (W.eMu u φ).2
    rw [← GlobalTheory.RamRational.span_ramSub_cols B C u] at h1
    have h2 : Submodule.span ℂ ((C.fm u).emb 0 '' ((C.fm u).ramSub : Set ((C.fm u).lat 0).V)) ≤ S.map g := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, hmem ⟨x, hx⟩, hg _⟩
    obtain ⟨ψ, hψ, hψ'⟩ := h2 h1
    rwa [← hginj hψ']

theorem exists_divStage (B : Base) (C : Cols B) (W : RowsRest B C) (n : ℕ) (c : Module.Basis (Fin n) ℂ W.EE)
    (Xo : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ) (hXo : ∀ v, IsUnit (Xo v).det)
    (Lr : Submodule (𝓞 B.LL) (Fin n → B.LL)) (Ln : ∀ u, Submodule (𝓞 B.LL) ((C.fm u).lat 0).V)
    (Bk : ∀ u, ((C.fm u).lat 0).V →ₗ[B.LL] Module.Dual B.LL (Fin n → B.LL)) (h : B.Word → ℝ) (etaF : ℝ) :
    ∃ (V : DivStage B C W) (e : V.div.RR.V ≃ₗ[B.LL] (Fin n → B.LL)),
      (∀ x, V.jEE x = ∑ i, B.embLL (e x i) • c i) ∧ (∀ x, x ∈ V.div.RR.L ↔ e x ∈ Lr) ∧
      (∀ v, v ≠ InfinitePlace.mk B.embLL → ∀ x, Formalism.HermitianLatticesTheory.normAt V.div.RR.b V.div.RR.X v x =
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) Xo v (e x)) ∧
      (∀ u x, x ∈ (V.div.Nu u).L ↔ V.nuIn u x ∈ Ln u) ∧
      (∀ u φ x, V.div.Bk u φ x = Bk u (V.nuIn u φ) (e x)) ∧ V.div.h = h ∧ V.div.etaF = etaF ∧
      V.div.HH = sFrame V.div.Nu V.div.h + V.div.RR.muMax := by
  classical
  obtain ⟨X0, hX0, hX0n⟩ := GlobalTheory.exists_frames_normAt_eq_norm B.LL B.embLL W.EE n c Lr
  choose m bN XN hXN hXNn using fun u : B.Word =>
    GlobalTheory.Mem.exists_restricted_frames B.LL ((C.fm u).lat 0) (C.fm u).ramSub ⊥ ((C.fm u).lat_good 0).1
  let X : InfinitePlace B.LL → Matrix (Fin n) (Fin n) ℂ := fun v =>
    if v = InfinitePlace.mk B.embLL then X0 v else Xo v
  let RR : HLat B.LL :=
    { V := Fin n → B.LL, ι := Fin n, b := Pi.basisFun B.LL (Fin n), X := X, L := Lr }
  let Nu : B.Word → HLat B.LL := fun u =>
    { V := (C.fm u).ramSub, ι := Fin (m u), b := bN u, X := XN u,
      L := (Ln u).comap ((C.fm u).ramSub.subtype.restrictScalars (𝓞 B.LL)) }
  let D : DivData B.LL B.Word :=
    { RR := RR, Nu := Nu, Bk := fun u => (Bk u) ∘ₗ (C.fm u).ramSub.subtype, h := h,
      HH := sFrame Nu h + RR.muMax, HH_ge := le_rfl, etaF := etaF, Dall := W.Dall, delP := W.delp,
      delP_le_one := W.delp_le_one }
  let V : DivStage B C W :=
    { div := D
      div_good := ⟨fun v => by
        show IsUnit (if v = InfinitePlace.mk B.embLL then X0 v else Xo v).det
        split_ifs
        · exact hX0 v
        · exact hXo v, fun u v => hXN u v⟩
      jEE := coordForm B.embLL c
      jEE_basis := by
        have : (fun i => coordForm B.embLL c (Pi.basisFun B.LL (Fin n) i)) = c :=
          funext (coordForm_basisFun B.embLL c)
        show LinearIndependent ℂ (fun i => coordForm B.embLL c (Pi.basisFun B.LL (Fin n) i)) ∧
          Submodule.span ℂ (Set.range (fun i => coordForm B.embLL c (Pi.basisFun B.LL (Fin n) i))) = ⊤
        rw [this]
        exact ⟨c.linearIndependent, c.span_eq⟩
      jN := ramForm W
      jN_basis := fun u => ramForm_basis W u (bN u)
      Dall_eq := rfl
      delP_eq := rfl
      nuIn := fun u => (C.fm u).ramSub.subtype
      nuIn_inj := fun u => (C.fm u).ramSub.injective_subtype
      nuIn_range := fun u => Submodule.range_subtype _
      nuIn_jN := fun u x => eMu_ramForm W u x
      nuIn_norm := fun u v x => hXNn u v x
      jEE_norm := fun x => by
        refine Eq.trans ?_ (hX0n x)
        show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) X _ x = _
        simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_true] }
  refine ⟨V, LinearEquiv.refl _ _, fun x => rfl, fun x => Iff.rfl, fun v hv x => ?_, fun u x => Iff.rfl,
    fun u φ x => rfl, rfl, rfl, rfl⟩
  show Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) X v x = Formalism.HermitianLatticesTheory.normAt (Pi.basisFun B.LL (Fin n)) Xo v x
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord, X, if_neg hv]

end GlobalTheory.Mem

end
end

section

open Formalism Formalism.BasicNotions

namespace GlobalTheory.Mem

theorem locStage_inhabited : Nonempty GlobalTheory.Mem.LocStage := by
  classical
  choose P AI hT using GlobalTheory.MemLoc.exists_locPrime_tied
  exact ⟨{ loc := fun l _ => P l, locA := fun l _ => AI l, locT := fun l _ => (hT l).some }⟩

end GlobalTheory.Mem
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rowIsometry_conjugatedGoodRows_finrank : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), 0 < c → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → R.models_HE → LinearMap.range eE = (R.EEat (R.levR F true)).comap R.HE.e → (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F true * ‖x‖ ^ 2) → (R.EEat (R.levR F true) ≤ R.EEat R.triv) → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) → (DallTie R F → Module.finrank ℂ (HHX X) = D.what₂.Dall) ∧ ∃ j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G, RowJ R eE X h G t j := by
  first | exact @GlobalTheory.Mem.SRe.exists_rowJ_and_finrank_HHX | exact GlobalTheory.Mem.SRe.exists_rowJ_and_finrank_HHX | (intros; apply GlobalTheory.Mem.SRe.exists_rowJ_and_finrank_HHX <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

theorem isIrreducible_sqRep (n : ℕ) (mu : DomWeight n) : (GlobalTheory.Branching.sqRep ℂ n mu).IsIrreducible := by
  have hU := GlobalTheory.Branching.isIrreducible_smallRep_unitary n mu
  obtain ⟨hn, hs⟩ := (CuspRep.isIrreducible_iff _).1 hU
  exact (CuspRep.isIrreducible_iff _).2 ⟨hn, fun S hS => hs S fun u => hS _⟩

theorem rhoK_tenMul {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (u : ∀ τ, nablaSq ℂ n (lam τ)) :
    Formalism.L2.DIV.rhoK lam g (GlobalTheory.CoefIrred.tenMul lam u) =
      GlobalTheory.CoefIrred.tenMul lam fun τ => GlobalTheory.Branching.sqRep ℂ n (lam τ) (g τ) (u τ) := by
  apply Subtype.ext
  rw [Formalism.L2.DIV.rhoK_coe, GlobalTheory.CoefIrred.tenMul_coe, GlobalTheory.CoefIrred.tenMul_coe, Formalism.L2.DIV.actTen]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem cAll_of_mem_embU {v u : InfinitePlace E} (huv : u ≠ v) {x : UA E n} (hx : x ∈ embU n v.embedding) :
    cAll x u = 1 := by
  have h := (Subgroup.mem_inf.1 hx).2
  rw [Subgroup.mem_iInf] at h
  have h2 := h u.embedding
  rw [Subgroup.mem_iInf] at h2
  exact h2 (by simpa using huv)

theorem embU_le_infU (τ : E →+* ℂ) : embU n τ ≤ infU E n := inf_le_left

theorem rep_tenMul_update [DecidableEq (InfinitePlace E)] (W : Wt E n) (v : InfinitePlace E) (x : infU E n)
    (hx : x.1 ∈ embU n v.embedding) (e : ∀ u, nablaSq ℂ n (W u)) (a : nablaSq ℂ n (W v)) :
    W.rep x (GlobalTheory.CoefIrred.tenMul W (Function.update e v a)) =
      GlobalTheory.CoefIrred.tenMul W (Function.update e v (GlobalTheory.Branching.sqRep ℂ n (W v) (cEmb v.embedding x.1) a)) := by
  change Formalism.L2.DIV.rhoK W (cAll x.1) _ = _
  rw [rhoK_tenMul]
  congr 1
  funext u
  by_cases h : u = v
  · subst h
    simp only [Function.update_self]
    rfl
  · simp only [Function.update_of_ne h, cAll_of_mem_embU h hx, map_one, Module.End.one_apply]

theorem hasWeightAt_of_finPart (π : AutSub E n) (W : Wt E n) {f : algForms W} (hf : f ∈ π.finPart W) (hf0 : f ≠ 0)
    (v : InfinitePlace E) : HasWeightAt π.V v.embedding (W v) := by
  classical
  obtain ⟨e, he⟩ : ∃ e, f.1 (GlobalTheory.CoefIrred.tenMul W e) ≠ 0 := by
    by_contra hc
    push Not at hc
    have h1 : f.1 = 0 := by
      apply (Formalism.L2.DIV.bVV ℂ W).ext
      intro i
      have hb : Formalism.L2.DIV.bVV ℂ W i = GlobalTheory.CoefIrred.tenMul W
          (fun τ => GlobalTheory.CoefIrred.ssBasis ℂ (W τ) (i τ)) := by
        apply Subtype.ext
        rw [Formalism.L2.DIV.bVV_coe, GlobalTheory.CoefIrred.tenMul_coe,
          Formalism.L2.DIV.bVVfun]
        simp only [GlobalTheory.CoefIrred.ssBasis_coe]
      rw [hb]
      exact hc _
    exact hf0 (Subtype.ext h1)
  refine ⟨isIrreducible_sqRep n (W v), f.1 ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v, fun h0 => he ?_, fun a => ?_,
    fun x a => ?_⟩
  · have := LinearMap.congr_fun h0 (e v)
    simpa [MultilinearMap.toLinearMap] using this
  · exact AutSub.mem_finPart.1 hf _
  · have hx : x.1 ∈ infU E n := embU_le_infU _ x.2
    have h2 := f.2.2 ⟨x.1, hx⟩ (GlobalTheory.CoefIrred.tenMul W (Function.update e v a))
    rw [rep_tenMul_update W v ⟨x.1, hx⟩ x.2] at h2
    exact h2

end GlobalTheory.DefU

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

theorem _root_.GlobalTheory.T.degreeRootDiscrBound_kummerFieldOfPowerIdealRoots : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ), 0 < h → Sz (kummerField φ h) (Real.log (Module.finrank ℚ E) + ((NumberField.Units.rank E + 2) * Real.log h + Real.log (classNumber E))) (Real.log |((discr E : ℤ) : ℝ)| / Module.finrank ℚ E + ((NumberField.Units.rank E + 2) * Real.log h + Real.log (classNumber E))) := by
  first | exact @GlobalTheory.FieldSize.sz_kummerField | exact GlobalTheory.FieldSize.sz_kummerField | (intros; apply GlobalTheory.FieldSize.sz_kummerField <;> assumption)
end
