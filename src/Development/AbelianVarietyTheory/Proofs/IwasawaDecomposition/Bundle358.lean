module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Formalism.LocalToGlobal.Columns.Bundle010
public import Formalism.LocalToGlobal.Columns.RecLevelLocP
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle337
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TC.FvChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hform_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E) (x y : Fin a → E) :
    hform σ (J.reindex (finCongr h) (finCongr h)) (fun j => x ((finCongr h).symm j))
      (fun j => y ((finCongr h).symm j)) = hform σ J x y := by
  subst h
  simp [hform]

theorem mem_latS_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E)
    (Lb : Submodule (𝓞 E) (Fin a → E)) (w : HeightOneSpectrum (𝓞 F)) (t : Fin a → E ⊗[F] w.adicCompletion F)
    (ht : t ∈ latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J Lb))) :
    (fun j => t ((finCongr h).symm j)) ∈ latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet σ (J.reindex (finCongr h) (finCongr h)) (reL h Lb))) := by
  subst h
  have hL : reL rfl Lb = Lb := by
    ext x
    simp [reL, reV]
  simpa [hL] using ht

theorem reGL_solve {a b : ℕ} (h : a = b) (w : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (g' : GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hg' : g' = reGL h _ g) (t : Fin a → E ⊗[F] w.adicCompletion F) (z : Fin a → E)
    (ht : (bc (prV (E := E) w) g).1 *ᵥ t = fun j => inclE (F := F) (w.adicCompletion F) (z j)) :
    ((bc (prV (E := E) w) g')⁻¹).1 *ᵥ
      (fun j => inclE (F := F) (w.adicCompletion F) (z ((finCongr h).symm j))) =
      fun j => t ((finCongr h).symm j) := by
  subst h hg'
  have hg : reGL rfl _ g = g := by
    ext
    simp [reGL]
  simp only [hg, finCongr_refl, Equiv.refl_symm, Equiv.refl_apply]
  rw [← ht, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

end GlobalTheory.Mem.Col2.TC.FvChart

namespace GlobalTheory.Mem.Col2.TC.FvChart

theorem crdN_mem_LdG (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i)
    (z : Formalism.L2.Herm.Ld D u i c) : crdN D i hi z.1 ∈ LdG D i hi (clsCrd D u i hi c) := by
  apply Submodule.subset_span
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  have h2 := hform_reindex (rankN D i hi) (sigD D : D.host.E →+* D.host.E) (D.sp.X i).gram
    (Formalism.L2.Herm.crd (D.sp.X i) y) (Formalism.L2.Herm.crd (D.sp.X i) z.1)
  have h3 := Formalism.L2.Herm.hT_crd D.sp.cm (D.sp.X i) y z.1
  have hz := z.2
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hz
  obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hz y hy)
  refine ⟨r, ?_⟩
  change _ = hform (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
    (fun j => Formalism.L2.Herm.crd (D.sp.X i) y ((finCongr (rankN D i hi)).symm j))
    (fun j => Formalism.L2.Herm.crd (D.sp.X i) z.1 ((finCongr (rankN D i hi)).symm j))
  unfold gramN
  rw [h2]
  rw [hr]
  exact h3

end GlobalTheory.Mem.Col2.TC.FvChart

namespace GlobalTheory.Mem.Col2.TC.FvChart

theorem exists_reindex_hom {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {a b : ℕ} (h : a = b) (σ : E →+* E) (J : Matrix (Fin a) (Fin a) E) (J' : Matrix (Fin b) (Fin b) E)
    (hJ : J' = J.reindex (finCongr h) (finCongr h))
    (Lb : Submodule (𝓞 E) (Fin a → E)) (Lb' : Submodule (𝓞 E) (Fin b → E)) (hL : Lb' = reL h Lb)
    (w : HeightOneSpectrum (𝓞 F)) :
    ∃ tr : latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J Lb)) →+
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet σ J' Lb')),
      ∀ t, (tr t).1 = fun j => t.1 ((finCongr h).symm j) := by
  subst hJ hL
  exact ⟨{ toFun := fun t => ⟨fun j => t.1 ((finCongr h).symm j), mem_latS_reindex h σ J Lb w t.1 t.2⟩
           map_zero' := rfl
           map_add' := fun _ _ => rfl }, fun _ => rfl⟩

end GlobalTheory.Mem.Col2.TC.FvChart

namespace GlobalTheory.Mem.Col2.TC.FvChart



theorem fvTie_of_car {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) (hH : CarH H F) (hT : CarT H F A)
    (u : D.what₂.Word) (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (v : (D.mem u).A.vT) (β : H.Ch u i) :
    Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb
      (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => D.clsLat u i c.1) (H.vT u v).1 ((D.mem u).A.Fv v)
      (fun c z => (D.fm u).fv i v c.1 ((A u).pr i v c.1 z))) := by
  have hc := hH.carC u i h1 h2 β
  have hw : (H.vT u v).1 = ((F u).atT.eV v).1 := congrArg (fun e => (e v).1) (hH.eV u).symm
  suffices hs : ∀ w, w = ((F u).atT.eV v).1 →
      Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb
        (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => D.clsLat u i c.1) w ((D.mem u).A.Fv v)
        (fun c z => (D.fm u).fv i v c.1 ((A u).pr i v c.1 z))) from hs _ hw
  intro w hw'
  subst hw'
  obtain ⟨tr, htr⟩ := exists_reindex_hom (F := D.host.F) (rankN D i (le_of_succ_m h2))
    (sigD D : D.host.E →+* D.host.E) (D.sp.X i).gram (gramN D i (le_of_succ_m h2)) rfl
    (H.lev u i h1 (le_of_succ_m h2) β).Lb ((F u).ch i h1 h2 β).lev.Lb hc.Lb_eq ((F u).atT.eV v).1
  refine ⟨⟨((F u).fMeC i h1 h2 β v).toAddMonoidHom.comp
    ((((F u).ch i h1 h2 β).lev.fT ((F u).atT.eV v).1 ((F u).atT.eV v).2).toAddMonoidHom.comp tr), ?_⟩⟩
  intro c z t ht
  have hmem := crdN_mem_LdG D u i (le_of_succ_m h2) c.1 z
  have hp := hT.prC u i h1 h2 v c.1 z ⟨_, hmem⟩ rfl
  refine (congrArg ((D.fm u).fv i v c.1) hp).symm.trans ?_
  have key : ((bc (prV (E := D.host.E) ((F u).atT.eV v).1) (((F u).ch i h1 h2 β).y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := D.host.F) (((F u).atT.eV v).1.adicCompletion D.host.F)
        (crdN D i (le_of_succ_m h2) z.1 a)) = (tr t).1 :=
    (reGL_solve (rankN D i (le_of_succ_m h2)) ((F u).atT.eV v).1 ((H.cls u i h1 (le_of_succ_m h2) β).y c).1
      (((F u).ch i h1 h2 β).y c).1 (hc.y_eq c) t.1 (Formalism.L2.Herm.crd (D.sp.X i) z.1) ht).trans (htr t).symm
  have hz := (congrArg (fun x => x ∈ latS (F := D.host.F) (((F u).atT.eV v).1.adicCompletion D.host.F)
    (intV D.host.E ((F u).atT.eV v).1)
    (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E)
      (gramN D i (le_of_succ_m h2)) ((F u).ch i h1 h2 β).lev.Lb))) key).mpr (tr t).2
  refine ((F u).fvC i h1 h2 v β c ⟨_, hmem⟩ hz).trans ?_
  exact congrArg (fun x => ((F u).fMeC i h1 h2 β v)
    ((((F u).ch i h1 h2 β).lev.fT ((F u).atT.eV v).1 ((F u).atT.eV v).2) x)) (Subtype.ext key)

end GlobalTheory.Mem.Col2.TC.FvChart



theorem GlobalTheory.Mem.Col2.TC.fvTie_charts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u i), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (H.lev u i h1 (le_of_succ_m h2) β).Lb (H.cls u i h1 (le_of_succ_m h2) β).y (fun c => (I.rec7 l Z).clsLat u i c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv i v c.1 ((A u).pr i v c.1 z))) := by
  intro B X I _ _ l Z H F A _ hH hT u i h1 h2 v β
  exact FvChart.fvTie_of_car H F A hH hT u i h1 h2 v β
end

section

noncomputable section

namespace GlobalTheory.Mem.Df

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2

attribute [local instance] GlobalTheory.Mem.Col2.starE



theorem inner_eq_of_norm_sq {K V E M : Type} [Field K] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [AddCommGroup M] [Module K M] (σ : K →+* ℂ) (j : M →ₛₗ[σ] V) (hspan : Submodule.span ℂ (Set.range j) = ⊤) (k : K)
    (hk : (σ k).im ≠ 0) (e : V →ₗ[ℂ] E) (q : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hn : ∀ m, ((‖e (j m)‖ ^ 2 : ℝ) : ℂ) = q (j m) (j m))
    (y y' : V) : inner ℂ (e y) (e y') = q y y' := by
  let D : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun y y' => inner ℂ (e y) (e y') - q y y')
    (fun y z y' => by simp only [map_add (f := _), inner_add_left, LinearMap.add_apply]; ring)
    (fun c y y' => by simp only [map_smul, inner_smul_left, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun y y' z => by simp only [map_add (f := _), inner_add_right]; ring)
    (fun c y y' => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]; ring)
  have hDapp : ∀ y y', D y y' = inner ℂ (e y) (e y') - q y y' := fun y y' => rfl
  have h0 : ∀ m, D (j m) (j m) = 0 := by
    intro m
    rw [hDapp, ← hn m, inner_self_eq_norm_sq_to_K]
    simp
  have hsym : ∀ m m', D (j m) (j m') + D (j m') (j m) = 0 := by
    intro m m'
    have h := h0 (m + m')
    simp only [map_add (f := _), LinearMap.add_apply, h0 m, h0 m'] at h
    linear_combination h
  have hpair : ∀ m m', D (j m) (j m') = 0 := by
    intro m m'
    have h1 := hsym m (k • m')
    rw [j.map_smulₛₗ, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
    have h2 := hsym m m'
    have h3 : (σ k - starRingEnd ℂ (σ k)) * D (j m) (j m') = 0 := by linear_combination h1 - starRingEnd ℂ (σ k) * h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exfalso
      rw [Complex.sub_conj] at h4
      simp [hk] at h4
    · exact h4
  have h1 : ∀ m, D (j m) = 0 := fun m => LinearMap.ext_on_range hspan fun m' => by rw [hpair m m']; rfl
  have hall : D = 0 := LinearMap.ext_on_range hspan fun m => by rw [h1 m]; rfl
  have h := congrArg (fun D : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ => D y y') hall
  simp only [hDapp, LinearMap.zero_apply] at h
  exact sub_eq_zero.1 h

theorem exists_embLL_im_ne {B : Base} (hX : B.fields.Ok) : ∃ k : B.LL, (B.embLL k).im ≠ 0 := by
  have hc : (InfinitePlace.mk (B.embLL : B.fields.K →+* ℂ)).IsComplex := hX.cplxK.isComplex _
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at hc
  by_contra hne
  push_neg at hne
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hne x)

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def cjPol (ι : Type) (n : ℕ) : Pol ℂ ι n →ₗ⋆[ℂ] Pol ℂ ι n where
  toFun p := MvPolynomial.map (starRingEnd ℂ) p
  map_add' p q := map_add _ p q
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, RingHom.id_apply]

theorem map_conj_smul {ι : Type} {n : ℕ} (r : ℂ) (p : Pol ℂ ι n) :
    MvPolynomial.map (starRingEnd ℂ) (r • p) = starRingEnd ℂ r • MvPolynomial.map (starRingEnd ℂ) p :=
  (cjPol ι n).map_smulₛₗ r p

abbrev rowS (a : I.ι) : GSD B.fields.K := mtildeGSD (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps

theorem rowS_ok (hX : B.fields.Ok) (a : I.ι) : (rowS I a).Ok :=
  mtildeOk (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) hX I.Ps

def cTerm (a : I.ι) (c : (rowS I a).Cl) (F G : MtCx I a) : ℂ :=
  ((Nat.card (@MulAction.stabilizer (rowS I a).G (rowS I a).D _ (rowS I a).actD ((rowS I a).outSec.rep c)) : ℕ) : ℂ)⁻¹ *
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 ((rowS I a).outSec.rep c))) (G.1 ((rowS I a).outSec.rep c))

theorem cTerm_add_left (a : I.ι) (c : (rowS I a).Cl) (F F' G : MtCx I a) :
    cTerm I a c (F + F') G = cTerm I a c F G + cTerm I a c F' G := by
  simp only [cTerm, Submodule.coe_add, Pi.add_apply, map_add (f := _), LinearMap.add_apply, mul_add]

theorem cTerm_smul_left (a : I.ι) (c : (rowS I a).Cl) (r : ℂ) (F G : MtCx I a) :
    cTerm I a c (r • F) G = starRingEnd ℂ r * cTerm I a c F G := by
  simp only [cTerm, SetLike.val_smul, Pi.smul_apply, map_conj_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem cTerm_add_right (a : I.ι) (c : (rowS I a).Cl) (F G G' : MtCx I a) :
    cTerm I a c F (G + G') = cTerm I a c F G + cTerm I a c F G' := by
  simp only [cTerm, Submodule.coe_add, Pi.add_apply, map_add (f := _), mul_add]

theorem cTerm_smul_right (a : I.ι) (c : (rowS I a).Cl) (r : ℂ) (F G : MtCx I a) :
    cTerm I a c F (r • G) = r * cTerm I a c F G := by
  simp only [cTerm, SetLike.val_smul, Pi.smul_apply, map_smul, smul_eq_mul]
  ring

def cSum (hX : B.fields.Ok) (a : I.ι) : MtCx I a →ₗ⋆[ℂ] MtCx I a →ₗ[ℂ] ℂ :=
  letI := (rowS_ok I hX a).fintypeCl
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun F G => ∑ c : (rowS I a).Cl, cTerm I a c F G)
    (fun F F' G => by simp only [cTerm_add_left, Finset.sum_add_distrib])
    (fun r F G => by simp only [cTerm_smul_left, Finset.mul_sum, smul_eq_mul])
    (fun F G G' => by simp only [cTerm_add_right, Finset.sum_add_distrib])
    (fun r F G => by simp only [cTerm_smul_right, Finset.mul_sum, smul_eq_mul, RingHom.id_apply])

theorem cSum_apply (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a) :
    cSum I hX a F G = letI := (rowS_ok I hX a).fintypeCl; ∑ c : (rowS I a).Cl, cTerm I a c F G := rfl

end GlobalTheory.Mem.Df

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.TC
open scoped TensorProduct

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem reL_refl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  simp only [reL, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem reGL_refl {a : ℕ} (R : Type) [CommRing R] (g : GL (Fin a) R) : reGL (rfl : a = a) R g = g := by
  ext i j
  simp [reGL]

theorem fvTie_of_coords (hc : CMData F E) (S : HSpace E) {cls : Type}
    (y : cls → Formalism.L2.Herm.UAf hc S) (lat : cls → Submodule (𝓞 E) S.V)
    (w : HeightOneSpectrum (𝓞 F)) (k : Type) [AddCommGroup k]
    (fz : ∀ c, Formalism.HermitianLatticesTheory.dual S.hT (lat c) → k)
    (Lb : Submodule (𝓞 E) (Fin S.rank → E)) {b : ℕ} (h : S.rank = b)
    (J : Matrix (Fin b) (Fin b) E) (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    (Lb' : Submodule (𝓞 E) (Fin b → E)) (hL : Lb' = reL h Lb)
    (y' : cls → GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (hy : ∀ c, y' c = reGL h _ (y c).1)
    (fT : latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J Lb')) →+ k)
    (hfv : ∀ c (z : Formalism.HermitianLatticesTheory.dual S.hT (lat c))
      (hz : ((bc (prV (E := E) w) (y' c))⁻¹).1 *ᵥ
          (fun a => inclE (F := F) (w.adicCompletion F) (reV h E (Formalism.L2.Herm.crd S z.1) a)) ∈
        latS (F := F) (w.adicCompletion F) (intV E w)
          (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J Lb'))),
      fz c z = fT ⟨_, hz⟩) :
    Nonempty (Formalism.L2.Herm.FvTie hc S Lb y lat w k fz) := by
  subst h
  obtain rfl : J = S.gram := by rw [hJ]; ext i j; simp
  obtain rfl : Lb' = Lb := hL.trans (reL_refl Lb)
  obtain rfl : y' = fun c => (y c).1 := funext fun c => (hy c).trans (reGL_refl _ _)
  refine ⟨⟨fT, fun c z t ht => ?_⟩⟩
  have ht' : ((bc (prV (E := E) w) (y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) = t.1 := by
    have e : (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) =
        fun a => inclE (F := F) (w.adicCompletion F) (Formalism.L2.Herm.crd S z.1 a) := rfl
    rw [e, ← ht, Matrix.mulVec_mulVec]
    simp
  have hz : ((bc (prV (E := E) w) (y c).1)⁻¹).1 *ᵥ
      (fun a => inclE (F := F) (w.adicCompletion F) (reV (rfl : S.rank = S.rank) E (Formalism.L2.Herm.crd S z.1) a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w)
        (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) S.gram Lb')) := by
    rw [ht']; exact t.2
  rw [hfv c z hz]
  exact congrArg fT (Subtype.ext ht')

theorem hform_reindex {a b : ℕ} (h : a = b) (σ : E →+* E) (G : Matrix (Fin a) (Fin a) E) (x y : Fin a → E) :
    hform σ (G.reindex (finCongr h) (finCongr h)) (reV h E x) (reV h E y) = hform σ G x y := by
  subst h
  have e : (G.reindex (finCongr (rfl : a = a)) (finCongr (rfl : a = a))) = G := by ext i j; simp
  rw [e]; rfl

end Generic

theorem crdN_mem_Ld {D : D7} (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i)
    (z : Formalism.L2.Herm.Ld D u i c) : crdN D i hi z.1 ∈ Ld D u i hi c := by
  refine Submodule.subset_span ?_
  intro x hx
  obtain ⟨x0, hx0, rfl⟩ := hx
  have h1 : (D.sp.X i).hT x0 z.1 ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    have := z.2
    simp only [Formalism.L2.Herm.Ld, Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf] at this
    exact this x0 hx0
  rw [Formalism.L2.Herm.hT_crd D.sp.cm] at h1
  have h2 := hform_reindex (rankN D i hi) (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.X i).gram
    (Formalism.L2.Herm.crd _ x0) (Formalism.L2.Herm.crd _ z.1)
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 h1
  exact ⟨r, hr.trans h2.symm⟩



theorem fvTie_top {D : D7} (H : Formalism.L2.Herm.HermColsCh D) (F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u))
    (A : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u)) (hH : CarH H F) (hT : CarT H F A) (u : D.what₂.Word)
    (h1 : 1 ≤ D.R.m) (v : (D.mem u).A.vT) (β : H.Ch u D.R.m) :
    Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X D.R.m) (H.lev u D.R.m h1 le_rfl β).Lb (H.cls u D.R.m h1 le_rfl β).y
      (fun c => D.clsLat u D.R.m c.1) (H.vT u v).1 ((D.mem u).A.Fv v)
      (fun c z => (D.fm u).fv D.R.m v c.1 ((A u).pr D.R.m v c.1 z))) := by
  obtain rfl : β = chM H u := @Subsingleton.elim _ (@Unique.instSubsingleton _ (H.Ch_m u).some) _ _
  have key : ∀ w, w = ((F u).atT.eV v).1 →
      Nonempty (Formalism.L2.Herm.FvTie D.sp.cm (D.sp.X D.R.m) (H.lev u D.R.m h1 le_rfl (chM H u)).Lb
        (H.cls u D.R.m h1 le_rfl (chM H u)).y (fun c => D.clsLat u D.R.m c.1) w ((D.mem u).A.Fv v)
        (fun c z => (D.fm u).fv D.R.m v c.1 ((A u).pr D.R.m v c.1 z))) := by
    intro w hw
    subst hw
    have hc := hH.carM u
    refine fvTie_of_coords D.sp.cm (D.sp.X D.R.m) _ _ _ _ _ _ (rankN D D.R.m le_rfl) (gramN D D.R.m le_rfl) rfl
      ((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.Lb hc.Lb_eq
      (fun c => (((F u).cls D.R.m le_rfl (Or.inr rfl)).y c.1).1) (fun c => hc.y_eq c.1)
      (((F u).fMe D.R.m le_rfl (Or.inr rfl) v).toAddMonoidHom.comp
        (((F u).cls D.R.m le_rfl (Or.inr rfl)).lev.fT _ ((F u).atT.eV v).2).toAddMonoidHom) ?_
    intro c z hz
    have hz' := crdN_mem_Ld u D.R.m le_rfl c.1 z
    have e1 := (F u).fv D.R.m le_rfl (Or.inr rfl) v c.1 ⟨_, hz'⟩ hz
    have e2 := hT.pr u D.R.m le_rfl v c.1 z ⟨_, hz'⟩ rfl
    exact (congrArg (fun p => (D.fm u).fv D.R.m v c.1 p) e2.symm).trans e1
  exact key _ (by rw [hH.eV u])



theorem fvTie_chart_top : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (h1 : 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u (I.rec7 l Z).R.m), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (H.lev u (I.rec7 l Z).R.m h1 le_rfl β).Lb (H.cls u (I.rec7 l Z).R.m h1 le_rfl β).y (fun c => (I.rec7 l Z).clsLat u (I.rec7 l Z).R.m c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv (I.rec7 l Z).R.m v c.1 ((A u).pr (I.rec7 l Z).R.m v c.1 z))) := by
  intro B X I _ _ l Z H F A _ hH hT u h1 v β
  exact fvTie_top H F A hH hT u h1 v β

end GlobalTheory.Mem.Col2.TC
end
end

section

noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne

def RowWD.unram (D : D7) (m : D.what₂.FT → PlE D.host → Multiset ℂ) (h0 : ∀ σ w, (0:ℂ) ∉ m σ w)
    (hc : ∀ σ w, Multiset.card (m σ w) = D.R.r) : RowWD D where
  par σ w := WD.lpUnr (D.nd.plOm.2 w) (m σ w)
  sat := m
  dim σ w := (WD.lpUnr_spec (h := D.nd.plOm.2 w) (m σ w) (h0 σ w)).2.2.trans (hc σ w)
  tame σ k v :=
    let w := D.naut.plGw k v
    WD.tame_of_unr (WD.lpUnr_spec (h := D.nd.plOm.2 w) (m σ w) (h0 σ w)).1

end GlobalTheory.HeightCounting
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt

noncomputable def pvPlace {D : D7} {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) :
    HeightOneSpectrum (𝓞 D.host.E) where
  asIdeal := A.Pv v
  isPrime := inferInstance
  ne_bot := by
    intro h
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (A.eV v).1.ne_bot
    have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ A.Pv v := (A.res_v v x).1 hx
    rw [h, Ideal.mem_bot] at h1
    exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E) (by simpa using h1))

theorem pvPlace_isOver {D : D7} {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) :
    IsOver (A.eV v).1 (pvPlace A v) := by
  ext x
  exact A.res_v v x

theorem eq_Pv_or_conj {D : D7} {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT)
    (q : HeightOneSpectrum (𝓞 D.host.E)) (hq : q.under (𝓞 D.host.F) = (A.eV v).1) :
    q.asIdeal = A.Pv v ∨ q.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) (A.Pv v) := by
  have hov : IsOver (A.eV v).1 q := by
    rw [← hq]
    rfl
  rcases rll_over_cases D.sp.cm (pvPlace_isOver A v) hov with e | e
  · exact Or.inl (congrArg HeightOneSpectrum.asIdeal e)
  · refine Or.inr ?_
    have h1 := conjIdeal_asIdeal (pvPlace A v)
    rw [e, ← h1]
    rfl

theorem primes_over_level_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u v (q : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)), q.under (𝓞 (I.rec7 l Z).host.F) = ((F u).atT.eV v).1 → q.asIdeal = (F u).atT.Pv v ∨ q.asIdeal = Formalism.HermitianLatticesTheory.conjIdeal (K := (I.rec7 l Z).host.E) ((F u).atT.Pv v) :=
  fun _ _ _ _ _ _ F _ _ u v q hq => eq_Pv_or_conj (F u).atT v q hq

end GlobalTheory.Mem.Col2.HAt
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.exists_admissible_localComponent_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (w : HeightOneSpectrum (𝓞 E)), ∃ σ : SmIrr (locU n w), IsAdmissible σ.ρ ∧ IsCompAlong π.V (locU n w) (MonoidHom.id _) σ.ρ := by
  first | exact @GlobalTheory.DefU.LocAdm.exists_admissible_comp | exact GlobalTheory.DefU.LocAdm.exists_admissible_comp | (intros; apply GlobalTheory.DefU.LocAdm.exists_admissible_comp <;> assumption)
end
