module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle286
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle036
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle042
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle194
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle296
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Formalism.LocalToGlobal.GlobalTheory.GL6.PRLocV
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle295
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle030
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g g' : ℕ} {X' X : Data E r}

theorem perFr_castFr (h : SameSp X' X) (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X (castFr h.psi x) v τ i = perFr X' x v τ i := by
  cases X; cases X'
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  dsimp only at h1 h2 h3 h4 h5
  subst h1 h2 h3
  rfl

noncomputable def renum (q : Fin g' ≃ Fin g) : (Fin g → ℂ) ≃L[ℂ] (Fin g' → ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ q).toContinuousLinearEquiv

theorem renum_apply (q : Fin g' ≃ Fin g) (z : Fin g → ℂ) (j : Fin g') : renum q z j = z (q j) := rfl

theorem hx_renum (h : SameSp X' X) {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} {idx' : Fin g' ≃ X'.Ψ × Fin r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} (hs' : IsSympl X' bas') (hs : IsSympl X bas)
    {x : Frame X'.Ψ r} (hxd : x ∈ X'.dom) (q : Fin g' ≃ Fin g)
    (hpv : ∀ v, renum q (pv X idx (castFr h.psi x) v) = pv X' idx' x v) (z w : Fin g → ℂ) :
    hx X bas idx (castFr h.psi x) z w = hx X' bas' idx' x (renum q z) (renum q w) := by
  have hx1 := h.castFr_mem_dom hxd
  have him' := (hx_laws E r X' g' bas' idx' 0 hs' Even.zero x hxd).2.2.1
  have him := (hx_laws E r X g bas idx 0 hs Even.zero _ hx1).2.2.1
  refine sub_eq_zero.1 (form_eq_zero_of_im
    (fun z w => hx X bas idx (castFr h.psi x) z w - hx X' bas' idx' x (renum q z) (renum q w))
    (fun w => ⟨fun u v => ?_, fun c u => ?_⟩) (fun z => ⟨fun u v => ?_, fun c u => ?_⟩) _
    (span_range_pv idx hs hx1) ?_ z w)
  · simp only [hx, map_add (f := _), mulVec_add, add_dotProduct]; ring
  · simp only [hx, map_smul, mulVec_smul, smul_dotProduct, smul_eq_mul]; ring
  · simp only [hx, map_add (f := _), star_add, mulVec_add, dotProduct_add]; ring
  · have : renum q (c • u) = c • renum q u := rfl
    simp only [hx, this, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_sub]
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [Complex.sub_im, hpv, hpv, him, him', h.EF_eq, sub_self]

theorem denseRange_embR {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (n : ℕ) : DenseRange (Ker.embR X (n := n)) := by
  obtain ⟨L, hL⟩ := Ker.exists_equiv_zR X idx (n := n) hs hx
  have h := L.symm.surjective.denseRange.comp (Ker.denseRange_zR_embR X idx hs hx) L.symm.continuous
  convert h using 1
  funext y
  simp [← hL]

theorem zR_lact (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r) {n : ℕ} (γ : GL (Fin r) E) (hγ : IsUn X γ)
    (v : Ker.WR X n) :
    Ker.zR X idx (lact γ x) (fun τ k => ((γ : Matrix (Fin r) (Fin r) E).map τ.1) *ᵥ v τ k) = Ker.zR X idx x v := by
  funext k i
  have hm : mat (lact γ x) (idx i).1 =
      (γ : Matrix (Fin r) (Fin r) E).map (idx i).1.1 * mat x (idx i).1 := rfl
  rw [Ker.zR, Ker.zR, hm]
  split_ifs
  · rw [PerMove.col_mul, PerMove.hermC_unitary _ _ _ hγ]
  · have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map (idx i).1.1).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map (idx i).1.1.mapMatrix)
    rw [Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

theorem zR_renum (h : SameSp X' X) {bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ} {idx' : Fin g' ≃ X'.Ψ × Fin r}
    {idx : Fin g ≃ X.Ψ × Fin r} (hs' : IsSympl X' bas')
    {x : Frame X'.Ψ r} (hxd : x ∈ X'.dom) (q : Fin g' ≃ Fin g)
    (hpv : ∀ v, renum q (pv X idx (castFr h.psi x) v) = pv X' idx' x v) {n : ℕ} (v : Ker.WR X' n) (k : Fin n) :
    renum q (Ker.zR X idx (castFr h.psi x) (fun τ => v ⟨τ.1, h.psi.ge τ.2⟩) k) = Ker.zR X' idx' x v k := by
  refine (denseRange_embR idx' hs' hxd n).induction_on (p := fun v : Ker.WR X' n =>
    renum q (Ker.zR X idx (castFr h.psi x) (fun τ => v ⟨τ.1, h.psi.ge τ.2⟩) k) = Ker.zR X' idx' x v k) v
    (isClosed_eq ?_ ?_) (fun y => hpv (y k))
  · have := (Ker.zRLin X idx (castFr h.psi x) (n := n)).continuous_of_finiteDimensional
    have h2 : Continuous fun (v : Ker.WR X' n) (τ : X.Ψ) => v ⟨τ.1, h.psi.ge τ.2⟩ :=
      continuous_pi fun τ => continuous_apply _
    have h3 := (continuous_apply k).comp (this.comp h2)
    exact (renum q).continuous.comp h3
  · exact (continuous_apply k).comp (Ker.zRLin X' idx' x (n := n)).continuous_of_finiteDimensional

end SlopeTestRemainingChoices

theorem anFib_move_renum : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r g g' : ℕ) (X' X : Data D.host.E r) (hX : SameSp X' X) (bas' : (Fin g' ⊕ Fin g' → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g' ≃ X'.Ψ × Fin r) (e' : Fin g' ≃ Lt1 Dw) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw), IsSympl X' bas' → IsSympl X bas → Matched c σ X' idx' e' → Matched c σ X idx e → ∀ x ∈ X'.dom, ∀ L : Lt D.host.E r, SelfD X' L → ∀ ga : GL (Fin r) D.host.E, IsUn X ga → letI : Algebra c.F ℂ := σ.toAlgebra; ∀ (y : FrPt Xo c ℂ) (A' : AnFib X' bas' idx' e' x L y) (th' : (Fin g' → ℂ) → ℂ), A'.Reads 1 y.s th' → ∃ (A : AnFib X bas idx e (lact ga (castFr hX.psi x)) (mapL ga L) y) (th : (Fin g → ℂ) → ℂ), A.Reads 1 y.s th ∧ (∀ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), A'.Marked mk → A.Marked (mvMap ga mk)) ∧ ∀ (n : ℕ) (v' : GlobalTheory.Ker.WR X' n) (v : GlobalTheory.Ker.WR X n), (∀ (τ : X'.Ψ) (k : Fin n), v ⟨τ.1, hX.psi ▸ τ.2⟩ k = ((ga : Matrix (Fin r) (Fin r) D.host.E).map τ.1) *ᵥ v' τ k) → GlobalTheory.Ker.gaussR X bas idx (lact ga (castFr hX.psi x)) (GlobalTheory.Ker.zR X idx (lact ga (castFr hX.psi x)) v) * ∏ b, th (GlobalTheory.Ker.zR X idx (lact ga (castFr hX.psi x)) v b) = GlobalTheory.Ker.gaussR X' bas' idx' x (GlobalTheory.Ker.zR X' idx' x v') * ∏ b, th' (GlobalTheory.Ker.zR X' idx' x v' b) := by
  intro D H Dw l Xo c σ r g g' X' X h bas' idx' e' bas idx e hs' hs hm' hm x hxd L hL ga hga
  letI : Algebra c.F ℂ := σ.toAlgebra
  intro y A th' hth
  let q : Fin g' ≃ Fin g := e'.trans e.symm
  have hq (j) : e (q j) = e' j := e.apply_symm_apply _
  have hpv (v) : renum q (pv X idx (castFr h.psi x) v) = pv X' idx' x v := by
    funext j
    rw [renum_apply, hm.1, hm'.1, hq, perFr_castFr h]
  have hty (j) : rowType X (idx (q j)) = rowType X' (idx' j) := by rw [hm.2, hm'.2, hq]
  have hx1 := h.castFr_mem_dom hxd
  obtain ⟨-, -, -, -, -, -, -, hinv⟩ := hx_laws _ r X g bas idx 0 hs Even.zero _ hx1
  obtain ⟨hdom, hpv2, -, hhx2⟩ := hinv ga hga
  have hhx (z w) : hx X bas idx (lact ga (castFr h.psi x)) z w = hx X' bas' idx' x (renum q z) (renum q w) := by
    rw [hhx2, hx_renum h hs' hs hxd q hpv]
  have hp (v) : renum q (pv X idx (lact ga (castFr h.psi x)) (Lev.lin ga v)) = pv X' idx' x v :=
    (congrArg (renum q) (hpv2 v)).trans (hpv v)
  have hp' (v) : renum q (pv X idx (lact ga (castFr h.psi x)) v) = pv X' idx' x (Lev.lin ga⁻¹ v) := by
    rw [← hp, Lev.lin_inv']
  have hlat (z) : (∃ v ∈ L, renum q z = pv X' idx' x v) ↔
      ∃ v ∈ mapL ga L, z = pv X idx (lact ga (castFr h.psi x)) v :=
    ⟨fun ⟨v, hv, hz⟩ => ⟨Lev.lin ga v, ⟨v, hv, rfl⟩, (renum q).injective (hz.trans (hp v).symm)⟩,
      fun ⟨v, hv, hz⟩ => ⟨_, Lev.mem_mapL.1 hv, (congrArg (renum q) hz).trans (hp' v)⟩⟩
  refine ⟨
    { ex := fun z => A.ex (renum q z)
      ex_add := fun z w => by rw [map_add (f := _), A.ex_add]
      ex_onto := A.ex_onto.comp (renum q).surjective
      ex_ker := fun z => (A.ex_ker _).trans (hlat z)
      ex_lin := fun a z => by
        rw [← A.ex_lin]
        congr 1
        funext j
        simp only [renum_apply, hty]
      hol := fun U f => ?_
      der := fun ℓ => ⟨?_, fun U hU f => ?_⟩
      fr := fun j z => A.fr j (renum q z)
      fr_hol := fun j => (A.fr_hol j).comp (renum q).differentiableOn fun z hz => hz
      fr_ne := fun j z => A.fr_ne j _
      fr_g := fun j j' z => A.fr_g j j' _
      fr_0 := fun j => by rw [map_zero]; exact A.fr_0 j
      χ := fun v => A.χ (Lev.lin ga⁻¹ v)
      χ_norm := fun v hv => A.χ_norm _ (Lev.mem_mapL.1 hv)
      fr_per := fun v hv j z hz => by
        rw [hhx, hhx, map_add (f := _), hp']; exact A.fr_per _ (Lev.mem_mapL.1 hv) j _ hz },
    fun z => th' (renum q z), fun j z => hth j (renum q z), fun mk hk a ha => ?_, fun n v' v hv => ?_⟩
  · exact ⟨(A.hol U f).1.preimage (renum q).continuous,
      (A.hol U f).2.comp (renum q).differentiableOn fun z hz => hz⟩
  · simpa only [map_zero] using (A.der ℓ).1
  · rw [(A.der ℓ).2 U hU f]
    have h1 := (renum q).comp_right_fderiv (f := fun z => ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (A.ex z).left U f) (x := 0)
    have h2 : renum q (Pi.single (e.symm ℓ) 1) = Pi.single (e'.symm ℓ) 1 := by
      funext j
      rw [renum_apply]
      have h3 : q j = e.symm ℓ ↔ j = e'.symm ℓ := by
        rw [Equiv.eq_symm_apply, Equiv.eq_symm_apply, hq]
      simp only [Pi.single_apply, h3]
    rw [← h2]
    rw [map_zero] at h1
    exact (congrArg (fun F => F (Pi.single (e.symm ℓ) 1)) h1).symm
  · rw [hk a ha, ← hp]
    change A.ex _ = A.ex _
    congr 3
    rw [Lev.lin_apply, mulVec_smul]
    rfl
  · have hv2 : v = fun τ k => ((ga : Matrix (Fin r) (Fin r) D.host.E).map τ.1) *ᵥ v' ⟨τ.1, h.psi.ge τ.2⟩ k := by
      funext τ k
      exact hv ⟨τ.1, h.psi.ge τ.2⟩ k
    have hz (k) : renum q (Ker.zR X idx (lact ga (castFr h.psi x)) v k) = Ker.zR X' idx' x v' k := by
      rw [hv2, zR_lact idx _ ga hga (fun τ => v' ⟨τ.1, h.psi.ge τ.2⟩), zR_renum h hs' hxd q hpv]
    simp only [Ker.gaussR, hhx, hz]

end GlobalTheory.OneMapRef
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.InfDecomp

theorem list_prod_map_mulSingle {ι M : Type} [DecidableEq ι] [Monoid M] (w : ι) (a : M) :
    ∀ l : List ι, l.Nodup → (l.map (Pi.mulSingle w a : ι → M)).prod = if w ∈ l then a else 1
  | [], _ => by simp
  | i :: l, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.prod_cons, list_prod_map_mulSingle w a l h.2]
    by_cases hi : i = w
    · subst hi
      simp [h.1]
    · simp [Pi.mulSingle_apply, hi, Ne.symm hi]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def cutPt (v : InfinitePlace E) (x : UA E n) : UA E n := ((embRet (n := n) v.embedding x : embU n v.embedding) : UA E n)

theorem cutPt_mem (v : InfinitePlace E) (x : UA E n) : cutPt v x ∈ embU n v.embedding := (embRet v.embedding x).2

theorem cInf_cutPt (v : InfinitePlace E) (x : UA E n) : cInf (cutPt v x) = cutGL v (cInf x) := by
  unfold cutPt
  rw [cInf_embRet, InfinitePlace.mk_embedding]


open Classical in
theorem evGL_cInf_cutPt (x : UA E n) (v w : InfinitePlace E) :
    evGL w (cInf (cutPt v x)) = (Pi.mulSingle w (evGL w (cInf x)) : InfinitePlace E → GL (Fin n) ℂ) v := by
  rw [cInf_cutPt, Pi.mulSingle_apply]
  split_ifs with h
  · subst h
    exact evGL_cutGL_self _ _
  · exact evGL_cutGL_of_ne (Ne.symm h) _

end GlobalTheory.DefU.InfDecomp

namespace GlobalTheory.DefU


open InfDecomp in
theorem infU_eq_list_prod_embU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (x : UA E n),
    x ∈ infU E n → ∃ y : InfinitePlace E → UA E n, (∀ v, y v ∈ embU n v.embedding) ∧
      (∀ v, cEmb v.embedding (y v) = cEmb v.embedding x) ∧ (Finset.univ.toList.map y).prod = x := by
  intro E _ _ _ n x hx
  classical
  refine ⟨fun v => cutPt v x, fun v => cutPt_mem v x, fun v => ?_, ?_⟩
  · change GeneralLinearGroup.map (coord v.embedding) (cInf (cutPt v x)) =
      GeneralLinearGroup.map (coord v.embedding) (cInf x)
    rw [cInf_cutPt, coord_embedding]
    exact evGL_cutGL_self v (cInf x)
  · refine Subtype.ext (ga_ext ?_ ?_)
    · change cInf (Finset.univ.toList.map fun v => cutPt v x).prod = cInf x
      rw [map_list_prod, List.map_map]
      refine gl_ext_evGL fun w => ?_
      rw [map_list_prod, List.map_map]
      have e : (evGL w ∘ cInf ∘ fun v : InfinitePlace E => cutPt v x) =
          (Pi.mulSingle w (evGL w (cInf x)) : InfinitePlace E → GL (Fin n) ℂ) := funext fun v => evGL_cInf_cutPt x v w
      rw [e, list_prod_map_mulSingle w _ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ w))]
    · let ψ : UA E n →* GL (Fin n) (Af E) := (GeneralLinearGroup.map (pFin E)).comp (UA E n).subtype
      change ψ (Finset.univ.toList.map fun v => cutPt v x).prod = ψ x
      rw [MonoidHom.mem_ker.1 hx, map_list_prod, List.map_map]
      refine List.prod_eq_one fun g hg => ?_
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hg
      exact MonoidHom.mem_ker.1 (cutPt_mem v x).1

end GlobalTheory.DefU

end
end

section

noncomputable section

namespace GlobalTheory.LevelHecke.MovePair

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem pairOf_act {R V k W W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]
    [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W'] (res : R →+* k) (M M' : Submodule R V)
    (pr : M →+ W) (pr' : M' →+ W') (φ : Module.Dual k W) (φ' : Module.Dual k W')
    (hs : ∀ (a : R) z, pr (a • z) = res a • pr z) (hs' : ∀ (a : R) z, pr' (a • z) = res a • pr' z)
    (g : V ≃ₗ[R] V) (a : k)
    (h1 : ∀ z ∈ M', ∃ s, res s ≠ 0 ∧ s • g z ∈ M)
    (h2 : ∀ z, g z ∈ M → ∃ s, res s ≠ 0 ∧ s • z ∈ M')
    (h3 : ∀ z (hz : z ∈ M') (hg : g z ∈ M), φ' (pr' ⟨z, hz⟩) = a * φ (pr ⟨g z, hg⟩)) :
    (pairOf res M' pr' φ').act g = (pairOf res M pr φ).dil a := by
  have key : ∀ z, z ∈ loc res M' ↔ g z ∈ loc res M := by
    intro z
    constructor
    · intro hz
      obtain ⟨s, hs0, h⟩ := (mem_loc _ _ _).1 hz
      refine loc_sat res M s _ hs0 ?_
      rw [← map_smul]
      exact (mem_loc _ _ _).2 (h1 _ h)
    · intro hz
      obtain ⟨s, hs0, h⟩ := (mem_loc _ _ _).1 hz
      rw [← map_smul] at h
      exact loc_sat res M' s _ hs0 ((mem_loc _ _ _).2 (h2 _ h))
  ext x
  · rw [Pr.mem_act]
    show g.symm x ∈ loc res M' ↔ x ∈ loc res M
    rw [key, g.apply_symm_apply]
  · obtain ⟨z, rfl⟩ := g.surjective x
    show φ' (locExt res M' pr' (g.symm (g z))) = a * φ (locExt res M pr (g z))
    rw [g.symm_apply_apply]
    by_cases hz : z ∈ loc res M'
    · have hz' := (key z).1 hz
      obtain ⟨s, hs0, h⟩ := (mem_loc _ _ _).1 hz
      obtain ⟨t, ht0, h'⟩ := (mem_loc _ _ _).1 hz'
      have e1 : (t * s) • z ∈ M' := by rw [mul_smul]; exact M'.smul_mem _ h
      have e2 : (t * s) • g z ∈ M := by rw [mul_comm, mul_smul]; exact M.smul_mem _ h'
      have e3 : g ((t * s) • z) ∈ M := by rw [map_smul]; exact e2
      have hne : res (t * s) ≠ 0 := by rw [map_mul]; exact mul_ne_zero ht0 hs0
      have e4 := h3 _ e1 e3
      have e5 : (⟨g ((t * s) • z), e3⟩ : M) = ⟨(t * s) • g z, e2⟩ := Subtype.ext (map_smul _ _ _)
      rw [e5, locExt_spec res M' pr' hs' z hz _ e1, locExt_spec res M pr hs _ hz' _ e2, map_smul, map_smul,
        smul_eq_mul, smul_eq_mul] at e4
      apply mul_left_cancel₀ hne
      rw [e4]; ring
    · rw [locExt_off _ _ _ _ hz, locExt_off _ _ _ _ (fun h => hz ((key z).2 h)), map_zero, map_zero, mul_zero]

theorem mov_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (z : Fin n → E) :
    (bc (prV (E := E) v) (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y')).1 *ᵥ
      (((bc (prV (E := E) v) y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a))) =
    ((bc (prV (E := E) v) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) ((γ.1 *ᵥ z) a)) := by
  have e : (fun a => inclE (F := F) (v.adicCompletion F) ((γ.1 *ᵥ z) a)) =
      (γ.1.map (inclE (F := F) (v.adicCompletion F))) *ᵥ (fun a => inclE (F := F) (v.adicCompletion F) (z a)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ _
  rw [e, mulVec_mulVec, ← Units.val_mul, map_mul, mul_inv_cancel_right, map_mul, map_inv, Units.val_mul,
    ← mulVec_mulVec]
  rfl

theorem mulsF_apply {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal) (a : ℤ)
    (h : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hM : MulsF S v hv a h) {k : Type} [Ring k] (φ : S.fM v hv ≃+ k)
    (x x' : Fin n → E ⊗[F] v.adicCompletion F) (e : h.1 *ᵥ x = x') :
    (x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) ↔
      x' ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) ∧
    ∀ hx hx', φ (S.fT v hv ⟨x, hx⟩) = (a : k) * φ (S.fT v hv ⟨x', hx'⟩) := by
  subst e
  obtain ⟨hg, hf⟩ := hM
  refine ⟨hg x, fun hx hx' => ?_⟩
  rw [← hf ⟨x, hx⟩, map_zsmul, zsmul_eq_mul]

section Tied

variable {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m}

theorem ld_lattice (c : (D.mem u).C.cls i) : Submodule.IsLattice D.host.E (Ld D u i hi c) := by
  letI := D.host.cmStar
  let φ := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)
  letI : Submodule.IsLattice D.host.E (clsCrd D u i hi c) := bwB_clsCrd_lat D u i hi c
  have hL : Submodule.IsFullLattice D.host.E (clsCrd D u i hi c) := by
    constructor
    change Submodule.span D.host.E (((D.clsLat u i c).map
      (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤
    rw [show Submodule.span D.host.E (((D.clsLat u i c).map
        (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
        (Submodule.span D.host.E (D.clsLat u i c : Set _)).map φ.toLinearMap by
          rw [Submodule.map_span]; rfl,
      (D.clsLat_lat u i c).span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.surjective
  obtain ⟨d, hd, hle⟩ := LocB.dual_le_bnd (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (bwB_gramN_det D i hi) _ hL
  exact Submodule.IsLattice.of_fg D.host.E (LocB.fg_of_le_bnd hd hle)




theorem ld_loc (K : ClsTied u i hi) (v : HeightOneSpectrum (𝓞 D.host.F)) (c : (D.mem u).C.cls i)
    (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Ld D u i hi c) ↔
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ x ∈ dualV K v := by
  let φ := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)
  letI : Submodule.IsLattice D.host.E (clsCrd D u i hi c) := bwB_clsCrd_lat D u i hi c
  have hL : Submodule.IsFullLattice D.host.E (clsCrd D u i hi c) := by
    constructor
    change Submodule.span D.host.E (((D.clsLat u i c).map
      (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤
    rw [show Submodule.span D.host.E (((D.clsLat u i c).map
        (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
        (Submodule.span D.host.E (D.clsLat u i c : Set _)).map φ.toLinearMap by
          rw [Submodule.map_span]; rfl,
      (D.clsLat_lat u i c).span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.surjective
  letI : Submodule.IsLattice D.host.E K.lev.Lb :=
    Submodule.IsLattice.of_fg D.host.E (Module.Finite.iff_fg.1 K.lev.Lb_fin)
  have hLb : Submodule.IsFullLattice D.host.E K.lev.Lb := ⟨K.lev.Lb_span⟩
  refine GlobalTheory.T.unitary_completion_maps_dualLattices D.host.F D.host.E (sigD D) _ (gramN D i hi) v (clsCrd D u i hi c) K.lev.Lb
    (bc (prV (E := D.host.E) v) (K.y c).1) (bwB_gramN_det D i hi) hL hLb
    (Formalism.UG.P.afsplit_bc_mem _ _ _ _ (K.y c).2) (fun x => ?_) x
  rw [← map_inv]
  exact rlv_yloc v (K.y c).1 (K.y_lat c) x

end Tied




theorem pc_act_of_mulsF : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → ∀ (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E) (a : ℤ), MulsF K.lev (A.eV v).1 (A.eV v).2 a (mov K (A.eV v).1 c γ c') → (pc P v c').act (glE γ) = (pc P v c).dil (a : (D.mem u).A.Fv v) := by
  intro D u A i hi P K fMe hT v c c' γ a hM
  have hin : ∀ c (z : Fin (D.R.N i) → D.host.E), z ∈ Ld D u i hi c →
      ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z a)) ∈ dualV K (A.eV v).1 :=
    fun c z hz => (ld_loc K _ c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)
  have hout : ∀ c (z : Fin (D.R.N i) → D.host.E),
      ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z a)) ∈ dualV K (A.eV v).1 →
      ∃ s, A.res v s ≠ 0 ∧ s • z ∈ Ld D u i hi c := by
    intro c z hz
    obtain ⟨r, hr, h⟩ := GlobalTheory.T.exists_smul_mem_lattice_of_mem_completion D.host.F D.host.E (A.eV v).1 _ _ (ld_lattice c) z ((ld_loc K _ c _).2 hz)
    exact ⟨_, fun h0 => hr ((A.res_v v r).2 h0), h⟩
  have hst := fun z => mulsF_apply K.lev _ _ a _ hM (fMe v) _ _
    (mov_mulVec (A.eV v).1 (K.y c).1 (K.y c').1 γ z)
  refine pairOf_act _ _ _ _ _ _ _ (P.pr_smul v c) (P.pr_smul v c') (glE γ) _
    (fun z hz => hout c (γ.1 *ᵥ z) ((hst z).1.1 (hin c' z hz)))
    (fun z hz => hout c' z ((hst z).1.2 (hin c (γ.1 *ᵥ z) hz))) (fun z hz hz' => ?_)
  · have hz2 : γ.1 *ᵥ z ∈ Ld D u i hi c := hz'
    have hT' : ∀ c (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi c), (D.fm u).fv i v c (P.pr v c ⟨z, hz⟩) =
        fMe v (K.lev.fT (A.eV v).1 (A.eV v).2 ⟨_, hin c z hz⟩) := fun c z hz => hT v c ⟨z, hz⟩ (hin c z hz)
    have e1 := hT' c' z hz
    have e2 := hT' c _ hz2
    exact e1.trans (((hst z).2 _ _).trans (congrArg (fun t => (a : (D.mem u).A.Fv v) * t) e2.symm))

end GlobalTheory.LevelHecke.MovePair

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ), ∃ e : embU n τ ≃ₜ* Matrix.unitaryGroup (Fin n) ℂ, ∀ x : embU n τ, GlobalTheory.Branching.unitaryIncl n (e x) = cEmb τ (x : UA E n) := by
  first | exact @GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup | exact GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup | (intros; apply GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.commute_unitaryArchimedeanPoints_distinct_places : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ τ' : E →+* ℂ), InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → ∀ x ∈ embU n τ, ∀ y ∈ embU n τ', Commute x y := by
  first | exact @GlobalTheory.UnitaryBC.embU_commute | exact GlobalTheory.UnitaryBC.embU_commute | (intros; apply GlobalTheory.UnitaryBC.embU_commute <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

theorem _root_.GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)), ∃ r : UA E n →* locU n w, Continuous r ∧ (∀ x : locU n w, r x = x) ∧ ∀ (g : UA E n) (y : locU n w), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) := by
  first | exact @GlobalTheory.DefU.LocRet.exists_ret | exact GlobalTheory.DefU.LocRet.exists_ret | (intros; apply GlobalTheory.DefU.LocRet.exists_ret <;> assumption)
end
