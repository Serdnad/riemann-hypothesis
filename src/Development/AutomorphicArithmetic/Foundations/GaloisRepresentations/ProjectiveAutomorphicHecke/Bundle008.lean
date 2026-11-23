module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle337
import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle148
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pThLoc_of :
    UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.ThLoc := by
  intro _ hB E _ _ _ n
  obtain ⟨-, hsurj⟩ := hB E n
  refine ⟨fun w hw y => ?_, fun hn x w z hz => ?_⟩
  · have hs : sim (th (loc hw y)) = 1 := by
      rw [sim_th, sim_loc, inv_one]
    obtain ⟨u, hu⟩ := hsurj _ hs
    have hmem : u.1 ∈ locU n w := by
      refine Subgroup.mem_inf.2 ⟨u.2, Subgroup.mem_iInf.2 fun u' => Subgroup.mem_iInf.2 fun h => MonoidHom.mem_ker.2 ?_⟩
      have h1 : comp u' (ofU u) = 1 := by
        rw [hu, comp_th, comp_loc_of_apart hw h, map_one]
      exact h1
    have hw' : cLoc w u.1 = invT n _ y := by
      have h1 : comp w (ofU u) = invT n _ y := by
        rw [hu, comp_th, comp_loc]
      exact h1
    have hu' : u = locF hw (invT n _ y) := by
      have h2 : (⟨u.1, hmem⟩ : locU n w) = (locE hw).symm (invT n _ y) := by
        apply (locE hw).injective
        rw [locE_apply, (locE hw).apply_symm_apply]
        exact hw'
      exact Subtype.ext (congrArg (fun t : locU n w => t.1) h2)
    show _ = ofU (locF hw _)
    rw [← hu, hu']
  · refine guf_ext (by rw [sim_th, map_inv]) fun u => ?_
    have hsym : (comp u z).valᵀ = (comp u z).val := by
      by_cases h : SameK x (cj u) w
      · rw [((hz u).1 h), transpose_smul, transpose_one]
      · rw [((hz u).2 h), Units.val_one, transpose_one]
    rw [comp_th, map_inv]
    apply Units.ext
    rw [invT_val, Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hsym]
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.PNbhd2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem exists_open_avoid (w : Plc E) (x : GLw n w) (hx : x ≠ 1) :
    ∃ V : Subgroup (GLw n w), IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w (n := n) ∧ x ∉ V := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  by_cases hxK : x ∈ GlobalTheory.LFun.KGL w (n := n)
  swap
  · exact ⟨_, hKo, le_rfl, hxK⟩
  have hne : ∃ i j, x.val i j ≠ (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j := by
    by_contra h
    push_neg at h
    exact hx (Units.ext (Matrix.ext h))
  obtain ⟨i, j, hij⟩ := hne
  haveI : CompactSpace ↥(GlobalTheory.LFun.KGL w (n := n)) := isCompact_iff_compactSpace.1 hKc
  let f : ↥(GlobalTheory.LFun.KGL w (n := n)) → w.adicCompletion E :=
    fun g => g.1.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j
  have hf : Continuous f :=
    Continuous.sub (Continuous.matrix_elem (Units.continuous_val.comp continuous_subtype_val) i j) continuous_const
  obtain ⟨A, hA⟩ := NonarchimedeanAddGroup.is_nonarchimedean
    ({x.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j}ᶜ : Set (w.adicCompletion E))
    (isOpen_compl_singleton.mem_nhds (by simpa using (sub_ne_zero.2 hij).symm))
  have hW : IsClopen (f ⁻¹' (A : Set (w.adicCompletion E))) := A.isClopen.preimage hf
  have h1 : (1 : ↥(GlobalTheory.LFun.KGL w (n := n))) ∈ f ⁻¹' (A : Set (w.adicCompletion E)) := by
    simp [f, A.zero_mem]
  obtain ⟨H, hH⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW h1
  refine ⟨(H : Subgroup _).map (GlobalTheory.LFun.KGL w (n := n)).subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · exact hKo.isOpenEmbedding_subtypeVal.isOpenMap _ H.isOpen
  · rintro ⟨h, hh, rfl⟩
    exact hA (hH hh) rfl

private theorem exists_Kw
    (F : Finset (Σ w : Plc E, {V : Subgroup (GLw n w) // IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w (n := n)})) :
    ∃ Kw : ∀ w : Plc E, Subgroup (GLw n w), (∀ w, IsOpen (Kw w : Set (GLw n w)) ∧ Kw w ≤ GlobalTheory.LFun.KGL w (n := n)) ∧
      ∀ i ∈ F, Kw i.1 ≤ i.2.1 := by
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨fun w => GlobalTheory.LFun.KGL w (n := n),
      fun w => ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).1, le_rfl⟩, by simp⟩
  | insert i F _ ih =>
    obtain ⟨Kw, h1, h2⟩ := ih
    obtain ⟨v, V, hVo, hVK⟩ := i
    have hle : ∀ w, Function.update Kw v (Kw v ⊓ V) w ≤ Kw w := fun w => by
      by_cases h : w = v
      · subst h
        rw [Function.update_self]
        exact inf_le_left
      · rw [Function.update_of_ne h]
    refine ⟨Function.update Kw v (Kw v ⊓ V), fun w => ?_, fun j hj => ?_⟩
    · refine ⟨?_, (hle w).trans (h1 w).2⟩
      by_cases h : w = v
      · subst h
        rw [Function.update_self]
        exact (h1 w).1.inter hVo
      · rw [Function.update_of_ne h]
        exact (h1 w).1
    · rcases Finset.mem_insert.1 hj with rfl | hj
      · simp only [Function.update_self]
        exact inf_le_right
      · exact (hle j.1).trans (h2 j hj)

end UpperTheory.Gal.CertificateRingHomMap.PNbhd2

theorem UpperTheory.Gal.CertificateRingHomMap.pNbhd2_of :
    UpperTheory.Gal.CertificateRingHomMap.Nbhd2 := by
  intro E _ _ _ n O hO
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  let p : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU (E := E) (n := n)).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hfin : ∀ x : UA E n, x ∈ finU (E := E) (n := n) ↔
      finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n) := by
    intro x
    constructor
    · intro hx
      have h1 : GeneralLinearGroup.map (pInf E) (x : GA E n) = 1 := hx
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
    · intro hx
      change GeneralLinearGroup.map (pInf E) (x : GA E n) = 1
      rw [← hx, pInf_finGL]
  have hc : IsClosed ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) := by
    have e : ((finU (E := E) (n := n) : Subgroup (UA E n)) : Set (UA E n)) =
        {x : UA E n | finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)} :=
      Set.ext hfin
    rw [e]
    exact isClosed_eq (GlobalTheory.DefU.LocAdm.continuous_finGL.comp (continuous_map_pFin.comp continuous_subtype_val))
      continuous_subtype_val
  have hι : Topology.IsClosedEmbedding (fun x : finU (E := E) (n := n) => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hc.isClosedEmbedding_subtypeVal
  have hKc := GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)
  have hKo := GlobalTheory.EulerTwRestr.isOpen_Kglob (E := E) (n := n)
  have hC : IsCompact {u : finU (E := E) (n := n) | p u ∈ GlobalTheory.EulerTw.Kglob E n} :=
    IsCompact.of_isClosed_subset (hι.isCompact_preimage (hKc.image GlobalTheory.DefU.LocAdm.continuous_finGL))
      ((Subgroup.isClosed_of_isOpen _ hKo).preimage hp) fun x hx => ⟨p x, hx, (hfin x).1 x.2⟩
  have hL : ∀ w : Plc E, Continuous fun u : finU (E := E) (n := n) => cLoc w u.1 := fun w =>
    (show Continuous (GeneralLinearGroup.map (n := Fin n) (pLoc E w)) from
      Continuous.units_map _ (Continuous.matrix_map continuous_id
        (show Continuous (pLoc E w) from RestrictedProduct.continuous_eval
          (R := fun w : Plc E => w.adicCompletion E)
          (A := fun w : Plc E => (w.adicCompletionIntegers E : Set (w.adicCompletion E))) w))).comp hp
  let D : (Σ w : Plc E, {V : Subgroup (GLw n w) // IsOpen (V : Set (GLw n w)) ∧ V ≤ GlobalTheory.LFun.KGL w (n := n)}) →
      Set (finU (E := E) (n := n)) := fun i => {u | cLoc i.1 u.1 ∈ i.2.1}
  have hD : ∀ i, IsClosed (D i) := fun i => (Subgroup.isClosed_of_isOpen _ i.2.2.1).preimage (hL i.1)
  have hone : ∀ u : finU (E := E) (n := n), (∀ i, u ∈ D i) → u = 1 := by
    intro u hu
    have h1 : ∀ w : Plc E, cLoc w u.1 = 1 := by
      intro w
      by_contra hne
      obtain ⟨V, hVo, hVK, hV⟩ := UpperTheory.Gal.CertificateRingHomMap.PNbhd2.exists_open_avoid w _ hne
      exact hV (hu ⟨w, V, hVo, hVK⟩)
    have h2 : p u = 1 := GlobalTheory.EulerTwRestr.gl_ext fun w => (h1 w).trans (map_one _).symm
    have h3 : GeneralLinearGroup.map (pInf E) (u.1 : GA E n) = 1 := u.2
    exact Subtype.ext (Subtype.ext (ga_ext (by rw [h3]; simp) (by simpa using (show GeneralLinearGroup.map (pFin E) (u.1 : GA E n) = 1 from h2))))
  have hemp : ({u : finU (E := E) (n := n) | p u ∈ GlobalTheory.EulerTw.Kglob E n} \ (O : Set (finU (E := E) (n := n)))) ∩ ⋂ i, D i = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun u hu => ?_
    have := hone u (Set.mem_iInter.1 hu.2)
    exact hu.1.2 (this ▸ O.one_mem)
  obtain ⟨F, hF⟩ := (hC.diff hO).elim_finite_subfamily_closed D hD (Set.disjoint_iff_inter_eq_empty.mpr hemp)
  obtain ⟨Kw, hK1, hK2⟩ := UpperTheory.Gal.CertificateRingHomMap.PNbhd2.exists_Kw F
  refine ⟨F.image Sigma.fst, Kw, hK1, fun u hu hS => ?_⟩
  by_contra huO
  have hmem : u ∈ ({u : finU (E := E) (n := n) | p u ∈ GlobalTheory.EulerTw.Kglob E n} \ (O : Set (finU (E := E) (n := n)))) ∩ ⋂ i ∈ F, D i :=
    ⟨⟨GlobalTheory.EulerTwRestr.mem_Kglob.2 hu, huO⟩,
      Set.mem_iInter₂.2 fun i hi => hK2 i hi (hS i.1 (Finset.mem_image_of_mem _ hi))⟩
  exact Set.disjoint_left.mp hF hmem.1 hmem.2
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem rat_eq_one_of_ZU (s : ℚˣ) (hpos : 0 < (s : ℚ))
    (h : Units.map (algebraMap ℚ AfQ).toMonoidHom s ∈ ZU) : s = 1 := by
  have hv : ∀ v : Plc ℚ, HeightOneSpectrum.valuation ℚ v (s : ℚ) = 1 := fun v => by
    have h1 : Valued.v ((algebraMap ℚ AfQ (s : ℚ)) v) = 1 := h v
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  have hi : ∀ x : ℚ, (∀ v : Plc ℚ, HeightOneSpectrum.valuation ℚ v x ≤ 1) → ∃ m : ℤ, (m : ℚ) = x := fun x hx => by
    obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ x hx
    have h2 : IsIntegral ℤ (algebraMap (𝓞 ℚ) ℚ a) := a.2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact ⟨m, by simpa using hm⟩
  obtain ⟨m, hm⟩ := hi s (fun v => (hv v).le)
  obtain ⟨m', hm'⟩ := hi (s : ℚ)⁻¹ (fun v => by rw [map_inv₀, hv v, inv_one])
  have hmm : m * m' = 1 := by
    have h3 : (m : ℚ) * m' = 1 := by rw [hm, hm']; exact mul_inv_cancel₀ s.ne_zero
    exact_mod_cast h3
  have hm1 : m = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hmm with h4 | h4
    · exact h4
    · subst h4
      rw [← hm] at hpos
      norm_num at hpos
  ext
  rw [← hm, hm1]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem coord_emb (v : InfinitePlace E) (x : E) :
    coord v.embedding (pInf E (algebraMap E (Ad E) x)) = v.embedding x := by
  have h : ∀ w : InfinitePlace E, pInf E (algebraMap E (Ad E) x) w = w.embedding x := fun w => pInf_algebraMap _ _
  unfold coord
  simp [h]

private theorem val_rat (W : Wt E n) (j : ℤ) (f : algForms W) (γ : Gam0 E n) (h1 : γ.1.2 = 1) :
    ∃ a : finU (E := E) (n := n), ofU a = rat γ ∧
      ∀ u : finU (E := E) (n := n), algForms.val f (a.1 * u.1) = xi0 W j γ (algForms.val f u.1) := by
  have hy : (γ.1.1.val.map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * γ.1.1.val = 1 := by
    have h : (γ.1.1.val.map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * γ.1.1.val =
      algebraMap ℚ E γ.1.2 • (1 : Matrix (Fin n) (Fin n) E) := γ.2.1
    rw [h, h1]
    simp
  have hY : ratGL E n γ.1.1 ∈ UA E n := by
    change Formalism.UG.cT (conjAd E) (γ.1.1.val.map (algebraMap E (Ad E))) * 1 * γ.1.1.val.map (algebraMap E (Ad E)) = 1
    rw [GlobalTheory.DefU.ClassFin.cT_map (algebraMap E (Ad E)) (IsCMField.complexConj E).toRingEquiv.toRingHom (conjAd E)
      (fun y => (conjAd_algebraMap y).symm), mul_one, ← Matrix.map_mul]
    have h2 : Formalism.UG.cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ.1.1.val * γ.1.1.val = 1 := hy
    rw [h2]
    simp
  let Y : UA E n := ⟨ratGL E n γ.1.1, hY⟩
  have hYr : Y ∈ ratU E n := Subgroup.mem_subgroupOf.2 ⟨γ.1.1, rfl⟩
  let a := GlobalTheory.UnitarySplit.finPart Y
  let b := GlobalTheory.UnitarySplit.infPart Y
  have hab : Y = a.1 * b.1 := GlobalTheory.UnitarySplit.finPart_mul_infPart Y
  refine ⟨a, ?_, fun u => ?_⟩
  · refine Subtype.ext (Prod.ext ?_ ?_)
    · exact pFin_finGL _
    · show (1 : AfQˣ) = Units.map (algebraMap ℚ AfQ).toMonoidHom γ.1.2
      rw [h1, map_one]
  · have e : a.1 * u.1 = Y * (u.1 * ((b⁻¹ : infU E n) : UA E n)) := by
      have hc := GlobalTheory.DefU.fin_mul_inf u.2 b.2
      rw [hab, Subgroup.coe_inv, mul_assoc, ← mul_assoc b.1, ← hc, mul_assoc u.1, mul_inv_cancel, mul_one]
    have hc : cAll b.1 = embAll E n γ.1.1 := by
      funext v
      show cEmb v.embedding b.1 = GeneralLinearGroup.map v.embedding γ.1.1
      refine Units.ext (Matrix.ext fun i k => ?_)
      have h3 : (cEmb v.embedding b.1).val i k = coord v.embedding ((cInf b.1).val i k) := rfl
      rw [h3, GlobalTheory.UnitarySplit.cInf_infPart]
      exact coord_emb v _
    rw [e, algForms.val_left f hYr, algForms.val_right, inv_inv]
    have h4 : xi0 W j γ = Representation.dual
        ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) γ.1.1 := by
      have h6 : xi0 W j γ = (((γ.1.2 : ℚ) : ℂ) ^ j) • Representation.dual
          ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) γ.1.1 := rfl
      rw [h6, h1]
      simp
    rw [h4, Representation.dual_apply, Representation.dual_apply]
    have h5 : W.rep b⁻¹ = ((Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W).comp (embAll E n)) γ.1.1⁻¹ := by
      have h7 : cAll (b⁻¹ : infU E n).1 = embAll E n γ.1.1⁻¹ := by
        rw [Subgroup.coe_inv, map_inv, hc, map_inv]
      show Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W (cAll (b⁻¹ : infU E n).1) =
        Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W (embAll E n γ.1.1⁻¹)
      rw [h7]
    rw [h5]

theorem pKerFormU_of :
    UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.KerFormU := by
  intro hB E _ _ _ n W j f hf K hK hfix
  obtain ⟨hinj, hsurj⟩ := hB E n
  let φ : GUf E n → Module.Dual ℂ W.Sp := fun g => if h : ∃ u, ofU u = g then algForms.val f h.choose.1 else 0
  have hφ : ∀ u : finU (E := E) (n := n), φ (ofU u) = algForms.val f u.1 := fun u => by
    have h : ∃ u', ofU u' = ofU u := ⟨u, rfl⟩
    show (if h : ∃ u', ofU u' = ofU u then algForms.val f h.choose.1 else 0) = _
    rw [dite_eq_left h, hinj h.choose_spec]
  have hone : ∀ γ : Gam0 E n, sim (rat γ) ∈ ZU → γ.1.2 = 1 := fun γ h => rat_eq_one_of_ZU γ.1.2 γ.2.2 h
  refine ⟨φ, ⟨?_, ?_, ?_⟩, hφ, ?_⟩
  · intro γ k hk he
    have h1 := hone γ (he ▸ hK k hk)
    rw [← he]
    show Units.map (algebraMap ℚ AfQ).toMonoidHom γ.1.2 = 1
    rw [h1, map_one]
  · intro γ u hγ hu
    obtain ⟨u₀, rfl⟩ := hsurj u hu
    obtain ⟨a, ha, hau⟩ := val_rat W j f γ (hone γ (hγ ▸ ZU.one_mem))
    rw [← ha, ← map_mul, hφ, hφ]
    exact hau u₀
  · intro k hk u hk1 hu
    obtain ⟨u₀, rfl⟩ := hsurj u hu
    obtain ⟨u', rfl⟩ := hsurj k hk1
    rw [← map_mul, hφ, hφ]
    show algForms.val f (u₀.1 * u'.1) = _
    rw [← algForms.val_algRep, hfix u' hk]
  · have hex : ∃ g, algForms.val f g ≠ 0 := by
      by_contra hc
      push_neg at hc
      refine hf (Subtype.ext (LinearMap.ext fun v => funext fun g => ?_))
      exact LinearMap.congr_fun (hc g) v
    obtain ⟨g, hg⟩ := hex
    refine ⟨ofU (GlobalTheory.UnitarySplit.finPart g), sim_ofU _, ?_⟩
    rw [hφ]
    intro h0
    apply hg
    have h1 := algForms.val_right f (GlobalTheory.UnitarySplit.finPart g).1 (GlobalTheory.UnitarySplit.infPart g)
    rw [← GlobalTheory.UnitarySplit.finPart_mul_infPart g] at h1
    rw [h1, h0, map_zero]

end UpperTheory.Gal.CertificateRingHomMap
end
