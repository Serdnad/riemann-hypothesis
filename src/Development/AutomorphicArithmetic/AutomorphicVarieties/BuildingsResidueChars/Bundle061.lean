module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.TwistOfRed
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RChar2

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc

section Real

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

private noncomputable def diagR (E : Type) [Field E] [NumberField E] [IsTotallyReal E] : E →+* TR.Rinf E :=
  (TR.pInf E).comp (algebraMap E (Ad E))

private theorem infDiag_eqR (k : Eˣ) : infDiag k = TR.infId E (Units.map (diagR E).toMonoidHom k) := by
  classical
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E) = (algebraMap E (InfiniteAdeleRing E) k, 1) := by
    unfold infDiag
    rw [MonoidHom.finsetProd_apply, Units.coe_prod]
    let ι : (∀ w : InfinitePlace E, w.Completion) →* AdeleRing (𝓞 E) E :=
      MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)
    change ∏ w : InfinitePlace E, ι (Pi.mulSingle w (algebraMap E w.Completion k)) =
      ι (fun w => algebraMap E w.Completion k)
    rw [← map_prod, Finset.univ_prod_mulSingle]
  apply Units.ext
  rw [h]
  refine Prod.ext ?_ ?_
  · change _ = 1 - TR.infEq E 1 + TR.infEq E ((TR.infEq E).symm (algebraMap E (InfiniteAdeleRing E) k))
    simp
  · change (1 : Af E) = 1 - 0 + 0
    simp

private theorem denseRange_diagR : DenseRange (diagR E) := by
  have hc : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact (TR.infEq E).symm.surjective.denseRange.comp (InfiniteAdeleRing.denseRange_algebraMap E) hc

private theorem denseRange_unitsR : DenseRange (Units.map (diagR E).toMonoidHom) := by
  refine dense_iff_inter_open.2 fun U hU ⟨u, hu⟩ => ?_
  obtain ⟨k, v, hv, hk⟩ := denseRange_diagR.exists_mem_open (Units.isOpenEmbedding_val.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have h0 : k ≠ 0 := by
    rintro rfl
    exact v.ne_zero (hk.trans (map_zero _))
  exact ⟨v, hv, Units.mk0 k h0, Units.ext hk.symm⟩

private theorem diagR_mk (φ : E →+* ℂ) (k : E) : ((diagR E k (InfinitePlace.mk φ) : ℝ) : ℂ) = φ k := by
  have hr := IsTotallyReal.isReal (InfinitePlace.mk φ)
  have e : diagR E k (InfinitePlace.mk φ) = InfinitePlace.embedding_of_isReal hr k := by
    change InfinitePlace.Completion.extensionEmbeddingOfIsReal hr
      (algebraMap E (InfinitePlace.mk φ).Completion k) = _
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hr (WithAbs.toAbs _ k)
  rw [e, InfinitePlace.embedding_of_isReal_apply,
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hr)]

private theorem chiInf_pos {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) (u : (TR.Rinf E)ˣ)
    (hu : ∀ v, 0 < u.val v) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ := by
  have hc : ∀ v, Continuous fun u : (TR.Rinf E)ˣ => u.val v := fun v => (continuous_apply v).comp Units.continuous_val
  have ho : IsOpen {u : (TR.Rinf E)ˣ | ∀ v, 0 < u.val v} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun v => isOpen_lt continuous_const (hc v)
  have hcl : IsClosed {u : (TR.Rinf E)ˣ |
      ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ n φ} :=
    isClosed_eq (Units.continuous_val.comp (TR.continuous_chiInf χ)) (continuous_finsetProd _ fun φ _ =>
      (Complex.continuous_ofReal.comp (hc _)).zpow₀ _ fun u => Or.inl
        (Complex.ofReal_ne_zero.2 (TR.unit_ne_zero u _)))
  refine closure_minimal ?_ hcl (denseRange_unitsR.open_subset_closure_inter ho hu)
  rintro _ ⟨hk, k, rfl⟩
  have h1 := h k fun φ => by
    have h2 := hk (InfinitePlace.mk (Complex.ofRealHom.comp φ))
    have h3 := diagR_mk (Complex.ofRealHom.comp φ) (k : E)
    exact h2.trans_eq (Complex.ofReal_injective h3)
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR] at h1
  refine h1.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (diagR_mk φ (k : E)).symm

open Classical in
private noncomputable def negAt (v : InfinitePlace E) : (TR.Rinf E)ˣ :=
  Units.map (MonoidHom.mulSingle (fun _ : InfinitePlace E => ℝ) v) (-1)

private theorem infId_negAt (v : InfinitePlace E) : TR.infId E (negAt v) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E v (-1) := by
  classical
  apply Units.ext
  refine Prod.ext ?_ ?_
  · change 1 - TR.infEq E 1 + TR.infEq E (Pi.mulSingle v (-1)) = Pi.mulSingle v (-1)
    rw [map_one, sub_self]
    refine (zero_add _).trans (funext fun w => ?_)
    change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
      ((Pi.mulSingle v (-1) : TR.Rinf E) w) = _
    by_cases h : w = v
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, map_neg, map_one]
    · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, map_one]
  · change (1 : Af E) - 0 + 0 = 1
    simp

private theorem bij_mk : Function.Bijective (InfinitePlace.mk : (E →+* ℂ) → InfinitePlace E) := by
  refine ⟨fun φ ψ h => ?_, fun w => ⟨w.embedding, w.mk_embedding⟩⟩
  rw [← InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal φ), h,
    InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal ψ)]

private theorem chiInf_all {χ : HChar E} {b : ℤ} (h : IsAlgPos χ fun _ => b)
    (hs : ∀ v : InfinitePlace E, χ.locInf v (-1) = (-1) ^ b) (u : (TR.Rinf E)ˣ) :
    ((TR.chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((u.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ b := by
  classical
  let s : (TR.Rinf E)ˣ := ∏ v, if u.val v < 0 then negAt v else 1
  have h1 : ∀ w, s.val w = if u.val w < 0 then -1 else 1 := fun w => by
    simp only [s, Units.coe_prod, Finset.prod_apply]
    rw [Finset.prod_eq_single w _ fun hw => absurd (Finset.mem_univ w) hw]
    · split_ifs
      · exact Pi.mulSingle_eq_same (M := fun _ : InfinitePlace E => ℝ) w _
      · rfl
    · intro v _ hv
      split_ifs
      · exact Pi.mulSingle_eq_of_ne (M := fun _ : InfinitePlace E => ℝ) hv.symm _
      · rfl
  have h2 : ((TR.chiInf χ s : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, ((s.val (InfinitePlace.mk φ) : ℝ) : ℂ) ^ b := by
    rw [bij_mk.prod_comp fun w => ((s.val w : ℝ) : ℂ) ^ b]
    simp only [h1]
    simp only [s, map_prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    split_ifs
    · have e : TR.chiInf χ (negAt v) = χ.locInf v (-1) := congrArg χ.1 (infId_negAt v)
      rw [e, hs]
      simp
    · simp
  have h3 := chiInf_pos h (s * u) fun w => by
    change 0 < s.val w * u.val w
    rw [h1]
    split_ifs with hw
    · linarith
    · rw [one_mul]
      exact lt_of_le_of_ne (not_lt.1 hw) (TR.unit_ne_zero u w).symm
  rw [map_mul, Units.val_mul] at h3
  refine mul_left_cancel₀ (TR.chiInf χ s).ne_zero (h3.trans ?_)
  rw [h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [← mul_zpow, ← Complex.ofReal_mul]
  rfl

end Real

theorem UpperTheory.heckeChar_algebraic_of_sign :
    UpperTheory.V.Af.Cr.AlgOfSign := by
  intro F _ _ _ χ b h hs k
  rw [HChar.inf, MonoidHom.comp_apply, infDiag_eqR]
  refine (chiInf_all h hs _).trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ b) (diagR_mk φ (k : F))
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private noncomputable def linRep {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) :
    Representation k Γ (Fin n → k) where
  toFun g := Matrix.toLin' (r g : Matrix (Fin n) (Fin n) k)
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' g h := by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp]

private theorem isIrr_iff {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) :
    IsIrr r ↔ (linRep r).IsIrreducible := by
  constructor
  · rintro ⟨h0, -, h⟩
    haveI : Nontrivial (Subrepresentation (linRep r)) := ⟨⊤, ⊥, fun h' =>
      h0 (congrArg Subrepresentation.toSubmodule h')⟩
    refine ⟨fun S => ?_⟩
    rcases h S.toSubmodule le_top (fun g v hv => S.apply_mem_toSubmodule g hv) with h1 | h1
    · left; exact Subrepresentation.toSubmodule_injective h1
    · right; exact Subrepresentation.toSubmodule_injective h1
  · intro h
    refine ⟨fun h0 => ?_, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
    · exact bot_ne_top (α := Subrepresentation (linRep r)) (Subrepresentation.toSubmodule_injective h0.symm)
    · rcases h.eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation (linRep r)) with h1 | h1
      · left; exact congrArg Subrepresentation.toSubmodule h1
      · right; exact congrArg Subrepresentation.toSubmodule h1

private theorem isIrr_comp_of_range {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (φ : Γ' →* Γ) (h : IsIrr (r.comp φ.range.subtype)) : IsIrr (r.comp φ) := by
  obtain ⟨h0, -, h⟩ := h
  refine ⟨h0, fun _ _ _ => Submodule.mem_top, fun W hle hW => h W hle ?_⟩
  rintro ⟨_, g, rfl⟩ v hv
  exact hW g v hv

theorem UpperTheory.galois_representation_irreducible_prime_dimension :
    UpperTheory.V.Af.Sol.IrrPrime := by
  intro Γ Γ' k _ _ _ _ _ n r φ hN hp hn hr
  apply isIrr_comp_of_range
  rw [isIrr_iff]
  by_contra hred
  haveI : φ.range.FiniteIndex := ⟨hp.ne_zero⟩
  have hcomm : commutator Γ ≤ φ.range := by
    haveI : Fact (φ.range.index).Prime := ⟨hp⟩
    haveI : IsCyclic (Γ ⧸ φ.range) := isCyclic_of_prime_card (p := φ.range.index) rfl
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff]
    rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    letI := IsCyclic.commGroup (α := Γ ⧸ φ.range)
    exact mul_comm _ _
  obtain ⟨η, hη, hker, e, he⟩ := UpperTheory.V.AlgebraTools.twistOfRed k Γ (Fin n → k) (linRep r) φ.range
    (Nat.cast_ne_zero.mpr hp.ne_zero) hcomm ((isIrr_iff r).mp hr) hred
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hr.1 (Subsingleton.elim _ _)
  apply hη
  ext g
  have h1 : η g ^ φ.range.index = 1 := by
    rw [← map_pow]; exact hker (Subgroup.pow_index_mem _ g)
  have h2 : η g ^ n = 1 := by
    have hl : linRep r g ∘ₗ (e : (Fin n → k) →ₗ[k] (Fin n → k)) =
        (η g : k) • ((e : (Fin n → k) →ₗ[k] (Fin n → k)) ∘ₗ linRep r g) := LinearMap.ext fun v => he g v
    have hd := congrArg LinearMap.det hl
    rw [LinearMap.det_smul, LinearMap.det_comp, LinearMap.det_comp, Module.finrank_fin_fun] at hd
    have hu : IsUnit (LinearMap.det (linRep r g)) := ((Group.isUnit g).map (linRep r)).map LinearMap.det
    have hue : IsUnit (LinearMap.det (e : (Fin n → k) →ₗ[k] (Fin n → k))) := e.isUnit_det'
    have hne := mul_ne_zero hue.ne_zero hu.ne_zero
    apply Units.ext
    apply mul_right_cancel₀ hne
    rw [Units.val_pow_eq_pow_val, ← hd, Units.val_one, one_mul, mul_comm]
  have hc : Nat.Coprime φ.range.index n := Nat.coprime_of_lt_prime hn0 hn hp
  have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [hc, pow_one] at this
  simp [this]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem irr_nontrivial {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) : Nontrivial (Fin n → k) := by
  obtain ⟨hne, -, -⟩ := hirr
  by_contra hc
  rw [not_nontrivial_iff_subsingleton] at hc
  exact hne (Subsingleton.elim _ _)

private theorem smul_one_inj {k : Type} [Field k] {n : ℕ} [Nontrivial (Fin n → k)] (a b : k)
    (h : a • (1 : Matrix (Fin n) (Fin n) k) = b • 1) : a = b := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → k)
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.mulVec v) h
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  exact smul_left_injective k hv h2

private theorem schur_scalar {Γ k : Type} [Group Γ] [Field k] [IsAlgClosed k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (g : GL (Fin n) k) (hg : ∀ s, r s * g = g * r s) :
    ∃ c : kˣ, (g : Matrix (Fin n) (Fin n) k) = (c : k) • 1 :=
  _root_.UpperTheory.Reformulated.B.Qi17.schur_scalar r hirr g hg

theorem UpperTheory.schur_extension :
    UpperTheory.V.Af.Sol.SchurExt := by
  intro Γ Γ' k _ _ _ _ n r r₁ φ hN hirr hiso
  obtain ⟨g, hg⟩ := hiso
  have hnt := irr_nontrivial _ hirr
  simp only [MonoidHom.comp_apply] at hg
  have hcomm : ∀ s t, (r.comp φ) t * (r s * (g * r₁ s * g⁻¹)⁻¹) =
      (r s * (g * r₁ s * g⁻¹)⁻¹) * (r.comp φ) t := by
    intro s t
    obtain ⟨u, hu⟩ := hN.conj_mem' (φ t) ⟨t, rfl⟩ s
    have h1 := hg u
    rw [hu] at h1
    simp only [map_mul, map_inv] at h1
    have h2 : r (φ t) * r s = r s * ((r s)⁻¹ * r (φ t) * r s) := by group
    rw [MonoidHom.comp_apply, ← mul_assoc, h2, h1, hg t]
    group
  choose c hc using fun s => schur_scalar _ hirr _ (hcomm s)
  have hr : ∀ s, (r s : Matrix (Fin n) (Fin n) k) =
      (c s : k) • ((g * r₁ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    intro s
    have h1 : r s = (r s * (g * r₁ s * g⁻¹)⁻¹) * (g * r₁ s * g⁻¹) := by group
    rw [h1, Units.val_mul, hc s, Matrix.smul_mul, Matrix.one_mul]
  have huniq : ∀ s (a : kˣ), (r s : Matrix (Fin n) (Fin n) k) =
      (a : k) • ((g * r₁ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) → c s = a := by
    intro s a ha
    apply Units.ext
    apply smul_one_inj (n := n)
    rw [← hc s, Units.val_mul, ha, Matrix.smul_mul, Units.mul_inv]
  have hmul : ∀ s t, c (s * t) = c s * c t := by
    intro s t
    apply huniq
    have h1 : g * r₁ (s * t) * g⁻¹ = (g * r₁ s * g⁻¹) * (g * r₁ t * g⁻¹) := by
      rw [map_mul]; group
    rw [map_mul r, Units.val_mul, hr s, hr t, h1, Units.val_mul (g * r₁ s * g⁻¹), Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, Units.val_mul (c s)]
  refine ⟨MonoidHom.mk' c hmul, ?_, g, ?_⟩
  · ext t
    have : c (φ t) = 1 := huniq _ _ (by rw [← hg t]; simp)
    simp [this]
  · intro s
    apply Units.ext
    rw [hr s]
    simp only [Units.val_mul, tw_val, MonoidHom.mk'_apply, Matrix.smul_mul, Matrix.mul_smul]
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

private theorem conj_algebraMap {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsCMField K] [IsCMField M] (x : K) :
    IsCMField.complexConj M (algebraMap K M x) = algebraMap K M (IsCMField.complexConj K x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K M)) x).symm

theorem UpperTheory.complexConj_place_under_eq :
    UpperTheory.V.Af.Sol.ConjUnder := by
  intro K M _ _ _ _ _ _ _ w
  refine ⟨?_, ?_, ?_⟩
  · apply HeightOneSpectrum.ext
    rw [cPl_asIdeal]
    change (cPl w).asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M))).comap _
    rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
    congr 1
    ext x
    exact conj_algebraMap (x : K)
  · show Nat.card (𝓞 M ⧸ (cPl w).asIdeal) = Nat.card (𝓞 M ⧸ w.asIdeal)
    refine Nat.card_congr (Ideal.quotientEquiv _ _
      (RingOfIntegers.mapRingEquiv (IsCMField.complexConj M).toRingEquiv) ?_).toEquiv
    rw [cPl_asIdeal]
    exact (Ideal.map_comap_of_surjective
      (RingOfIntegers.mapRingEquiv (IsCMField.complexConj M).toRingEquiv : 𝓞 M →+* 𝓞 M)
      (RingOfIntegers.mapRingEquiv _).surjective w.asIdeal).symm
  · apply HeightOneSpectrum.ext
    rw [cPl_asIdeal, cPl_asIdeal, Ideal.comap_comap]
    convert Ideal.comap_id w.asIdeal
    ext x
    exact IsCMField.complexConj_apply_apply M (x : M)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem algSat_injective (n q : ℕ) (hq : q ≠ 0) (B B' : Multiset ℂˣ)
    (h : UpperTheory.V.Af.algSat n q B = UpperTheory.V.Af.algSat n q B') : B = B' := by
  unfold UpperTheory.V.Af.algSat at h
  have hc : ((((q : ℝ) ^ (((n : ℝ) - 1) / 2)) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) ^ (((n : ℝ) - 1) / 2) :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hq) _
    exact_mod_cast this.ne'
  have h1 := Multiset.map_injective (mul_right_injective₀ hc) h
  have h2 : ∀ s : Multiset ℂˣ, (do let a ← s; pure (a : ℂ)) =
      Multiset.map (fun a : ℂˣ => (a : ℂ)) s := fun s => Multiset.bind_singleton _ _
  rw [h2, h2] at h1
  exact Multiset.map_injective Units.val_injective h1

theorem UpperTheory.hecke_eigenvalue_basic_properties :
    UpperTheory.V.Af.Sol.EigBasic := by
  intro F Ω _ _ _ _ _ l _ ι v
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  refine ⟨?_, ?_, ?_⟩
  · intro δ δ' z z' hz hz' A' hA'
    obtain ⟨hi, hf⟩ := hz A' hA'
    obtain ⟨hi', hf'⟩ := hz' A' hA'
    refine ⟨fun s hs => ?_, fun τ hτ => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hi s hs, hi' s hs, inv_one, mul_one]
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul, Units.val_inv_eq_inv_val,
        map_inv₀, hf τ hτ, hf' τ hτ]
      push_cast
      rfl
  · intro δ z z' hz hz'
    apply Units.ext
    rw [← (hz A hA).2 σ hσ, ← (hz' A hA).2 σ hσ]
  · intro n r B B' hB hB'
    have e1 := (hB A hA).2 σ hσ
    have e2 := (hB' A hA).2 σ hσ
    rw [e1] at e2
    have e3 := congrArg Polynomial.roots e2
    rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e3
    have hq : Formalism.ConjugateSelfDual.normV v ≠ 0 := by
      unfold Formalism.ConjugateSelfDual.normV
      exact Nat.card_pos.ne'
    exact algSat_injective n _ hq B B' e3
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_cyclic_subextension_over_rat :
    UpperTheory.V.Af.Sol.CycQ := by
  intro N
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (N + 3)
  obtain ⟨q, hq, -, hqp⟩ := Nat.exists_prime_gt_modEq_one 0 hp.ne_zero
  haveI := Fact.mk hq
  have hpdvd : p ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_le).mp hqp.symm
  haveI : IsAbelianGalois ℚ (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {q} ℚ (CyclotomicField q ℚ)
  have hcardG : Nat.card Gal(CyclotomicField q ℚ/ℚ) = q - 1 := by
    rw [IsGalois.card_aut_eq_finrank, IsCyclotomicExtension.Rat.finrank q (CyclotomicField q ℚ),
      Nat.totient_prime hq]
  haveI : IsCyclic Gal(CyclotomicField q ℚ/ℚ) :=
    isCyclic_of_surjective (IsCyclotomicExtension.autEquivPow (CyclotomicField q ℚ)
      (Polynomial.cyclotomic.irreducible_rat hq.pos)).symm (MulEquiv.surjective _)
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Gal(CyclotomicField q ℚ/ℚ))
  have hH : Nat.card (Subgroup.zpowers (g ^ p)) = (q - 1) / p := by
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hp.ne_zero (by rw [hg, hcardG]; exact hpdvd), hg, hcardG]
  have hfin : Module.finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) = p := by
    have h1 := (letI : Module.Free (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) (CyclotomicField q ℚ) := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) (CyclotomicField q ℚ))
    rw [IntermediateField.finrank_fixedField_eq_card, hH,
      IsCyclotomicExtension.Rat.finrank q (CyclotomicField q ℚ), Nat.totient_prime hq] at h1
    obtain ⟨m, hm⟩ := hpdvd
    have hq2 := hq.two_le
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; omega
      · exact h
    rw [hm, Nat.mul_div_cancel_left m hp.pos] at h1
    exact Nat.eq_of_mul_eq_mul_right hmpos h1
  haveI : IsAbelianGalois ℚ (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) :=
    IsAbelianGalois.tower_bot ℚ _ (CyclotomicField q ℚ)
  refine ⟨IntermediateField.fixedField (Subgroup.zpowers (g ^ p)), inferInstance, inferInstance,
    inferInstance, ?_, ?_, ?_⟩
  · classical
    rw [NumberField.isTotallyReal_iff]
    have hodd := InfinitePlace.nrRealPlaces_pos_of_odd_finrank
      (K := IntermediateField.fixedField (Subgroup.zpowers (g ^ p)))
      (by rw [hfin]; exact hp.odd_of_ne_two (by omega))
    obtain ⟨w0, hw0⟩ : ∃ w : InfinitePlace (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))),
        w.IsReal := by
      by_contra hne
      push_neg at hne
      have : IsEmpty {w : InfinitePlace (IntermediateField.fixedField (Subgroup.zpowers (g ^ p))) //
          w.IsReal} := ⟨fun w => hne w.1 w.2⟩
      simp [InfinitePlace.nrRealPlaces] at hodd
    intro w
    obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq (k := ℚ) (w := w0) (w' := w)
      (Subsingleton.elim _ _)
    rw [← hσ]
    exact InfinitePlace.isReal_smul_iff.mpr hw0
  · rw [hfin]; exact hp
  · rw [hfin]; omega
end
