module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Formalism.LocalToGlobal.Columns.Bundle012
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.Columns.Bundle004

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem isOpen_intA (F : Type) [Field F] [NumberField F] :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, Valued.v (a v) ≤ 1} :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => ((v.adicCompletionIntegers F : ValuationSubring _) : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)

private theorem continuous_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} :
    Continuous (sim : GUf E n → AfQˣ) := continuous_snd.comp continuous_subtype_val

private theorem continuous_mat {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} :
    Continuous (mat : GUf E n → GL (Fin n) (Af E)) := continuous_fst.comp continuous_subtype_val

private theorem continuous_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Plc E) :
    Continuous (comp w : GUf E n → GL (Fin n) (w.adicCompletion E)) :=
  (Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))).comp continuous_mat

theorem UpperTheory.Gal.CertificateRingHomMap.pLevOpen_of :
    UpperTheory.Gal.CertificateRingHomMap.LevOpen := by
  intro E _ _ _ n S Kw hK
  have hI : IsOpen {a : Af E | ∀ v, Valued.v (a v) ≤ 1} := isOpen_intA E
  have hJ : IsOpen {a : AfQ | ∀ v, Valued.v (a v) ≤ 1} := isOpen_intA ℚ
  let A : Set (GUf E n) :=
    ((((fun k => ((sim k : AfQˣ) : AfQ)) ⁻¹' {a : AfQ | ∀ v, Valued.v (a v) ≤ 1}) ∩
      ((fun k => (((sim k)⁻¹ : AfQˣ) : AfQ)) ⁻¹' {a : AfQ | ∀ v, Valued.v (a v) ≤ 1})) ∩
    ((⋂ i, ⋂ j, (fun k => (mat k).val i j) ⁻¹' {a : Af E | ∀ v, Valued.v (a v) ≤ 1}) ∩
      (⋂ i, ⋂ j, (fun k => ((mat k)⁻¹).val i j) ⁻¹' {a : Af E | ∀ v, Valued.v (a v) ≤ 1}))) ∩
    ⋂ w ∈ S, comp w ⁻¹' (Kw w : Set (GLw n w))
  have hAo : IsOpen A := by
    refine ((IsOpen.inter ?_ ?_).inter (IsOpen.inter ?_ ?_)).inter ?_
    · exact hJ.preimage (Units.continuous_val.comp continuous_sim)
    · exact hJ.preimage (Units.continuous_val.comp continuous_sim.inv)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hI.preimage ((Units.continuous_val.comp continuous_mat).matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        hI.preimage ((Units.continuous_val.comp continuous_mat.inv).matrix_elem i j)
    · exact isOpen_biInter_finset fun w hw => (hK w hw).preimage (continuous_comp w)
  have hone : ∀ (i j : Fin n) (v : Plc E), Valued.v (((1 : Matrix (Fin n) (Fin n) (Af E)) i j) v) ≤ 1 := by
    intro i j v
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq]
      change Valued.v (1 : v.adicCompletion E) ≤ 1
      rw [map_one]
    · rw [Matrix.one_apply_ne h]
      change Valued.v (0 : v.adicCompletion E) ≤ 1
      rw [map_zero]
      exact zero_le'
  have hQ : ∀ v : Plc ℚ, Valued.v ((1 : AfQ) v) ≤ 1 := fun v => by
    change Valued.v (1 : v.adicCompletion ℚ) ≤ 1
    rw [map_one]
  have h1 : (1 : GUf E n) ∈ A := by
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
    · simpa using hQ
    · simpa using hQ
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one]
      exact fun i j => hone i j
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one, inv_one]
      exact fun i j => hone i j
    · simp only [Set.mem_iInter, Set.mem_preimage, map_one]
      exact fun w _ => (Kw w).one_mem
  have hsub : A ⊆ (lev S Kw : Set (GUf E n)) := by
    rintro k ⟨⟨⟨hs, hs'⟩, hm, hm'⟩, hc⟩
    simp only [Set.mem_iInter, Set.mem_preimage] at hm hm' hc
    refine mem_lev.2 ⟨fun v => ?_, fun w hw => hc w hw, fun w _ _ => ?_⟩
    · have h : Valued.v (((sim k : AfQˣ) : AfQ) v * (((sim k)⁻¹ : AfQˣ) : AfQ) v) = 1 := by
        change Valued.v ((((sim k : AfQˣ) : AfQ) * (((sim k)⁻¹ : AfQˣ) : AfQ)) v) = 1
        rw [Units.mul_inv]
        exact map_one _
      rw [map_mul] at h
      refine le_antisymm (hs v) ?_
      calc (1 : _) = _ := h.symm
        _ ≤ Valued.v (((sim k : AfQˣ) : AfQ) v) * 1 := mul_le_mul' le_rfl (hs' v)
        _ = _ := mul_one _
    · rw [GlobalTheory.HenQ.Basic.mem_KGL_iff]
      refine ⟨fun i j => hm i j w, fun i j => ?_⟩
      have : (comp w k)⁻¹ = GeneralLinearGroup.map (pLoc E w) (mat k)⁻¹ := (map_inv _ _).symm
      rw [this]
      exact hm' i j w
  exact Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hAo.mem_nhds h1) hsub)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pOfUBij_of :
    UpperTheory.Gal.CertificateRingHomMap.OfUBij := by
  intro E _ _ _ n
  refine ⟨fun u v h => ?_, fun g hg => ?_⟩
  · have h1 : GeneralLinearGroup.map (pFin E) u.1.1 = GeneralLinearGroup.map (pFin E) v.1.1 :=
      congrArg (fun x : GUf E n => mat x) h
    have h2 := congrArg (finGL E n) h1
    rw [GlobalTheory.DefU.ClassFin.finGL_pFin, GlobalTheory.DefU.ClassFin.finGL_pFin] at h2
    exact Subtype.ext (Subtype.ext h2)
  · have hs : g.1.2 = 1 := hg
    have h : Formalism.UG.cT (conjFin (GlobalTheory.DefU.ClassFin.cc E)) (mat g).val * (mat g).val = 1 :=
      (mem_Sim.1 g.2).trans (by rw [hs]; simp)
    refine ⟨⟨⟨finGL E n (mat g), GlobalTheory.DefU.ClassFin.finGL_mem_UA _ h⟩, pInf_finGL _⟩, ?_⟩
    exact Subtype.ext (Prod.ext (pFin_finGL _) hs.symm)
end

section

open Module

private theorem exists_common_eigenvector_of_commute_of_invariant {E ι : Type} [AddCommGroup E] [Module ℂ E]
    (T : ι → E →ₗ[ℂ] E) (hT : ∀ i j, T i ∘ₗ T j = T j ∘ₗ T i) :
    ∀ n : ℕ, ∀ W : Submodule ℂ E, finrank ℂ W = n → FiniteDimensional ℂ W → W ≠ ⊥ →
      (∀ i, ∀ x ∈ W, T i x ∈ W) → ∃ x ∈ W, x ≠ 0 ∧ ∀ i, ∃ c : ℂ, T i x = c • x := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hfin hne hW
  by_cases hs : ∀ i, ∃ c : ℂ, ∀ x ∈ W, T i x = c • x
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨x, hx, hx0, fun i => (hs i).imp fun c hc => hc x hx⟩
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((T i).restrict (fun x hx => hW i x hx))
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    set W' : Submodule ℂ E := W ⊓ LinearMap.ker (T i - μ • LinearMap.id) with hW'
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ T i x = μ • x := by
      intro x
      simp [hW', sub_eq_zero]
    have hle : W' ≤ W := inf_le_left
    have hlt : W' < W := by
      refine lt_of_le_of_ne hle ?_
      intro heq
      obtain ⟨x, hx, hne'⟩ := hi μ
      exact hne' ((hmem x).1 (by rw [heq]; exact hx)).2
    haveI : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hle
    have hlt' : finrank ℂ W' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hne' : W' ≠ ⊥ := by
      intro hbot
      have hv0 : (v : E) ∈ W' := (hmem _).2 ⟨v.2, by
        have := hv.apply_eq_smul
        simpa using congrArg Subtype.val this⟩
      rw [hbot, Submodule.mem_bot] at hv0
      exact hv.2 (Subtype.ext hv0)
    have hW'inv : ∀ j, ∀ x ∈ W', T j x ∈ W' := by
      intro j x hx
      rw [hmem] at hx ⊢
      refine ⟨hW j x hx.1, ?_⟩
      have h1 := LinearMap.congr_fun (hT i j) x
      simp only [LinearMap.comp_apply] at h1
      rw [h1, hx.2, map_smul]
    obtain ⟨x, hx, hx0, hc⟩ := ih _ hlt' W' rfl inferInstance hne' hW'inv
    exact ⟨x, hle hx, hx0, hc⟩

theorem UpperTheory.Gal.CertificateRingHomMap.pCentralEig2_of :
    UpperTheory.Gal.CertificateRingHomMap.CentralEig2 := by
  intro Γ H Z V _ _ _ _ _ ι K ξ ζ hζ M hfin hM hne hinv
  let T : Z → (H → V) →ₗ[ℂ] (H → V) := fun z =>
    { toFun := fun Φ g => Φ (g * ζ z), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hT : ∀ a b, T a ∘ₗ T b = T b ∘ₗ T a := by
    intro a b
    refine LinearMap.ext fun Φ => funext fun g => ?_
    show Φ (g * ζ a * ζ b) = Φ (g * ζ b * ζ a)
    rw [mul_assoc, mul_assoc, hζ a (ζ b)]
  obtain ⟨Φ, hΦM, hΦ0, hc⟩ :=
    exists_common_eigenvector_of_commute_of_invariant T hT _ M rfl hfin hne (fun z Φ hΦ => hinv Φ hΦ z)
  choose c hc using hc
  have hcg : ∀ z g, Φ (g * ζ z) = c z • Φ g := fun z g => congrFun (hc z) g
  obtain ⟨g0, hg0⟩ := Function.ne_iff.mp hΦ0
  have hscal : ∀ a b : ℂ, a • Φ g0 = b • Φ g0 → a = b := fun a b h =>
    smul_left_injective ℂ hg0 h
  have hF : (∀ (γ : Γ) (g : H), Φ (ι γ * g) = ξ γ (Φ g)) ∧ ∀ k ∈ K, ∀ g : H, Φ (g * k) = Φ g :=
    hM hΦM
  have h1 : c 1 = 1 := by
    apply hscal
    rw [← hcg 1 g0, map_one, mul_one, one_smul]
  have hmul : ∀ a b, c (a * b) = c a * c b := by
    intro a b
    apply hscal
    rw [← hcg (a * b) g0, map_mul, ← mul_assoc, hcg b, hcg a, smul_smul, mul_comm]
  let χ : Z →* ℂ := { toFun := c, map_one' := h1, map_mul' := hmul }
  refine ⟨Φ, hΦM, hΦ0, χ.toHomUnits, ?_, ?_, ?_⟩
  · intro z g
    exact hcg z g
  · intro z hz
    apply Units.ext
    show c z = 1
    apply hscal
    rw [← hcg z g0, hF.2 _ hz g0, one_smul]
  · intro z γ a hzγ hξ
    show c z = a
    apply hscal
    rw [← hcg z g0, ← hξ (Φ g0), ← hF.1 γ g0, ← hzγ, hζ z g0]
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pSphType_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.SphType := by
  intro hIC hLC E _ _ _ n π w hw
  refine ⟨?_, ?_⟩
  · rintro ⟨B, σ, ⟨-, f, hf0, hfV, hf⟩, hB⟩
    have hker : LinearMap.ker f = ⊥ := by
      refine (((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => ?_)).resolve_right
        fun h => hf0 (LinearMap.ker_eq_top.1 h)
      rw [LinearMap.mem_ker] at hv ⊢
      have h1 := hf ⟨(locF hw g).1, locF_mem hw g⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, cLoc_locF] at h1
      rw [h1, hv, map_zero]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    have hfix := GlobalTheory.LGrp.mem_fixed.1 hv
    have hφ0 : f v ≠ 0 := fun h => hv0 (LinearMap.ker_eq_bot.1 hker (h.trans (map_zero f).symm))
    have key : ∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n x (f v) = f v := by
      intro x hx hk
      have h1 := hf ⟨x, hx⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h1
      rw [← h1, hfix _ hk]
    obtain ⟨-, -, -, -, hcc, hloc⟩ := hLC E n w hw
    refine ⟨⟨f v, hfV v, hφ0, fun x hx h => ?_⟩, ⟨f v, hfV v, hφ0, fun x hx h => ?_⟩⟩
    · simpa using key x hx h
    · rw [hloc] at hx
      have h2 := hIC E n (ofU ⟨x, (Subgroup.mem_inf.1 hx).1⟩) (cj w) (by rw [sim_ofU]; exact one_mem _)
        (by rw [comp_ofU]; exact h)
      rw [hcc, comp_ofU] at h2
      simpa using key x hx h2
  · rintro J χ ⟨φ, hφ, h0, hact⟩
    have hlev := (π.isAut.aut φ hφ).level
    have hc : Continuous fun k : J => (locF hw k.1 : finU (E := E) (n := n)) := by
      have h1 : Continuous fun k : GLw n w => (locF hw k : finU (E := E) (n := n)) :=
        Continuous.subtype_mk (continuous_subtype_val.comp (locE hw).symm.continuous) _
      exact h1.comp continuous_subtype_val
    have hset : {k : J | χ k = 1} = (fun k : J => (locF hw k.1 : finU (E := E) (n := n))) ⁻¹' {k : finU (E := E) (n := n) | RU E n k φ = φ} := by
      ext k
      have hk : cLoc w (locF hw k.1).1 ∈ J := by rw [cLoc_locF]; exact k.2
      have h1 := hact (locF hw k.1).1 (locF_mem hw k.1) hk
      have h2 : (⟨cLoc w (locF hw k.1).1, hk⟩ : J) = k := Subtype.ext (cLoc_locF hw k.1)
      rw [h2] at h1
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [h1]
      constructor
      · intro h; rw [h]; simp
      · intro h
        have h3 : ((χ k : ℂˣ) : ℂ) = 1 := smul_left_injective ℂ h0 (by simpa using h)
        exact Units.ext h3
    rw [hset]
    exact hlev.preimage hc
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem cpow_key (q n j : ℕ) (hq : 0 < q) :
    (q : ℂ) ^ (j.choose 2) * (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - (j : ℂ))) / 2) =
      (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ^ j := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hρ : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (q : ℂ) ^ (((n : ℂ) - 1) / 2) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
    push_cast
    rfl
  rw [hρ, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast (q : ℂ) (j.choose 2), ← Complex.cpow_add _ _ hq0,
    Nat.cast_choose_two]
  congr 1
  ring

theorem UpperTheory.Gal.CertificateRingHomMap.pRootsAlg_of :
    UpperTheory.Gal.CertificateRingHomMap.RootsAlg := by
  intro q n hq B hB a c ϑ h
  refine ⟨?_, ?_⟩
  · have h0 := h 0 (Nat.zero_le n)
    simpa [GlobalTheory.LFun.satEig, Multiset.esymm] using h0
  · set ρ : ℂ := (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hρ
    set s : Multiset ℂ := B.map (fun b : ℂˣ => (b : ℂ)) with hs
    have hcard : Multiset.card s = n := by simp [hs, hB]
    have e1 : (UpperTheory.V.Af.algSat n q B).map (· * c) = s.map (fun x => (ρ * c) • x) := by
      have e0 : UpperTheory.V.Af.algSat n q B = s.map (fun α => ρ * α) := by
        show Multiset.map _ (B.bind fun b => ({(b : ℂ)} : Multiset ℂ)) = _
        rw [Multiset.bind_singleton]
      rw [e0, Multiset.map_map]
      refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply, smul_eq_mul]
      ring
    have e2 : Multiset.card (s.map (fun x => (ρ * c) • x)) = n := by simp [hcard]
    rw [e1, UpperTheory.Gal.crystallineComparison.rootPol, Multiset.prod_X_sub_X_eq_sum_esymm, e2, Finset.mul_sum, UpperTheory.Gal.crystallineComparison.heckePol]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hk : _ = ρ ^ j := cpow_key q n j hq
    rw [h j hjn, ← Multiset.pow_smul_esymm, smul_eq_mul]
    have e3 : (-1 : ℂ) ^ j * (q : ℂ) ^ (j.choose 2) * (a * GlobalTheory.LFun.satEig q n B j * c ^ j) =
        a * ((-1) ^ j * ((ρ * c) ^ j * s.esymm j)) := by
      have e4 : GlobalTheory.LFun.satEig q n B j = (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - (j : ℂ))) / 2) * s.esymm j := rfl
      rw [e4, mul_pow]
      linear_combination ((-1) ^ j * a * s.esymm j * c ^ j) * hk
    rw [e3]
    simp only [map_mul, map_pow, map_neg, map_one]
    ring
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.LFun (KGL IsSatVecGL heckeVec satEig)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

theorem invT_val {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : (invT n R g).val = (g⁻¹).valᵀ := rfl

@[simp] theorem invT_invT' {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : invT n R (invT n R g) = g := by
  apply Units.ext
  rw [invT_val, ← map_inv, invT_val, inv_inv, transpose_transpose]

theorem invT_mem_Sim {A B : Type} [CommRing A] [CommRing B] {σ : A →+* A} {i : B →+* A} {n : ℕ} {p : GL (Fin n) A × Bˣ}
    (h : p ∈ Sim σ i n) : (invT n A p.1, p.2⁻¹) ∈ Sim σ i n := by
  have h1 := mem_Sim.1 h
  have h2 : p.1.valᵀ * p.1.val.map σ = i p.2 • (1 : Matrix (Fin n) (Fin n) A) := by
    have := congrArg transpose h1
    rwa [transpose_mul, transpose_transpose, transpose_smul, transpose_one] at this
  have h3 : i (p.2⁻¹ : Bˣ) * i p.2 = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have h4 : (p.1⁻¹).valᵀ * p.1.valᵀ = 1 := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  have h5 : (p.1⁻¹).val.map σ * p.1.val.map σ = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have h6 : p.1.val.map σ = i p.2 • (p.1⁻¹).valᵀ := by
    rw [← Matrix.one_mul (p.1.val.map σ), ← h4, Matrix.mul_assoc, h2, Matrix.mul_smul, Matrix.mul_one]
  refine mem_Sim.2 ?_
  show (((p.1⁻¹).valᵀ).map σ)ᵀ * (p.1⁻¹).valᵀ = i (p.2⁻¹ : Bˣ) • 1
  rw [transpose_map, transpose_transpose, ← h5, h6, Matrix.mul_smul, smul_smul, h3, one_smul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def th : GUf E n →* GUf E n :=
  (((invT n (Af E)).prodMap invMonoidHom).comp (GUf E n).subtype).codRestrict _ fun g => invT_mem_Sim g.2

def th0 : Gam0 E n →* Gam0 E n :=
  (((invT n E).prodMap invMonoidHom).comp (Gam0 E n).subtype).codRestrict _ fun g =>
    ⟨invT_mem_Sim g.2.1, (Units.posSubgroup ℚ).inv_mem g.2.2⟩

@[simp] theorem sim_th (g : GUf E n) : sim (th g) = (sim g)⁻¹ := rfl

@[simp] theorem comp_th (w : Plc E) (g : GUf E n) : comp w (th g) = invT n _ (comp w g) := GlobalTheory.SplitPts.invT_map _ _

@[simp] theorem th_th (g : GUf E n) : th (th g) = g := Subtype.ext (Prod.ext (invT_invT' _) (inv_inv _))

theorem th_rat (γ : Gam0 E n) : th (rat γ) = rat (th0 γ) :=
  Subtype.ext (Prod.ext (GlobalTheory.SplitPts.invT_map _ _).symm (map_inv (Units.map (algebraMap ℚ AfQ).toMonoidHom) _).symm)

theorem guf_ext {g g' : GUf E n} (h1 : sim g = sim g') (h2 : ∀ w, comp w g = comp w g') : g = g' :=
  Subtype.ext (Prod.ext (Units.ext (GlobalTheory.SplitPts.matAf_ext fun w => congrArg Units.val (h2 w))) h1)

theorem invT_mem_KGL {w : Plc E} {y : GLw n w} (h : y ∈ KGL w (n := n)) : invT n _ y ∈ KGL w (n := n) := by
  obtain ⟨z, rfl⟩ := h
  exact ⟨invT n _ z, GlobalTheory.SplitPts.invT_map _ z⟩

def levT (Kw : ∀ w : Plc E, Subgroup (GLw n w)) : ∀ w : Plc E, Subgroup (GLw n w) := fun w => (Kw w).comap (invT n _)

theorem th_mem_lev {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} {k : GUf E n} :
    th k ∈ lev S Kw ↔ k ∈ lev S (levT Kw) := by
  simp only [mem_lev, sim_th, comp_th, inv_mem_iff, levT, Subgroup.mem_comap]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₃_congr fun w _ _ => ⟨fun h => ?_, invT_mem_KGL⟩
  simpa using invT_mem_KGL h

def ThLoc : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
  (∀ (w : Plc E) (hw : IsSplitAt w) (y : GLw n w), th (loc hw y) = loc hw (invT n _ y)) ∧
    (0 < n → ∀ (x : E) (w : Plc E) (z : GUf E n), IsCen x w z → th z = z⁻¹)

end UpperTheory.Gal.CertificateRingHomMap

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pLocMem_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocMem := by
  intro hIC hLC E _ _ _ n S Kw w hw hcw y
  obtain ⟨-, hap, -, -, hcc, -⟩ := hLC E n w hw
  have hsim : sim (loc hw y) ∈ ZU := by
    rw [sim_loc]; exact ZU.one_mem
  have hone : ∀ u, u ≠ w → u ≠ cj w → comp u (loc hw y) = 1 := fun u h1 h2 =>
    comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩) y
  refine ⟨fun hwS hy => mem_lev.2 ⟨hsim, ?_, ?_⟩, fun hwS hy => mem_lev.2 ⟨hsim, ?_, ?_⟩⟩
  · intro u hu
    by_cases h1 : u = w
    · subst h1
      rw [comp_loc]; exact hy
    · have h2 : u ≠ cj w := fun h => hcw (h ▸ hu)
      rw [hone u h1 h2]; exact (Kw u).one_mem
  · intro u hu hcu
    have h1 : u ≠ w := fun h => hu (h ▸ hwS)
    have h2 : u ≠ cj w := fun h => hcu (by rw [h, hcc]; exact hwS)
    rw [hone u h1 h2]; exact (GlobalTheory.LFun.KGL u (n := n)).one_mem
  · intro u hu
    have h1 : u ≠ w := fun h => hwS (h ▸ hu)
    have h2 : u ≠ cj w := fun h => hcw (h ▸ hu)
    rw [hone u h1 h2]; exact (Kw u).one_mem
  · intro u hu hcu
    by_cases h1 : u = w
    · subst h1
      rw [comp_loc]; exact hy
    · by_cases h2 : u = cj w
      · subst h2
        exact hIC E n (loc hw y) w hsim (by rw [comp_loc]; exact hy)
      · rw [hone u h1 h2]; exact (GlobalTheory.LFun.KGL u (n := n)).one_mem
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pXiScalar_of :
    UpperTheory.Gal.CertificateRingHomMap.XiScalar := by
  intro E _ _ _ n W j y s t hy v
  have hy' : y = Formalism.L2.Col.brpSc E t := Units.ext (by rw [hy, Formalism.L2.Col.brpSc_coe])
  have hinv : y⁻¹ = Formalism.L2.Col.brpSc E t⁻¹ := by
    rw [hy']
    exact (map_inv (Units.map (algebraMap E (Matrix (Fin n) (Fin n) E) : E →* Matrix (Fin n) (Fin n) E)) t).symm
  have hemb : embAll E n y⁻¹ = fun u => Formalism.L2.Col.brpSc ℂ (Units.map (u.embedding : E →* ℂ) t⁻¹) := by
    funext u
    ext i k
    rw [hinv]
    change ((((Formalism.L2.Col.brpSc E t⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E).map u.embedding) i k = _
    rw [Formalism.L2.Col.brpSc_coe, Formalism.L2.Col.brpSc_coe]
    by_cases h : i = k <;> simp [Matrix.one_apply, h]
  have hr := Formalism.L2.Col.tensorWeights_scalar_action (K := ℂ) W (fun u => Units.map (u.embedding : E →* ℂ) t⁻¹)
  rw [← hemb] at hr
  simp only [xi, MonoidHom.coe_mk, OneHom.coe_mk, Representation.dual_apply]
  rw [MonoidHom.comp_apply, hr]
  ext x
  simp [Module.Dual.transpose_apply, smul_smul]
end
