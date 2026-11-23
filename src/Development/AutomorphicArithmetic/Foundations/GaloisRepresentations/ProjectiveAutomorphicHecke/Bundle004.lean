module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
public import GroundTheory.GlobalFields.Adele.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import GroundTheory.GlobalFields.Adele.Bundle002

@[expose] public section

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.LocalCommutativity

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem rel (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := mem_Sim.1 k.2
  have h2 := congrArg (RingHom.mapMatrix (pLoc E u)) h
  rw [map_mul] at h2
  refine h2.trans ?_
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

private theorem gu_ext {a b : GUf E n} (hs : sim a = sim b) (hc : ∀ u, comp u a = comp u b) : a = b := by
  refine Subtype.ext (Prod.ext (Units.ext (GlobalTheory.SplitPts.matAf_ext fun u => ?_)) hs)
  exact congrArg Units.val (hc u)

private theorem comm_scalar {R : Type} [CommRing R] (M X : Matrix (Fin n) (Fin n) R)
    (ho : ∀ i j, i ≠ j → M i j = 0) (hd : ∀ i j, M i i = M j j) : M * X = X * M := by
  have e : M = Matrix.diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, ho i j hij]
  ext i j
  rw [e, Matrix.diagonal_mul, Matrix.mul_diagonal, hd i j, mul_comm]

end UpperTheory.Gal.CertificateRingHomMap.LocalCommutativity

open UpperTheory.Gal.CertificateRingHomMap.LocalCommutativity in
theorem UpperTheory.Gal.CertificateRingHomMap.pLocComm_of :
    UpperTheory.Gal.CertificateRingHomMap.LocComm := by
  intro E _ _ _ n w hw
  obtain ⟨hne, hund, hover⟩ := GlobalTheory.SplitPts.over_split hw
  have hcc : cj (cj w) = w := GlobalTheory.SplitPts.conjSrc_conjSrc_cm w
  have hap : ∀ u, GlobalTheory.Cong.Apart u w ↔ u ≠ w ∧ u ≠ cj w := by
    intro u
    constructor
    · intro h
      exact ⟨fun e => h (by rw [e]), fun e => h (by rw [e]; exact hund)⟩
    · rintro ⟨h1, h2⟩ h
      rcases hover u h with e | e
      · exact h1 e
      · exact h2 e
  refine ⟨?_, hap, hne, ⟨w, hne.symm, hund.symm⟩, hcc, ?_⟩
  · intro k hk y
    refine gu_ext (by rw [map_mul, map_mul]; exact mul_comm _ _) fun u => ?_
    rw [map_mul, map_mul]
    by_cases h1 : u = w
    · subst h1
      rw [hk, one_mul, mul_one]
    by_cases h2 : u = cj w
    · subst h2
      have r := rel k w
      rw [hk, Units.val_one, Matrix.mul_one] at r
      have r' := congrArg Matrix.transpose r
      rw [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at r'
      have hent : ∀ i j, conjLoc (GlobalTheory.SplitPts.conjE E) w ((comp (cj w) k).val i j) = _ :=
        fun i j => congrFun (congrFun r' i) j
      have hinj := (conjLoc (GlobalTheory.SplitPts.conjE E) w).injective
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul]
      refine comm_scalar _ _ (fun i j hij => hinj ?_) (fun i j => hinj ?_)
      · rw [hent i j, map_zero]; simp [hij]
      · rw [hent i i, hent j j]; simp
    · rw [comp_loc_of_apart hw ((hap u).2 ⟨h1, h2⟩), mul_one, one_mul]
  · unfold locU
    rw [hund]
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap.LevelShrinking

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem comm_of_cLoc {w : Plc E} (hw : IsSplitAt w) (z : UA E n) (hz : cLoc w z = 1)
    (y : UA E n) (hy : y ∈ locU n w) : y * z = z * y := by
  have hyf := (Subgroup.mem_inf.1 hy).1
  have hyo := (Subgroup.mem_inf.1 hy).2
  have hc : z * y * z⁻¹ * y⁻¹ ∈ locU n w := by
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
    · have h1 : cInf y = 1 := MonoidHom.mem_ker.1 hyf
      exact MonoidHom.mem_ker.2 (by simp [h1])
    · have h1 : cLoc u y = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hyo u) hu)
      exact MonoidHom.mem_ker.2 (by simp [h1])
  have h1 := GlobalTheory.SplitPts.eq_one_of_cLoc hw ⟨_, hc⟩ (by simp [hz])
  have h2 : z * y * z⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h1
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h2)).symm

private def CJ {w : Plc E} (J : Subgroup (GLw n w)) : Subgroup (UA E n) := locU n w ⊓ J.comap (cLoc w)

private theorem isCompact_CJ {w : Plc E} (hw : IsSplitAt w) (J : Subgroup (GLw n w))
    (hJ : IsCompact (J : Set (GLw n w))) : IsCompact (CJ J : Set (UA E n)) := by
  have hc : Continuous fun x : GLw n w => (((locE hw).symm x : locU n w) : UA E n) :=
    continuous_subtype_val.comp (locE hw).symm.continuous
  have he : (CJ J : Set (UA E n)) = (fun x : GLw n w => (((locE hw).symm x : locU n w) : UA E n)) '' (J : Set (GLw n w)) := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨cLoc w g, h2, ?_⟩
      have : (locE hw).symm (cLoc w g) = ⟨g, h1⟩ := by
        apply (locE hw).injective
        rw [ContinuousMulEquiv.apply_symm_apply, locE_apply]
      simp [this]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨((locE hw).symm x).2, ?_⟩
      show cLoc w (locF hw x).1 ∈ J
      rw [cLoc_locF]
      exact hx
  rw [he]
  exact hJ.image hc

private theorem finite_index {w : Plc E} (hw : IsSplitAt w) (J : Subgroup (GLw n w))
    (hJ : IsCompact (J : Set (GLw n w))) (φ : UA E n → ℂ) (hφ : IsAutFormU φ) :
    ∃ N : Subgroup (CJ J : Subgroup (UA E n)), N.FiniteIndex ∧ ∀ k ∈ N, RU E n (k : UA E n) φ = φ := by
  haveI : CompactSpace (CJ J : Subgroup (UA E n)) := isCompact_iff_compactSpace.1 (isCompact_CJ hw J hJ)
  let N : Subgroup (CJ J : Subgroup (UA E n)) :=
    { carrier := {k | RU E n (k : UA E n) φ = φ}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        show RU E n ((a * b : CJ J) : UA E n) φ = φ
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        show RU E n ((a⁻¹ : CJ J) : UA E n) φ = φ
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hle : (CJ J : Subgroup (UA E n)) ≤ finU (E := E) (n := n) := fun k hk => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).1
  have hop : IsOpen (N : Set (CJ J : Subgroup (UA E n))) :=
    hφ.level.preimage (f := fun k : (CJ J : Subgroup (UA E n)) => (⟨k.1, hle k.2⟩ : finU (E := E) (n := n)))
      (Continuous.subtype_mk continuous_subtype_val _)
  haveI := Subgroup.quotient_finite_of_isOpen N hop
  exact ⟨N, Subgroup.finiteIndex_of_finite_quotient, fun k hk => hk⟩

private theorem step_core (π : AutSub E n) (W : Wt E n) (f : algForms W) {w : Plc E} (hw : IsSplitAt w)
    (hf : f ∈ π.finPart W) (r : UA E n →₀ ℂ) (hr : ∀ g ∈ r.support, g ∈ locU n w) :
    ∃ f' ∈ π.finPart W, (∀ v, f'.1 v = r.sum fun g a => a • RU E n g (f.1 v)) ∧
      ∀ u : finU (E := E) (n := n), cLoc w u.1 = 1 → algRep W u f = f → algRep W u f' = f' := by
  have hle : locU n w ≤ finU (E := E) (n := n) := inf_le_left
  let F : r.support → algForms W := fun g => r g.1 • algRep W ⟨g.1, hle (hr _ g.2)⟩ f
  have hval : ∀ v, (∑ g : r.support, F g).1 v = r.sum fun g a => a • RU E n g (f.1 v) := by
    intro v
    rw [Finsupp.sum, ← Finset.sum_coe_sort r.support, Submodule.coe_sum, LinearMap.sum_apply]
    rfl
  refine ⟨∑ g : r.support, F g, AutSub.mem_finPart.2 fun v => ?_, hval, fun u hu hfix => ?_⟩
  · rw [hval]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (π.isAut.stable _ _ (AutSub.mem_finPart.1 hf v))

  · rw [map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    have hcm : u * (⟨g.1, hle (hr _ g.2)⟩ : finU (E := E) (n := n)) = ⟨g.1, hle (hr _ g.2)⟩ * u :=
      Subtype.ext (comm_of_cLoc hw u.1 hu g.1 (hr _ g.2)).symm
    simp only [F]
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, hcm, map_mul, Module.End.mul_apply, hfix]

private theorem mem_lev_off (hC : LocComm) {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} {w : Plc E}
    (hw : IsSplitAt w) (hwS : w ∈ S) (hcj : cj w ∉ S) {J : Subgroup (GLw n w)} (u : finU (E := E) (n := n))
    (hu : ofU u ∈ lev S (Function.update Kw w J)) (x : GLw n w) (u' : finU (E := E) (n := n)) (hx : u = locF hw x * u')
    (h1 : cLoc w u'.1 = 1) : ofU u' ∈ lev S Kw := by
  obtain ⟨-, hap, -, -, hcc, -⟩ := hC E n w hw
  obtain ⟨-, hu2, hu3⟩ := mem_lev.1 hu
  have hsame : ∀ t : Plc E, GlobalTheory.Cong.Apart t w → comp t (ofU u') = comp t (ofU u) := by
    intro t ht
    have h2 : comp t (loc hw x) = 1 := comp_loc_of_apart hw ht x
    rw [hx, map_mul, map_mul]
    have h3 : comp t (ofU (locF hw x)) = 1 := h2
    rw [h3, one_mul]
  refine mem_lev.2 ⟨by rw [sim_ofU]; exact one_mem _, fun t ht => ?_, fun t ht hct => ?_⟩
  · by_cases htw : t = w
    · subst htw
      rw [comp_ofU, h1]
      exact one_mem _
    · have hne : t ≠ cj w := fun h => hcj (h ▸ ht)
      rw [hsame t ((hap t).2 ⟨htw, hne⟩)]
      have := hu2 t ht
      rwa [Function.update_of_ne htw] at this
  · have htw : t ≠ w := fun h => ht (h ▸ hwS)
    have hne : t ≠ cj w := fun h => hct (by rw [h, hcc]; exact hwS)
    rw [hsame t ((hap t).2 ⟨htw, hne⟩)]
    exact hu3 t ht hct

end UpperTheory.Gal.CertificateRingHomMap.LevelShrinking

open UpperTheory.Gal.CertificateRingHomMap.LevelShrinking in
theorem UpperTheory.Gal.CertificateRingHomMap.pStepAt_of :
    UpperTheory.Gal.CertificateRingHomMap.LocAdj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.StepAt := by
  intro hA hC _ E _ _ _ n π W f hf hf0 S Kw w hw hwS hcj hfix J χ hJc hT
  obtain ⟨φ, hφπ, hφ0, hφ⟩ := hT
  let χ' : (CJ J : Subgroup (UA E n)) →* ℂˣ :=
    χ.comp (((cLoc w).comp (CJ J : Subgroup (UA E n)).subtype).codRestrict J fun k => (Subgroup.mem_inf.1 k.2).2)
  have hf1 : f.1 ≠ 0 := fun h => hf0 (Subtype.ext h)
  obtain ⟨r, hrH, ⟨v₀, hv₀⟩, hrχ⟩ := hA (UA E n) (UA E n → ℂ) W.Sp (RU E n) π.V π.isAut.stable π.isAut.irred
    (locU n w) (CJ J) inf_le_left
    (fun g => ⟨(locF hw (cLoc w g)).1, locF_mem hw _, (locF hw (cLoc w g)).1⁻¹ * g,
      fun y hy => (comm_of_cLoc hw _ (by simp) y hy).symm, by simp⟩)
    (fun ψ hψ => finite_index hw J hJc ψ (π.isAut.aut ψ hψ)) χ'
    ⟨φ, hφπ, hφ0, fun k => hφ k.1 (Subgroup.mem_inf.1 k.2).1 (Subgroup.mem_inf.1 k.2).2⟩
    f.1 hf1 (AutSub.mem_finPart.1 hf)
  obtain ⟨f', hf', hval, hoff⟩ := step_core π W f hw hf r hrH
  refine ⟨f', hf', fun h => hv₀ ?_, fun u hu h => ?_⟩
  · rw [← hval, h]
    rfl
  · set x := cLoc w u.1 with hxdef
    set a := locF hw x with hadef
    have hax : cLoc w a.1 = x := cLoc_locF hw x
    have h1 : cLoc w ((a⁻¹ * u : finU (E := E) (n := n)) : UA E n) = 1 := by
      have : ((a⁻¹ * u : finU (E := E) (n := n)) : UA E n) = a.1⁻¹ * u.1 := rfl
      rw [this, map_mul, map_inv, hax, ← hxdef, inv_mul_cancel]
    have hu' : u = a * (a⁻¹ * u) := by group
    have hfix' : algRep W (a⁻¹ * u) f = f :=
      hfix _ (mem_lev_off hC hw hwS hcj u hu x _ hu' h1)
    have hstep := hoff _ h1 hfix'
    have hak : a.1 ∈ (CJ J : Subgroup (UA E n)) :=
      Subgroup.mem_inf.2 ⟨locF_mem hw x, by show cLoc w a.1 ∈ J; rw [hax]; exact h⟩
    have hχ : ((χ' ⟨a.1, hak⟩ : ℂˣ) : ℂ) = ((χ ⟨x, h⟩ : ℂˣ) : ℂ) := by
      have : (((cLoc w).comp (CJ J : Subgroup (UA E n)).subtype).codRestrict J
          fun k => (Subgroup.mem_inf.1 k.2).2) ⟨a.1, hak⟩ = ⟨x, h⟩ := Subtype.ext hax
      simp only [χ', MonoidHom.comp_apply, this]
    have e : algRep W u f' = algRep W a f' := by
      conv_lhs => rw [hu', map_mul, Module.End.mul_apply, hstep]
    rw [e]
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    have h2 := hrχ ⟨a.1, hak⟩ v
    rw [← hval, hχ] at h2
    exact h2

end
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem comp_rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) •
        (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := congrArg (RingHom.mapMatrix (pLoc E u)) (mem_Sim.1 k.2)
  rw [map_mul] at h
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, sim]

private theorem val_sim {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (hk : sim k ∈ ZU) (u : Plc E) :
    Valued.v (pLoc E u (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ))) = 1 := by
  show Valued.v (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ) u) = 1
  rw [GroundTheory.Global.AdeleBaseChange.finiteAdeleMap_apply, GroundTheory.Global.SemiLocal.valued_completionMap,
    hk (GroundTheory.Global.AdeleBaseChange.below ℚ u), one_pow]

theorem UpperTheory.Gal.CertificateRingHomMap.pIntConj_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj := by
  intro E _ _ _ n k w hs ha
  have hmap : ∀ g : Matrix.GeneralLinearGroup (Fin n) ((cj w).adicCompletion E),
      Matrix.GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) g ∈ GlobalTheory.LFun.KGL w n ↔
        g ∈ GlobalTheory.LFun.KGL (cj w) n := by
    intro g
    have hv : ∀ x : (cj w).adicCompletion E,
        conjLoc (GlobalTheory.SplitPts.conjE E) w x ∈ w.adicCompletionIntegers E ↔
          x ∈ (cj w).adicCompletionIntegers E := fun x => by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
        (conjLoc_spec (GlobalTheory.SplitPts.conjE E) w).2.2 x]
    rw [GlobalTheory.AdelicU.mem_GLint_iff, GlobalTheory.AdelicU.mem_GLint_iff]
    refine and_congr (forall₂_congr fun a b => hv _) (forall₂_congr fun a b => ?_)
    rw [← map_inv]
    exact hv _
  rw [← hmap]
  set s := pLoc E w (GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E ((sim k : AfQˣ) : AfQ)) with hsdef
  have hv : Valued.v s = 1 := val_sim k hs w
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  set a := comp w k with hadef
  set G := Matrix.GeneralLinearGroup.map (n := Fin n) (conjLoc (GlobalTheory.SplitPts.conjE E) w) (comp (cj w) k) with hG
  have hrel : (G.val)ᵀ * a.val = s • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := comp_rel k w
  have hGt : (G.val)ᵀ = s • (a⁻¹).val := by
    calc (G.val)ᵀ = (G.val)ᵀ * (a.val * (a⁻¹).val) := by rw [Units.mul_inv, Matrix.mul_one]
      _ = ((G.val)ᵀ * a.val) * (a⁻¹).val := by rw [Matrix.mul_assoc]
      _ = _ := by rw [hrel, smul_mul_assoc, Matrix.one_mul]
  have hGi : (G⁻¹).val = s⁻¹ • (a.val)ᵀ := by
    have h1 : G.val * (s⁻¹ • (a.val)ᵀ) = 1 := by
      have h2 : a.val * (G.val)ᵀ = s • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
        rw [hGt, Matrix.mul_smul, Units.mul_inv]
      have h3 := congrArg Matrix.transpose h2
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at h3
      rw [Matrix.mul_smul, h3, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    calc (G⁻¹).val = (G⁻¹).val * (G.val * (s⁻¹ • (a.val)ᵀ)) := by rw [h1, Matrix.mul_one]
      _ = ((G⁻¹).val * G.val) * (s⁻¹ • (a.val)ᵀ) := by rw [Matrix.mul_assoc]
      _ = _ := by rw [Units.inv_mul, Matrix.one_mul]
  obtain ⟨ha1, ha2⟩ := (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w a).1 ha
  refine (GlobalTheory.BCT.GlobLev.mem_KGL_iff_val w G).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · have h := congrFun (congrFun hGt j) i
    rw [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [h, map_mul, hv, one_mul]
    exact ha2 j i
  · rw [hGi, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hv, inv_one, one_mul, Matrix.transpose_apply]
    exact ha1 j i
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

open GroundTheory.Global.AdeleBaseChange in
private theorem rel {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (k : GUf E n) (u : Plc E) :
    ((comp (cj u) k).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) u))ᵀ * (comp u k).val =
      pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ)) • (1 : Matrix (Fin n) (Fin n) (u.adicCompletion E)) := by
  have h := mem_Sim.1 k.2
  have h2 := congrArg (RingHom.mapMatrix (pLoc E u)) h
  rw [map_mul] at h2
  refine Eq.trans ?_ (h2.trans ?_)
  · congr 1
  · ext i j
    by_cases hij : i = j
    · subst hij
      simp [RingHom.mapMatrix_apply, sim, Matrix.one_apply]
    · simp [RingHom.mapMatrix_apply, sim, Matrix.one_apply, hij]

open GroundTheory.Global.AdeleBaseChange in
private theorem val_le {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (hn : 0 < n) (k : GUf E n)
    (hk : ∀ w, comp w k ∈ GlobalTheory.LFun.KGL w (n := n)) (u : Plc E) :
    Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) ≤ 1 := by
  have h := congrFun (congrFun (rel k u) ⟨0, hn⟩) ⟨0, hn⟩
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h
  rw [← h]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [map_mul, Matrix.transpose_apply, Matrix.map_apply, (conjLoc_spec _ u).2.2]
  exact mul_le_one' (((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val _ _).1 (hk _)).1 _ _)
    (((GlobalTheory.BCT.GlobLev.mem_KGL_iff_val _ _).1 (hk _)).1 _ _)

open GroundTheory.Global.AdeleBaseChange in
theorem UpperTheory.Gal.CertificateRingHomMap.pIntSim_of :
    UpperTheory.Gal.CertificateRingHomMap.IntSim := by
  intro E _ _ _ n hn k hk v
  obtain ⟨P, hPm, hPo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  let u : Plc E := ⟨P, hPm.isPrime, hP0⟩
  have hu : below ℚ u = v := (below_eq_iff u v).2 hPo
  subst hu
  have h1 := val_le hn k hk u
  have h2 := val_le hn k⁻¹ (fun w => by rw [map_inv]; exact inv_mem (hk w)) u
  have hmul : pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ)) * pLoc E u (finiteAdeleMap ℚ E (sim k⁻¹ : AfQˣ)) = 1 := by
    rw [← map_mul, ← map_mul, map_inv, Units.mul_inv, map_one, map_one]
  have h3 : Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) = 1 := by
    refine le_antisymm h1 ?_
    calc (1 : _) = Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) *
          Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k⁻¹ : AfQˣ))) := by
            rw [← map_mul, hmul, map_one]
      _ ≤ Valued.v (pLoc E u (finiteAdeleMap ℚ E (sim k : AfQˣ))) * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  have h4 : Valued.v (GroundTheory.Global.SemiLocal.completionMap (below ℚ u) u (((sim k : AfQˣ) : AfQ) (below ℚ u))) = 1 := h3
  rw [GroundTheory.Global.SemiLocal.valued_completionMap] at h4
  exact (pow_eq_one_iff.1 h4).resolve_right (Ideal.ramificationIdx_pos (R := 𝓞 ℚ) u.asIdeal).ne'
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem isCompact_ZU : IsCompact (ZU : Set AfQˣ) := by
  have hO := GroundTheory.Global.isCompact_integralFiniteAdeles ℚ
  have hB' : IsCompact (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) : Set AfQᵐᵒᵖ) :=
    MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hO
  have e : (ZU : Set AfQˣ) = Units.embedProduct _ ⁻¹'
      ((GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ) ×ˢ
        (MulOpposite.unop ⁻¹' (GroundTheory.Global.integralFiniteAdeles (𝓞 ℚ) ℚ : Set AfQ))) := by
    ext s
    simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply, MulOpposite.unop_op,
      GroundTheory.Global.mem_integralFiniteAdeles]
    constructor
    · intro h
      have h2 := (ZU.inv_mem h)
      exact ⟨fun v => (h v).le, fun v => (h2 v).le⟩
    · rintro ⟨h1, h2⟩ v
      have h3 : Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) = 1 := by
        rw [← map_mul]
        show Valued.v (((s : AfQ) * (↑s⁻¹ : AfQ)) v) = 1
        rw [Units.mul_inv]; exact map_one _
      refine le_antisymm (h1 v) ?_
      calc (1 : _) = Valued.v ((s : AfQ) v) * Valued.v ((↑s⁻¹ : AfQ) v) := h3.symm
        _ ≤ Valued.v ((s : AfQ) v) * 1 := mul_le_mul_right (h2 v) _
        _ = _ := mul_one _
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage (hO.prod hB')

private theorem isClosed_GUf (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    IsClosed (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) := by
  have hl : Continuous fun p : GL (Fin n) (Af E) × AfQˣ =>
      (p.1.val.map (conjFin (GlobalTheory.SplitPts.conjE E)))ᵀ * p.1.val :=
    ((Units.continuous_val.comp continuous_fst).matrix_map (continuous_conjFin _)).matrix_transpose.matrix_mul
      (Units.continuous_val.comp continuous_fst)
  have hr : Continuous fun p : GL (Fin n) (Af E) × AfQˣ =>
      GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ) • (1 : Matrix (Fin n) (Fin n) (Af E)) :=
    Continuous.smul (f := fun p : GL (Fin n) (Af E) × AfQˣ => GroundTheory.Global.AdeleBaseChange.finiteAdeleMap ℚ E (p.2 : AfQ))
      (g := fun _ => (1 : Matrix (Fin n) (Fin n) (Af E)))
      (GroundTheory.Global.AdeleBaseChange.continuous_finiteAdeleMap.comp (Units.continuous_val.comp continuous_snd))
      continuous_const
  exact isClosed_eq hl hr

theorem UpperTheory.Gal.CertificateRingHomMap.pIntCompact_of :
    UpperTheory.Gal.CertificateRingHomMap.IntCompact := by
  intro E _ _ _ n
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have e : Subtype.val '' (lev (E := E) (n := n) ∅ (fun _ => ⊤) : Set (GUf E n)) =
      (GUf E n : Set (GL (Fin n) (Af E) × AfQˣ)) ∩ ((GlobalTheory.EulerTw.Kglob E n : Set _) ×ˢ (ZU : Set AfQˣ)) := by
    ext p
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨h1, -, h3⟩ := mem_lev.1 hk
      exact ⟨k.2, GlobalTheory.EulerTwRestr.mem_Kglob.2 fun w => h3 w (by simp) (by simp), h1⟩
    · rintro ⟨hp, h1, h2⟩
      refine ⟨⟨p, hp⟩, mem_lev.2 ⟨h2, by simp, fun w _ _ => GlobalTheory.EulerTwRestr.mem_Kglob.1 h1 w⟩, rfl⟩
  rw [e]
  exact ((GlobalTheory.EulerTwRestr.isCompact_Kglob (E := E) (n := n)).prod isCompact_ZU).inter_left (isClosed_GUf E n)
end
