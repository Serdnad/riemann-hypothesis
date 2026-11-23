module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.IsCondAt
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OneNonUnit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem hasSatGL_of_invT {E : Type} [Field E] [NumberField E] {a : ℕ} {w w' : HeightOneSpectrum (𝓞 E)}
    (c : w.adicCompletion E ≃+* w'.adicCompletion E) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (hq : Formalism.UG.qV E w' = Formalism.UG.qV E w)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin a) (w'.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' (GlobalTheory.LFun.ConjPlace.invT c a g) (T x) = T (ρ g x)) {B : Multiset ℂˣ}
    (h : GlobalTheory.LFun.HasSatGL w ρ B) : GlobalTheory.LFun.HasSatGL w' ρ' (B.map (·⁻¹)) := by
  have hK := GlobalTheory.LFun.ConjPlace.mem_iff_invT (n := a) c (GlobalTheory.LFun.ConjPlace.map_mem_Ov_iff c hc)
  have hf : ∀ g y, T.toLinearMap ((ρ.comp (GlobalTheory.LFun.ConjPlace.invT c a).symm.toMonoidHom) g y) =
      ρ' g (T.toLinearMap y) := fun g y => by
    change T (ρ ((GlobalTheory.LFun.ConjPlace.invT c a).symm g) y) = ρ' g (T y)
    rw [← hT, MulEquiv.apply_symm_apply]
  have key : ∀ x, GlobalTheory.LFun.IsSatVecGL w ρ x B → GlobalTheory.LFun.IsSatVecGL w' ρ' (T x) (B.map (·⁻¹)) := fun x hx =>
    (GlobalTheory.LFun.ConjPlace.isSatVecGL_invT c hc hq hx).map T.toLinearMap hf
      ((map_ne_zero_iff T T.injective).2 hx.1)
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := GlobalTheory.LGrp.mem_fixed.1 hy _ ((hK k).1 hk)
    rwa [hT] at this

private theorem theta_locGL {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : GL (Fin a) ((cPl w).adicCompletion E)) :
    thetaGL a (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g) =
      locGL E a w (thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) := by
  have key : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL a (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ v)
        (Matrix.GeneralLinearGroup.map (pLoc E (cPl v)) (locGL E a (cPl w) g))) := fun v =>
    GlobalTheory.ThetaPull.map_thetaGL (pLoc E v) (RingHom.id _) (RingHom.id _) (fun _ => rfl)
      (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g))
  have key2 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v) (thetaGL a (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      Matrix.GeneralLinearGroup.map (pLoc E v)
        (locGL E a w (thetaGL a (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g))) := fun v => by
    rw [key]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, pLoc_locGL]
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective _ e)), map_one, map_one]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin a) (v.adicCompletion E) => u.val i j) (key2 v)

private theorem conjLoc_surjective {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (conjLoc (IsCMField.complexConj E).toRingEquiv w) := fun y => by
  classical
  refine ⟨pLoc E _ (GlobalTheory.ThetaPull.cFin E (sLoc E w y)), ?_⟩
  rw [← pLoc_conjFin]
  exact (congrArg (pLoc E w) (GlobalTheory.ThetaPull.cFin_cFin _)).trans
    (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w y)

theorem UpperTheory.theta_satake_parameters_inverse :
    UpperTheory.V.Af.Bc.ThetaSat := by
  intro E _ _ _ n P w B h
  rw [CG.hasSat_mk] at h ⊢
  let c : (cPl w).adicCompletion E ≃+* w.adicCompletion E :=
    RingEquiv.ofBijective (conjLoc _ w) ⟨(conjLoc _ w).injective, conjLoc_surjective w⟩
  have hq : Formalism.UG.qV E w = Formalism.UG.qV E (cPl w) := by
    change Ideal.absNorm w.asIdeal = Ideal.absNorm (conjSrc (IsCMField.complexConj E).toRingEquiv w).asIdeal
    rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
    rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
    exact (Nat.card_congr (Ideal.quotientEquiv (w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).toRingHom) w.asIdeal (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv)
      (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv).symm
  let ρ' := (GlobalTheory.ThetaPull.thetaSub P).locRep w
  let T₀ : P.V ≃ₗ[ℂ] (GlobalTheory.ThetaPull.thetaSub P).V := (GlobalTheory.ThetaPull.pull E n).submoduleMap P.V
  have h0 : ∀ g x, ρ' (thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) (T₀ x) =
      T₀ (P.locRep (cPl w) g x) := fun g x => by
    rw [CuspSub.locRep_eq, CuspSub.locRep_eq, ← theta_locGL]
    exact Subtype.ext (GlobalTheory.ThetaPull.pull_act (.fin (locGL E n (cPl w) g)) x.1).symm
  let k := PhiU n (w.adicCompletion E)
  let S : (GlobalTheory.ThetaPull.thetaSub P).V ≃ₗ[ℂ] (GlobalTheory.ThetaPull.thetaSub P).V :=
    LinearEquiv.ofLinear (ρ' k⁻¹) (ρ' k) (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
  refine hasSatGL_of_invT c (conjLoc_spec _ w).2.2 hq (T₀.trans S) (fun g x => ?_) h
  have e : thetaGL n (RingHom.id _) (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) =
      k * GlobalTheory.LFun.ConjPlace.invT c n g * k⁻¹ := by
    have e1 : GlobalTheory.LFun.ConjPlace.invT c n g = GlobalTheory.CuspRep.invT n _ (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) :=
      Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)
    rw [e1]
    rfl
  change ρ' _ (ρ' k⁻¹ (T₀ x)) = ρ' k⁻¹ (T₀ _)
  rw [← h0, e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

section Hecke

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

private theorem isOpen_ker_kills {M : ℕ} (hM : 1 ≤ M) {φ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) :
    IsOpen (φ.ker : Set (_root_.Formalism.ConjugateSelfDual.G F Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := F) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ s fun ζ hζ => hs ζ hζ

private theorem exists_hchar_fin {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ)
    {M : ℕ} (hM : 1 ≤ M) {φ : _root_.Formalism.ConjugateSelfDual.G F Ω →* (Qbar l)ˣ} (hφ : KillsMu M φ) :
    ∃ χ : HChar F, IsAlgPos χ 0 ∧ IsLAdicOf art ι χ 0 φ := by
  have ho := isOpen_ker_kills hM hφ
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hfi : Finite (_root_.Formalism.ConjugateSelfDual.G F Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ ho
  have hpos : 0 < φ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  obtain ⟨χ, ⟨h1, h2⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι φ (continuous_of_isOpen_ker' φ ho) hpos
    (MonoidHom.ext fun s => by
      rw [MonoidHom.pow_apply, ← map_pow]
      exact φ.ker.pow_index_mem s)
  exact ⟨χ, isAlgPos_zero_of_orderDvd hpos h1, h2⟩

private theorem isAlgPos_mul {χ χ' : HChar F} {n n' : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) (h' : IsAlgPos χ' n') :
    IsAlgPos (χ * χ') (n + n') := fun k hk => by
  have e : (χ * χ').inf k = χ.inf k * χ'.inf k := rfl
  rw [e, Units.val_mul, h k hk, h' k hk, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_add₀ ((map_ne_zero φ).2 k.ne_zero) _ _).symm

private theorem isAlgPos_inv {χ : HChar F} {n : (F →+* ℂ) → ℤ} (h : IsAlgPos χ n) : IsAlgPos χ⁻¹ (-n) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm

private theorem exists_hchar_cyc {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ) (j : ℤ) :
    ∃ (χ : HChar F) (n : (F →+* ℂ) → ℤ), IsAlgPos χ n ∧ IsLAdicOf art ι χ n (cycBar F Ω l ^ j) := by
  have key : ∀ m : ℕ, ∃ (χ : HChar F) (n : (F →+* ℂ) → ℤ), IsAlgPos χ n ∧ IsLAdicOf art ι χ n (cycBar F Ω l ^ m) := fun m => by
    have h := GlobalTheory.Published.CharAboveModel.absPow_isAlgPos F m
    obtain ⟨μ, hμ, hL⟩ := ha.exists_isLAdicOf ι h
    have e : μ = cycBar F Ω l ^ m := GlobalTheory.Published.CharAboveModel.eq_cyc_pow ha hμ hL
    exact ⟨_, _, h, e ▸ hL⟩
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · simpa using key m
  · obtain ⟨χ, n, h1, h2⟩ := key m
    exact ⟨_, _, isAlgPos_inv h1, by simpa using h2.inv⟩

private theorem continuous_cyc {art : Ideles F →* Gab F Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ) :
    Continuous (cycBar F Ω l) := by
  have h := GlobalTheory.Published.CharAboveModel.absPow_isAlgPos F 1
  obtain ⟨μ, hμ, hL⟩ := ha.exists_isLAdicOf ι h
  have e : μ = cycBar F Ω l ^ 1 := GlobalTheory.Published.CharAboveModel.eq_cyc_pow ha hμ hL
  rw [pow_one] at e
  exact e ▸ hμ

end Hecke

theorem UpperTheory.exists_algebraic_heckeChar_cyclotomic :
    UpperTheory.V.Af.Bc.CycHecke := by
  intro H F Ω _ _ _ _ _ l _ ι wt θ hθ
  obtain ⟨art, ha⟩ := H F Ω
  obtain ⟨M, φ, hM, hφ, rfl⟩ := hθ
  obtain ⟨χ, h1, h2⟩ := exists_hchar_fin ha ι hM hφ
  obtain ⟨χ', n, h3, h4⟩ := exists_hchar_cyc ha ι wt
  refine ⟨?_, _, art, _, ha, isAlgPos_mul h3 h1, h4.mul h2⟩
  have hc : Continuous φ := continuous_of_isOpen_ker' φ (isOpen_ker_kills hM hφ)
  exact ((continuous_cyc ha ι).zpow wt).mul hc
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem dc_common {G : Type} [Group G] (K K' : Subgroup G) (x : G) :
    ∃ s : Finset (MulAction.orbit K (x : G ⧸ K')), ∀ (M : Type) [AddCommGroup M] [Module ℂ M]
      (ρ : Representation ℂ G M) (v : M), Hi.dc ρ K K' x v = ∑ q ∈ s, ρ (q : G ⧸ K').out v := by
  by_cases h : Finite (MulAction.orbit K (x : G ⧸ K'))
  · letI := Fintype.ofFinite (MulAction.orbit K (x : G ⧸ K'))
    refine ⟨Finset.univ, fun M _ _ ρ v => ?_⟩
    rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  · refine ⟨∅, fun M _ _ ρ v => ?_⟩
    rcases subsingleton_or_nontrivial M with hM | hM
    · exact Subsingleton.elim _ _
    have hs : (Function.support fun q : MulAction.orbit K (x : G ⧸ K') => ρ (q : G ⧸ K').out) = Set.univ := by
      refine Set.eq_univ_of_forall fun q hq => ?_
      have h1 : ρ ((q : G ⧸ K').out⁻¹ * (q : G ⧸ K').out) = 0 := by rw [map_mul, show ρ (q : G ⧸ K').out = 0 from hq, mul_zero]
      rw [inv_mul_cancel, map_one] at h1
      exact one_ne_zero h1
    rw [Hi.dc, finsum_of_infinite_support, Finset.sum_empty, LinearMap.zero_apply]
    rw [hs]
    exact fun hf => h (Set.finite_univ_iff.1 hf)

private theorem killed_of_mem_iSup {G V U ι J : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (T : J → V →ₗ[ℂ] V) (S : J → U →ₗ[ℂ] U)
    (hTS : ∀ j i u, f i (S j u) = T j (f i u))
    (hT : ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → ∀ j, ∀ x ∈ W, T j x ∈ W)
    (φ : V) (h0 : φ ≠ 0) (hK : ∀ j, T j φ = 0)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) : ∃ v : U, v ≠ 0 ∧ ∀ j, S j v = 0 := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hφ
  have key : ∀ s : Finset ι, ∀ W : Submodule ℂ V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → φ ∉ W →
      φ ∈ W ⊔ ⨆ i ∈ s, LinearMap.range (f i) → ∃ v : U, v ≠ 0 ∧ ∀ j, S j v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro W _ h1 h2; exact absurd (by simpa using h2) h1
    | insert i s _ ih =>
      intro W hW h1 h2
      rw [Finset.iSup_insert, ← sup_assoc] at h2
      by_cases h3 : φ ∈ W ⊔ LinearMap.range (f i)
      · obtain ⟨x, hx, _, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 h3
        have hv : f i v ∉ W := fun h => h1 (e ▸ add_mem hx h)
        have hc : W.comap (f i) = ⊥ := by
          refine (((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ).2 _ fun g u hu => ?_).resolve_right fun h => hv ?_
          · rw [Submodule.mem_comap, hf]; exact hW g _ hu
          · have : v ∈ W.comap (f i) := h ▸ Submodule.mem_top
            exact this
        refine ⟨v, fun h => hv (by rw [h, map_zero]; exact zero_mem _), fun j => ?_⟩
        have h4 : S j v ∈ W.comap (f i) := by
          have h5 := hK j
          rw [← e, map_add (f := _)] at h5
          rw [Submodule.mem_comap, hTS, eq_neg_of_add_eq_zero_right h5]
          exact neg_mem (hT W hW j x hx)
        rwa [hc, Submodule.mem_bot] at h4
      · refine ih _ (fun g y hy => ?_) h3 h2
        obtain ⟨x, hx, _, ⟨v, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add (f := _), ← hf]
        exact Submodule.add_mem_sup (hW g x hx) ⟨_, rfl⟩
  exact key s ⊥ (fun g x hx => by simp_all) (by simpa using h0) (by simpa using hs)

private theorem dc_eigen_descend {G V U ι : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G U) (hσ : σ.IsIrreducible) (f : ι → U →ₗ[ℂ] V)
    (hf : ∀ i g u, f i (σ g u) = ρ g (f i u)) (K : Subgroup G) (x : G) (lam : ℂ)
    (φ : V) (h0 : φ ≠ 0) (hK : φ ∈ Hi.fixd ρ K) (hl : Hi.dc ρ K K x φ = lam • φ)
    (hφ : φ ∈ ⨆ i, LinearMap.range (f i)) :
    ∃ v : U, v ≠ 0 ∧ v ∈ Hi.fixd σ K ∧ Hi.dc σ K K x v = lam • v := by
  obtain ⟨s, hs⟩ := dc_common K K x
  obtain ⟨v, hv0, hv⟩ := killed_of_mem_iSup ρ σ hσ f hf
    (fun j : Option K => j.elim (Hi.dc ρ K K x - lam • LinearMap.id) fun k => ρ k - LinearMap.id)
    (fun j : Option K => j.elim (Hi.dc σ K K x - lam • LinearMap.id) fun k => σ k - LinearMap.id)
    (by
      rintro (_ | k) i u

      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, map_sub, map_smul, hs,
        map_sum, hf]
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hf])
    (by
      rintro W hW (_ | k) y hy
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hs]
        exact sub_mem (Submodule.sum_mem _ fun q _ => hW _ _ hy) (W.smul_mem _ hy)
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply]
        exact sub_mem (hW _ _ hy) hy)
    φ h0
    (by
      rintro (_ | k)
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hl, sub_self]
      · simp only [Option.elim, LinearMap.sub_apply, LinearMap.id_apply]
        exact sub_eq_zero.2 (hK k k.2))
    hφ
  exact ⟨v, hv0, fun k hk => sub_eq_zero.1 (hv (some ⟨k, hk⟩)), sub_eq_zero.1 (hv none)⟩

theorem UpperTheory.hasUEigenvalue_of_locIsotypic :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (Af F)) V) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))), LocIsotypic ρ w σ → ∀ (c : ℕ) (lam : ℂ), HasU w (ρ.comp (locGL F 2 w)) c lam → HasU w σ.ρ c lam := by
  intro F _ _ w V _ _ ρ σ ⟨_, htop⟩ c lam ⟨φ, h0, hK, hl⟩
  exact dc_eigen_descend (ρ.comp (locGL F 2 w)) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] V // ∀ g v, f (σ.ρ g v) = ρ (locGL F 2 w g) (f v)} => f.1) (fun f => f.2)
    (K1 w c) _ lam φ h0 hK hl (htop ▸ Submodule.mem_top)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section SlopeTestRemainingChoices
open GlobalTheory.SmGL GlobalTheory.PRep Matrix

private theorem sep_of_irred {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hρ : ρ.IsIrreducible) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0) (v : V) (hv : ∀ g, L (ρ g v) = 0) : v = 0 := by
  let S : Subrepresentation ρ :=
    ⟨{ carrier := {v | ∀ g, L (ρ g v) = 0}
       add_mem' := fun {a b} ha hb g => by simp [ha g, hb g]
       zero_mem' := fun g => by simp
       smul_mem' := fun c a ha g => by simp [ha g] }, fun x a ha g => by
      have := ha (g * x)
      simpa using this⟩
  haveI := hρ
  rcases eq_bot_or_eq_top S with h | h
  · have : v ∈ S.toSubmodule := hv
    rw [h] at this
    exact this
  · exfalso
    apply hL
    ext a
    have : a ∈ S.toSubmodule := by rw [h]; trivial
    simpa using this 1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem diag_eq (a d : kˣ) :
    diagT k (Fin 2) ![a, d] = GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) 0 := by
  ext i j
  rw [val_diagT]
  fin_cases i <;> fin_cases j <;>
    simp [aff, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_div_cancel₀]

private theorem cont_diag : Continuous (diagT k (Fin 2)) :=
  (continuous_leviEmb k (points (Fin 2))).comp (continuous_leviTorus k (Fin 2))

private theorem finiteRing_sq_sub_mul_sq_eq_of_card (σ : SmIrr (GL (Fin 2) k)) (μ₁ μ₂ : kˣ →* ℂˣ) (L : σ.V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (h : ∀ (a d : kˣ) (x : k) v, L (σ.ρ (GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
      ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
    IsSmoothChar μ₁ ∧ IsSmoothChar μ₂ ∧ IsSubquotient σ.ρ (Hi.PS ![μ₁ * absPow k (-1), μ₂]) ∧
      ∀ (z : kˣ) v, σ.ρ (GeneralLinearGroup.scalar (Fin 2) z) v = ((μ₁ z * μ₂ z : ℂˣ) : ℂ) • v := by
  obtain ⟨v₀, hv₀⟩ : ∃ v, L v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hL (LinearMap.ext hc)
  have hst : ∀ a d : kˣ, σ.ρ (diagT k (Fin 2) ![a, d]) v₀ = v₀ → μ₁ a * μ₂ d = 1 := by
    intro a d had
    have := h a d 0 v₀
    rw [← diag_eq, had] at this
    ext
    exact (mul_eq_right₀ hv₀).1 this.symm
  have hopen : IsOpen {g | σ.ρ g v₀ = v₀} := σ.smooth v₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hc : Continuous fun a : kˣ => diagT k (Fin 2) ![a, 1] :=
      cont_diag.comp (continuous_pi fun i => by fin_cases i; exacts [continuous_id, continuous_const])
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hopen.preimage hc).mem_nhds ?_) ?_)
    · have : (![1, 1] : Fin 2 → kˣ) = 1 := by funext i; fin_cases i <;> rfl
      simp [this]
    · intro a ha
      simpa using hst a 1 ha
  · have hc : Continuous fun a : kˣ => diagT k (Fin 2) ![1, a] :=
      cont_diag.comp (continuous_pi fun i => by fin_cases i; exacts [continuous_const, continuous_id])
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hopen.preimage hc).mem_nhds ?_) ?_)
    · have : (![1, 1] : Fin 2 → kˣ) = 1 := by funext i; fin_cases i <;> rfl
      simp [this]
    · intro a ha
      simpa using hst 1 a ha
  · let τ : Representation ℂ (Levi k fun _ : Fin 2 => Unit) ℂ :=
      (ofChar (torusChar fun i => ![μ₁ * absPow k (-1), μ₂] i * absPow k ((((2 : ℕ) : ℂ) - 1) / 2))).comp
        (leviTorus k (Fin 2)).symm.toMonoidHom
    have law : ∀ (p : parab k (points (Fin 2))) (u : σ.V), L (σ.ρ p u) =
        (deltaHalf k (fun _ : Fin 2 => Unit) (leviProj k (points (Fin 2)) p) : ℂ) •
          τ (leviProj k (points (Fin 2)) p) (L u) := by
      intro p u
      set t : Fin 2 → kˣ := (leviTorus k (Fin 2)).symm (leviProj k (points (Fin 2)) p) with ht
      have ht1 : ∀ i, GeneralLinearGroup.det (leviProj k (points (Fin 2)) p i) = t i := fun i => rfl
      have ht2 : ∀ i, (t i : k) = ((p : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) i i := by
        intro i
        rw [← ht1]
        simp
      have h10 : ((p : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 :=
        (mem_borel k).1 p.2 1 0 (by decide)
      have hp : (p : GL (Fin 2) k) = GeneralLinearGroup.scalar (Fin 2) (t 1) *
          aff (t 0 / t 1) (((p : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 1 / t 1) := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [aff, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_div_cancel₀, ← ht2, h10]
      rw [hp, h]
      show _ = _ • ofChar _ t (L u)
      rw [ofChar_apply, deltaHalf_apply, torusChar_apply, Fin.prod_univ_two, Fin.prod_univ_two, ht1, ht1,
        modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp), smul_eq_mul, ← mul_assoc, ← Units.val_mul]
      congr 2
      have e1 : absPow k (-1) = (absPow k (1 / 2))⁻¹ * (absPow k (1 / 2))⁻¹ := by
        rw [← absPow_neg, ← absPow_add]; norm_num
      have e2 : ((((2 : ℕ) : ℤ) - 1 - 2 * ((0 : Fin 2) : ℕ) : ℤ) : ℂ) / 2 = 1 / 2 := by norm_num
      have e3 : ((((2 : ℕ) : ℤ) - 1 - 2 * ((1 : Fin 2) : ℕ) : ℤ) : ℂ) / 2 = -(1 / 2) := by norm_num
      have e4 : (((2 : ℕ) : ℂ) - 1) / 2 = 1 / 2 := by norm_num
      rw [e2, e3, e4, absPow_neg, e1]
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      generalize absPow k (1 / 2) (t 0) = x
      generalize absPow k (1 / 2) (t 1) = y
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    let f : σ.V →ₗ[ℂ] IndSp (points (Fin 2)) τ :=
      { toFun := fun v => ⟨⟨fun g => L (σ.ρ g v), fun p g => by
            refine Eq.trans ?_ (law p (σ.ρ g v))
            show L (σ.ρ (p * g) v) = _
            rw [map_mul, Module.End.mul_apply]⟩,
          mem_smoothPart_of_nhds (Filter.mem_of_superset
            (IsOpen.mem_nhds (σ.smooth v) (by simp)) fun g hg => by
              have hg' : σ.ρ g v = v := hg
              apply Subtype.ext
              funext x
              show L (σ.ρ (x * g) v) = L (σ.ρ x v)
              rw [map_mul, Module.End.mul_apply, hg'])⟩
        map_add' := fun c d => by ext g; simp
        map_smul' := fun c d => by ext g; simp }
    refine IsSubquotient.of_injective (ρ := parInd (points (Fin 2)) τ) ⟨f, fun g => ?_⟩ fun c d hcd => ?_
    · refine LinearMap.ext fun c => Subtype.ext (Subtype.ext (funext fun x => ?_))
      show L (σ.ρ x (σ.ρ g c)) = L (σ.ρ (x * g) c)
      rw [map_mul, Module.End.mul_apply]
    · refine sub_eq_zero.1 (sep_of_irred σ.ρ σ.irred L hL _ fun g => ?_)
      have : L (σ.ρ g c) = L (σ.ρ g d) := congrFun (congrArg (fun φ => φ.1.1) hcd) g
      rw [map_sub, map_sub, this, sub_self]
  · intro z v
    refine sub_eq_zero.1 (sep_of_irred σ.ρ σ.irred L hL _ fun g => ?_)
    have hc : g * GeneralLinearGroup.scalar (Fin 2) z =
        GeneralLinearGroup.scalar (Fin 2) z * aff (z / z) 0 * g := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [aff, GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm]
    rw [map_sub, map_sub, ← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, h]
    simp

end SlopeTestRemainingChoices

theorem UpperTheory.isSubquotient_principalSeries_of_borel_functional :
    ∀ (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin 2) (w.adicCompletion F))) (μ₁ μ₂ : (w.adicCompletion F)ˣ →* ℂˣ) (L : σ.V →ₗ[ℂ] ℂ), L ≠ 0 → (∀ (a d : (w.adicCompletion F)ˣ) (x : w.adicCompletion F) v, L (σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) = ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) → GlobalTheory.SmGL.IsSmoothChar μ₁ ∧ GlobalTheory.SmGL.IsSmoothChar μ₂ ∧ GlobalTheory.SmGL.IsSubquotient σ.ρ (Hi.PS ![μ₁ * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1), μ₂]) ∧ ∀ (z : (w.adicCompletion F)ˣ) v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) v = ((μ₁ z * μ₂ z : ℂˣ) : ℂ) • v := by
  intro F _ _ w σ μ₁ μ₂ L hL h
  exact finiteRing_sq_sub_mul_sq_eq_of_card σ μ₁ μ₂ L hL h
end
