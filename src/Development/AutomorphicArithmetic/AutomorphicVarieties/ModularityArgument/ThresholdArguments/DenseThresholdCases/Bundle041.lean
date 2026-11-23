module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle028
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.SphScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle006
import GroundTheory.LocalFields.UnramifiedHensel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle020
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle033
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdTransfer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.OverOf4
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle065
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle006
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.LocTrans

@[expose] public section

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem symOf_act {T W κ : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (t : κ → T) (c : κ → ℂ) :
    ∃ act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W, ∀ a, act (MvPolynomial.X a) = c a • (θ (t a) : Module.End ℂ W) :=
  ⟨(MonoidAlgebra.lift ℂ (Module.End ℂ W) T ((Units.coeHom _).comp θ)).comp
    (MvPolynomial.aeval fun a => MonoidAlgebra.single (t a) (c a)), fun a => by simp⟩
private theorem symOf_int {R R' W W' κ : Type} [CommRing R] [AddCommGroup W] [Module R W] [CommRing R'] [AddCommGroup W']
    [Module R' W'] (Φ : MvPolynomial κ ℤ →+* Module.End R W) (Φ' : MvPolynomial κ ℤ →+* Module.End R' W') (g : W →+ W')
    (h : ∀ a m, Φ' (MvPolynomial.X a) (g m) = g (Φ (MvPolynomial.X a) m)) (F : MvPolynomial κ ℤ) (m : W) :
    Φ' F (g m) = g (Φ F m) := by
  induction F using MvPolynomial.induction_on generalizing m with
  | C r =>
    rw [eq_intCast (MvPolynomial.C : ℤ →+* MvPolynomial κ ℤ), map_intCast, map_intCast, Module.End.intCast_apply,
      Module.End.intCast_apply, map_zsmul]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), hp, hq]
  | mul_X p a hp => rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h, hp]
private theorem symOf_sym {R W W' : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module ℂ W'] {q n : ℕ}
    (c : R →+* ℂ) (act : PU R q n →ₐ[R] Module.End R W) (act' : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Module.End ℂ W') (g : W →+ W')
    (hg : ∀ r m, g (r • m) = c r • g m) (j : Fin q) (N : ℕ) (E : Fin n → Module.End R W) (E' : Fin n → Module.End ℂ W')
    (h : ∀ i, act (MvPolynomial.X (j, i)) = (N : R) ^ (i : ℕ) • E i)
    (h' : ∀ i, act' (MvPolynomial.X i) = (N : ℂ) ^ (i : ℕ) • E' i) (hE : ∀ i m, E' i (g m) = g (E i m)) (k : ℕ) (m : W) :
    act' (MvPolynomial.esymm (Fin n) ℂ k) (g m) = g (act (emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ k)) m) := by
  have h1 := symOf_int (act.toRingHom.comp (emb ℤ R j)) (act'.toRingHom.comp (MvPolynomial.map (Int.castRingHom ℂ))) g
    (fun a m => by
      have e : emb ℤ R j (MvPolynomial.X a) = MvPolynomial.X (j, a) := by simp [emb]
      change act' (MvPolynomial.map _ (MvPolynomial.X a)) _ = g (act (emb ℤ R j (MvPolynomial.X a)) m)
      rw [MvPolynomial.map_X, e, h, h', LinearMap.smul_apply, LinearMap.smul_apply, hg, hE, map_pow, map_natCast])
    (MvPolynomial.esymm (Fin n) ℤ k) m
  rw [RingHom.comp_apply, MvPolynomial.map_esymm] at h1
  exact h1
private theorem symOf_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem symOf_vieta {n : ℕ} {A K K' G : Type} [CommRing A] [CommRing K] [CommRing K'] [Group G] (D : GDet n A G)
    (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (hD : D.map f = GDet.ofRep ρ) (e : K →+* K') (g : G) (α : Fin n → K')
    (h : ((ρ g).map e).charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))) (k : ℕ) (hk : k ≤ n) :
    MvPolynomial.eval α (MvPolynomial.esymm (Fin n) K' k) = e (f (D.lam k (MonoidAlgebra.single g 1))) := by
  have h1 := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 k
  rw [MonoidAlgebra.mapRingHom_single, map_one, hD, GDet.lam, symOf_chi] at h1
  have h2 := Multiset.prod_X_sub_C_coeff (Finset.univ.val.map α) (k := n - k) (by simp)
  rw [Multiset.map_map, Multiset.card_map, Finset.card_val, Finset.card_fin, Nat.sub_sub_self hk] at h2
  rw [← h1, map_mul, ← Polynomial.coeff_map, ← Matrix.charpoly_map, h, ← MvPolynomial.coe_aeval_eq_eval, RingHom.coe_coe,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, Finset.prod_eq_multiset_prod]
  erw [h2]
  rw [map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
  simp
private theorem symOf_sph {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {Y : Type} [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GL (Fin n) k) Y)
    (σ : SmIrr (GL (Fin n) k)) (hs : IsoSum π ⊤ σ) (y : Y) (hy : y ∈ fixd π (KO k (Fin n))) (h0 : y ≠ 0) :
    IsSpherical σ.ρ := by
  have h1 := isoFix k n Y π σ _ GlobalTheory.SplitFlip.isCompact_KO hs y hy
  unfold IsSpherical IsSphericalFor
  intro h2
  have h3 : ∀ v ∈ fixd σ.ρ (KO k (Fin n)), v = 0 := fun v hv => by
    have h4 : v ∈ GlobalTheory.PRep.fixed σ.ρ (KO k (Fin n)) := fun u => by simpa using hv u u.2
    rw [h2] at h4
    exact (Submodule.mem_bot ℂ).1 h4
  refine h0 ((Submodule.mem_bot ℂ).1 ((iSup_le fun f => ?_ : _ ≤ (⊥ : Submodule ℂ Y)) h1))
  rintro _ ⟨v, hv, rfl⟩
  rw [h3 v hv, map_zero]
  exact zero_mem _
theorem UpperTheory.V.Z.Win.T2.symOf_alt :
    _root_.UpperTheory.V.Pa.Lev.symOf_s_ty := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ _ hx _ T ph ta ⟨ι, hsep, hrel⟩ j k hk m hm
  refine Subtype.ext (sub_eq_zero.1 (hsep _ fun y => ?_))
  obtain ⟨Θ, hΘ⟩ := thetaQ L n q w ℂ y.Y y.π (fun _ => ⊤) fun j =>
    (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[(w j).adicCompletion L])).ne').isUnit
  obtain ⟨act, hact⟩ := symOf_act (Θ j) (fun i : Fin n => Pi.mulSingle i (x j)) fun i => (qj w j : ℂ) ^ (i : ℕ)
  let g : fixd A.ρ (UC n w fun _ => ⊤) →+ fixd y.π (UC n w fun _ => ⊤) :=
    { toFun := fun m => ⟨y.sp m, fun u hu => by rw [← y.sp_act, m.2 u hu]⟩
      map_zero' := Subtype.ext (map_zero y.sp)
      map_add' := fun a a' => Subtype.ext (map_add y.sp _ _) }
  have hg : ∀ (r : A.R) m, g (r • m) = ι (y.θ r) • g m := fun r m => Subtype.ext (y.sp_smul r m)
  have hΘg : ∀ t m, (Θ j t).val (g m) = g ((T.Θw j t).val m) := fun t m =>
    Subtype.ext (thetaMap L n q w A.R A.P ℂ y.Y A.ρ y.π _ T.Θw Θ T.hw hΘ y.sp y.sp_act j t m (g m) rfl)
  have h1 := symOf_sym (ι.toRingHom.comp y.θ) T.actw act g hg j (qj w j)
    (fun i => (T.Θw j (Pi.mulSingle i (x j))).val) (fun i => (Θ j (Pi.mulSingle i (x j))).val) (T.actw_u j) hact
    (fun i => hΘg _) k m
  have hfix : ((g m : fixd y.π (UC n w fun _ => ⊤)) : y.Y) ∈ fixd (y.π.comp (atJ n w j)) (KO _ (Fin n)) := fun u hu => by
    change y.π (atJ n w j u) (y.sp m) = y.sp m
    rw [← y.sp_act, hm (atJ n w j u) fun j' _ => ?_]
    by_cases e : j' = j
    · subst e
      simpa [atJ] using hu
    · simp [atJ, Pi.mulSingle_eq_of_ne e]
  by_cases hz : g m = 0
  · have h2 : g (T.actw (emb ℤ A.R j (MvPolynomial.esymm (Fin n) ℤ k)) m) =
        g (A.p.D.lam k (MonoidAlgebra.single (ph j) 1) • m) := by
      rw [← h1, hg, hz, map_zero, smul_zero]
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val h2
  have hsph : IsSpherical (y.σ j).ρ :=
    symOf_sph _ (y.σ j) (y.iso j) _ hfix fun e => hz (Subtype.ext e)
  have h0 := sphScalar hP.gl hP.bz L n q w y.Y y.π Θ hΘ j (y.σ j) (y.iso j) (x j) (hx j) act hact
    (MvPolynomial.esymm (Fin n) ℂ k) (ι (y.θ (A.p.D.lam k (MonoidAlgebra.single (ph j) 1))))
    (MvPolynomial.esymm_isSymmetric _ _ _)
    (fun θ hθ χ hχ => symOf_vieta A.p.D y.θ (mat y.rep) y.det ι.toRingHom (ph j) _
      (((_root_.UpperTheory.V.Z.Win.relT' (hrel y j)) ⊤ le_top θ hθ χ hχ _ fun _ => rfl).1 (Or.inl hsph)) k hk) (g m) hfix
  have h2 := h1.symm.trans (h0.trans (hg _ m).symm)
  rw [map_sub, sub_eq_zero]
  exact congrArg Subtype.val h2
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem exists_place_above_prime_pow (K : Type) [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  haveI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K) (Ideal.span {(l : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (RingHom.injective_int _)]; exact bot_le)
  have hm : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hl.out.ne_zero (by exact_mod_cast hm)
private theorem trace_map_ring_hom_pow {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (y : MonoidAlgebra A G) : (D.map f).tr (MonoidAlgebra.mapRingHom G f y) = f (D.tr y) :=
  ((UpperTheory.V.CA.d_gmap D).2.2.1 f y).2 1
private theorem trace_map_comp_pow {n : ℕ} {A B C G : Type} [CommRing A] [CommRing B] [CommRing C] [Group G] (D : GDet n A G)
    (f : A →+* B) (g : B →+* C) (k : A →+* C) (hk : g.comp f = k) (y : MonoidAlgebra B G) :
    g ((D.map f).tr y) = (D.map k).tr (MonoidAlgebra.mapRingHom G g y) := by
  rw [← trace_map_ring_hom_pow, (UpperTheory.V.CA.d_gmap D).2.1, hk]
private theorem charpoly_of_representation_pow {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K)
    (y : MonoidAlgebra K G) : (GDet.ofRep ρ).chi y = (GDet.repAlg ρ K y).charpoly := by
  change (GDet.repAlg ρ (Polynomial K) _).det = Matrix.det _
  congr 1
  have h : GDet.repAlg ρ (Polynomial K) (MonoidAlgebra.mapRingHom G Polynomial.C y) =
      (Polynomial.C : K →+* Polynomial K).mapMatrix (GDet.repAlg ρ K y) := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => ext i j; simp [GDet.repAlg]
  rw [map_sub, h, Matrix.charmatrix]
  congr 1
  exact (GDet.repAlg ρ (Polynomial K)).commutes Polynomial.X
private theorem trace_eq_zero_of_rep_eq_zero_pow {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K)
    (y₀ y : MonoidAlgebra K G) (h₀ : (GDet.ofRep ρ).tr y₀ = 0) (h : GDet.repAlg ρ K y = 0) : (GDet.ofRep ρ).tr y = 0 := by
  rcases n with _ | n
  · rw [← h₀, GDet.tr, GDet.tr, GDet.lam, GDet.lam, charpoly_of_representation_pow, charpoly_of_representation_pow, Subsingleton.elim (GDet.repAlg ρ K y) (GDet.repAlg ρ K y₀)]
  · nontriviality K
    rw [GDet.tr, GDet.lam, charpoly_of_representation_pow, h, Matrix.charpoly_zero, Polynomial.coeff_X_pow]
    simp
private theorem map_ring_hom_second_relation_pow {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (E : ℕ) (ph ta : G)
    (u : Fin n → A) (i : Fin n) (y : A) : MonoidAlgebra.mapRingHom G f (twoPowerModulus E ph ta u i y) =
      twoPowerModulus E ph ta (fun i => f (u i)) i (f y) := by
  simp only [twoPowerModulus, map_mul, map_pow, map_list_prod, List.map_ofFn, Function.comp_def, map_sub,
    apply_ite (MonoidAlgebra.mapRingHom G f), MonoidAlgebra.mapRingHom_single, map_one]
private theorem rep_single_eq_smul_pow {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K) (g : G) (a : K) :
    GDet.repAlg ρ K (MonoidAlgebra.single g a) = a • ρ g := by
  ext i j; simp [GDet.repAlg]
private theorem rep_second_relation_pow_eq_zero {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K) (E : ℕ) (ph ta : G)
    (α : Fin n → K) (i : Fin n) (c : K)
    (h : (List.ofFn fun i' => if i' = i then 1 else ρ ph - α i' • (1 : Matrix (Fin n) (Fin n) K)).prod ^ (E + 1) *
      (ρ ta - c • (1 : Matrix (Fin n) (Fin n) K)) = 0) :
    GDet.repAlg ρ K (twoPowerModulus E ph ta α i (c - 1)) = 0 := by
  rw [twoPowerModulus, map_mul, map_pow, map_list_prod, List.map_ofFn]
  refine Eq.trans ?_ h
  congr 1
  · congr 3
    funext k
    by_cases hk : k = i <;> simp [hk, rep_single_eq_smul_pow]
  · simp [rep_single_eq_smul_pow, sub_smul]
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete in
private theorem reduction_of_polynomial_element_pow {n q : ℕ} {R G E : Type} [CommRing R] [Group G] [Ring E] [Algebra R E] (D : GDet n R G)
    (act : PUY R q n →ₐ[R] E) (Nq : Fin q → ℕ) (j : Fin q) (k : ℕ) (z : MonoidAlgebra (MvPolynomial (Fin n ⊕ Fin n) R) G)
    (z' : MonoidAlgebra (PUY R q n) G)
    (hz : MonoidAlgebra.mapRingHom G (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i)) :
      MvPolynomial (Fin n ⊕ Fin n) R →ₐ[R] PUY R q n).toRingHom z = z')
    (h : act (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i))
      ((∏ i : Fin n, ∏ i' ∈ Finset.univ.erase i, ((MvPolynomial.X (.inl i) - MvPolynomial.X (.inl i')) *
        (MvPolynomial.X (.inl i) - (Nq j : MvPolynomial (Fin n ⊕ Fin n) R) * MvPolynomial.X (.inl i')))) ^ k *
        (D.map (MvPolynomial.C : R →+* MvPolynomial (Fin n ⊕ Fin n) R)).tr z)) = 0) :
    act (fEl Nq (uV R) ^ k * (D.map (MvPolynomial.C : R →+* PUY R q n)).tr z') = 0 := by
  have e := trace_map_comp_pow D (MvPolynomial.C : R →+* MvPolynomial (Fin n ⊕ Fin n) R)
    (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i)) :
      MvPolynomial (Fin n ⊕ Fin n) R →ₐ[R] PUY R q n).toRingHom MvPolynomial.C (by ext : 1; simp) z
  rw [hz] at e
  rw [fEl, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_pow, mul_assoc, map_mul, ← e]
  refine mul_eq_zero_of_right _ (Eq.trans ?_ h)
  simp [map_prod]
private theorem trace_vanishing_of_evaluation_pow {n : ℕ} {R K S G : Type} [CommRing R] [CommRing K] [CommRing S] [Group G] (D : GDet n R G) (θ : R →+* K) (ι : K →+* S)
    (ρ : G →* Matrix (Fin n) (Fin n) K) (hD : D.map θ = GDet.ofRep ρ) (z₀ : MonoidAlgebra R G) (h₀ : D.tr z₀ = 0)
    (v : Fin n ⊕ Fin n → S) (z : MonoidAlgebra (MvPolynomial (Fin n ⊕ Fin n) R) G)
    (h : GDet.repAlg (ι.mapMatrix.toMonoidHom.comp ρ) S
      (MonoidAlgebra.mapRingHom G (MvPolynomial.eval₂Hom (ι.comp θ) v) z) = 0) :
    MvPolynomial.eval₂ (ι.comp θ) v ((D.map (MvPolynomial.C : R →+* MvPolynomial (Fin n ⊕ Fin n) R)).tr z) = 0 := by
  have hD' : D.map (ι.comp θ) = GDet.ofRep (ι.mapMatrix.toMonoidHom.comp ρ) := by
    rw [← (UpperTheory.V.CA.d_gmap D).2.1, hD, (UpperTheory.V.CA.d_gmap (GDet.ofRep ρ)).2.2.2]
  rw [← MvPolynomial.coe_eval₂Hom, trace_map_comp_pow D _ _ (ι.comp θ) (by ext : 1; simp), hD']
  refine trace_eq_zero_of_rep_eq_zero_pow _ (MonoidAlgebra.mapRingHom G (ι.comp θ) z₀) _ ?_ h
  rw [← hD', trace_map_ring_hom_pow, h₀, map_zero]
theorem UpperTheory.V.Z.Win.T2.level_relation_two_x :
    _root_.UpperTheory.V.Th.LevelRelationTwoX := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ h1 h2 h3 T ph ta ⟨ι, hsep, hloc⟩ j i
  obtain ⟨v⟩ : Nonempty (globOf r V).frame.Vl := (exists_place_above_prime_pow (Lp L) l).elim fun v hv => ⟨⟨v, hv⟩⟩
  have h₀ := A.p.Ord v (fun _ => 1) 1
  refine reduction_of_polynomial_element_pow A.p.D T.act1 (qj w) j _
    (twoPowerModulus (2 * n.factorial) (ph j) (ta j) (fun i => MvPolynomial.X (.inl i)) i (MvPolynomial.X (.inr i))) _
    ((map_ring_hom_second_relation_pow _ _ _ _ _ _ _).trans (by simp)) ?_
  refine _root_.UpperTheory.V.Th.relOfX_alt hP l L Ω s V0 O n r B J D b V h q w A x δ h1 h2 h3 T ι hsep j _ fun y θ hθ χ hχ S _ _ U hU => ?_
  rw [MvPolynomial.eval₂_mul]
  by_cases hreg : ∀ a a' : Fin n, a ≠ a' → (qj w j : ℂ) ^ (a : ℕ) * (χ (Pi.mulSingle a (x j)) : ℂ) ≠
      (qj w j : ℂ) ^ (a' : ℕ) * (χ (Pi.mulSingle a' (x j)) : ℂ) ∧ (qj w j : ℂ) ^ (a : ℕ) * (χ (Pi.mulSingle a (x j)) : ℂ) ≠
      (qj w j : ℂ) * ((qj w j : ℂ) ^ (a' : ℕ) * (χ (Pi.mulSingle a' (x j)) : ℂ))
  · refine mul_eq_zero_of_right _ ?_
    refine trace_vanishing_of_evaluation_pow A.p.D y.θ ((algebraMap ℂ S).comp ι.toRingHom) (mat y.rep) y.det _ h₀ _ _ ?_
    rw [map_ring_hom_second_relation_pow]
    simp only [MvPolynomial.eval₂Hom_X', Sum.elim_inl, Sum.elim_inr]
    refine rep_second_relation_pow_eq_zero _ _ _ _ _ _ _ ?_
    have h5 := powRel ℂ S (algebraMap ℂ S) n n.factorial (2 * n.factorial) _ _ _ _ U i (by omega) hU
      ((_root_.UpperTheory.V.Z.Win.relT' (hloc y j) _ le_rfl θ hθ χ hχ _ fun _ => rfl).2 hreg i)
    rw [Matrix.map_map, Matrix.map_map] at h5
    exact h5
  · refine mul_eq_zero_of_left ?_ _
    rw [← MvPolynomial.coe_eval₂Hom]
    simp only [map_pow, map_prod, map_mul, map_sub, map_natCast, MvPolynomial.eval₂Hom_X', Sum.elim_inl]
    exact fNil ℂ S (algebraMap ℂ S) n n.factorial (qj w j) _ U hU hreg
end
end

section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness
private theorem irr_of_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (φ : Γ →* kˣ)
    (h : IsIrr (tw r φ)) : IsIrr r := by
  obtain ⟨hne, -, hmin⟩ := h
  refine ⟨hne, fun _ _ _ => Submodule.mem_top, fun U _ hU => hmin U le_top fun s v hv => ?_⟩
  have e : (tw r φ s : Matrix (Fin n) (Fin n) k).mulVec v =
      (φ s : k) • (r s : Matrix (Fin n) (Fin n) k).mulVec v := by
    rw [tw_val, Matrix.smul_mulVec]
  rw [e]
  exact U.smul_mem _ (hU s v hv)
private theorem comp_tw {Γ Δ k : Type} [Group Γ] [Group Δ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (φ : Γ →* kˣ)
    (f : Δ →* Γ) : (tw r φ).comp f = tw (r.comp f) (φ.comp f) := by
  refine MonoidHom.ext fun s => Units.ext ?_
  simp only [MonoidHom.comp_apply, tw_val]
private theorem open_ker {K Ω C : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω]
    [Algebra ℚ K] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω] [Group C] {M : ℕ} (hM : 1 ≤ M) {φ : G ℚ Ω →* C}
    (hφ : KillsMu M φ) :
    IsOpen ((φ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)).ker : Set (G K Ω)) := by
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    classical
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots hM] using hζ
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
    ((hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral (K := K) ζ).mem_nhds ?_) fun s hs => ?_)
  · simp only [Set.mem_iInter]
    exact fun ζ _ => Subgroup.one_mem _
  · simp only [Set.mem_iInter] at hs
    exact hφ _ fun ζ hζ => hs ζ hζ
end UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness
open UpperTheory.V.Z.Kato.WeilSphericalRecords.TwistWitness in
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.twWit_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → _root_.UpperTheory.V.Z.Win.AIsoTwAlt → TwWit := by
  intro P hI l _ Ω _ _ _ ι n W M φ hM hφ hW K _ _ _ _ _ _ hK hirr
  haveI : Algebra.IsAlgebraic ℚ K := inferInstance
  haveI : IsAlgClosure K Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, (IsAlgClosure.isAlgebraic (R := ℚ) (K := Ω)).tower_top K⟩
  rw [comp_tw] at hirr ⊢
  have hW' := hW K hK (irr_of_tw _ _ hirr)
  have hs := (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results P K Ω l ι).1 0 (φ.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω))
    (open_ker hM hφ)
  rw [zpow_zero, one_mul] at hs
  obtain ⟨hc, art, χ, a, h⟩ := hs
  exact (hI P K Ω l ι n _ hW').2 _ ⟨χ, hc, art, a, h⟩
end
end

section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
section SlopeTestRemainingChoices
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
private theorem ps_wt_any {D : Raw Ω c} (h : D.Good) {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) (i : Fin 4)
    {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (h1 : s ∈ D.ψ.ker) (h2 : s ∈ D.om.ker) :
    D.ps i s = chiO ℚ Ω l c.O s ^ D.wts4 i := by
  have hl : l.Prime := Fact.out
  obtain ⟨u, -, hu⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l A _ hl hA (h.pl_over l hl)
  have e : ∀ γ : G ℚ Ω →* c.Oˣ, γ (u⁻¹ * s * u) = γ s := fun γ => by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  have h3 := (facts D h).2.2.2.1 i (u⁻¹ * s * u) ⟨⟨hu s hs, (e _).trans h1⟩, (e _).trans h2⟩
  rwa [e, e] at h3
private theorem map_psi {ι Γ R R' : Type} [Group Γ] [CommRing R] [CommRing R'] (P : PD ι Γ R) (f : R →+* R') (v : ι) (i : Fin 4)
    (s : Γ) : (P.map f).ψ v i s = f (P.ψ v i s) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [PD.ψ, PD.map, Matrix.mul_apply, adj_apply, map_sum]
private theorem charpoly_conj {H K K' : Type} [Group H] [Field K] [Field K'] (f : K →+* K') {r r' : H →* M4 K}
    (h : IsConj4 r r') (g : H) : (mapRep f r g).charpoly = (mapRep f r' g).charpoly := by
  obtain ⟨u, hu⟩ := h
  show ((r g).map f).charpoly = ((r' g).map f).charpoly
  rw [Matrix.charpoly_map, Matrix.charpoly_map, hu, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
end SlopeTestRemainingChoices
theorem UpperTheory.V.Ws.pureW_of_proModular_of_isZero :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (ι : PadicAlgCl l ≃+* ℂ) (𝔞 : Amb l) (e : 𝔞.K ≃+* PadicAlgCl l), 𝔞.IsZero e → ∀ r, _root_.UpperTheory.V.Ws.ProModAlt D ι 𝔞 r → PureW ι (mapRep ((e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK) r) := by
  intro Ω _ _ _ l _ c D hD ι 𝔞 e he r hr
  obtain ⟨T, c', h, X, J, y, r₁, -, -, hPM, hy, -, hJ, hconj, -, hres, hin⟩ := hr
  let f : 𝔞.V →+* PadicAlgCl l := (e : 𝔞.K →+* PadicAlgCl l).comp 𝔞.toK
  let y' : X.A →ₐ[c'.O] PadicAlgCl l :=
    { f.comp y with
      commutes' := fun x => by
        have h1 : y (algebraMap c'.O X.A x) = 𝔞.a c' x := DFunLike.congr_fun hy x
        exact (congrArg f h1).trans (he.1 c' x) }
  have hy' : ∀ x, y' x = f (y x) := fun _ => rfl
  have hw : T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y' : X.A →+* PadicAlgCl l)) := mkWts4 <| by
    have hc : Continuous (resQ T.F) := UpperTheory.V.Af.continuous_restrictScalarsHom ℚ T.F Ω
    refine ⟨(D.ψ.ker ⊓ D.om.ker).comap (resQ T.F),
      (hD.psi_open.inter (facts D hD).2.2.2.2.2.2.2.2.2.2.2.2.1).preimage hc, fun v i s hs => ?_⟩
    have h1 : resQ T.F s ∈ Ine (F := ℚ) (T.pl v) := hs.2
    have h2 := ps_wt_any hD (T.ovl v) i h1 hs.1.1 hs.1.2
    have h3 : f (y (X.P.ψ v i s)) = ((D.ps i (resQ T.F s) : c.O) : PadicAlgCl l) :=
      (congrArg f (hin v i s hs.2)).trans (he.1 c _)
    have h4 : (GlobalTheory.GalOfCusp.cycBar T.F Ω l s : PadicAlgCl l) =
      ((chiO ℚ Ω l c.O (resQ T.F s) : c.O) : PadicAlgCl l) := rfl
    refine (congrArg (· ^ 2) ((map_psi X.P _ v i s).trans h3)).trans ?_
    rw [h2]
    have h5 : (2 * (D.wts4 i : ℤ)) = ((D.wts4 i * 2 : ℕ) : ℤ) := by push_cast; ring
    simp only [h5, zpow_natCast, Units.val_pow_eq_pow_val, h4, SubmonoidClass.coe_pow, pow_mul]
  have hp := hPM.pur y' (fun b hb => by rw [hy', hJ b hb, map_zero]) hw (mapRep f r₁) (by
    ext g i j
    exact congrArg f (congrFun (congrFun (DFunLike.congr_fun hres g) i) j))
  obtain ⟨H, M, hH, hM, hp⟩ := _root_.UpperTheory.GalN.V.pureW' hp
  refine ⟨H, M, hH, hM, fun p h1 h2 A hA n σ hn hσ hF => ?_⟩
  have h3 : (mapRep f r σ).charpoly = (mapRep f r₁ σ).charpoly :=
    charpoly_conj (e : 𝔞.K →+* PadicAlgCl l) hconj σ
  rw [h3]
  exact hp p h1 h2 A hA n σ hn hσ hF
end
end

section




section
open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth UpperTheory.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
namespace UpperTheory.V.Cu.RankFourTensorSourceAtPrime
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
private theorem toB_chi (c : Coef l) (g : _root_.Formalism.ConjugateSelfDual.G ℚ Ω) : toB (chiO ℚ Ω l c.O) g = cycBar ℚ Ω l g := by
  ext
  rfl
private theorem cont_emb (E : Type) [Field E] [NumberField E] [Algebra E Ω] : Continuous (galEmb ℚ E Ω) := by
  haveI : FaithfulSMul E Ω := (faithfulSMul_iff_algebraMap_injective E Ω).2 (algebraMap E Ω).injective
  haveI : Module.IsTorsionFree E Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  exact (galEmbTop ℚ E Ω).1.continuous
private theorem cont_res (F : IntermediateField ℚ Ω) [NumberField F] : Continuous (resQ F) := cont_emb F
private theorem cont_delta (d : UpperTheory.V.Cu.Dat Ω l) : Continuous (toB d.δ) := by
  have h : Continuous fun g => ((toB d.δ g : (Qbar l)ˣ) : Qbar l) := ((UpperTheory.integrality_of_norm_coefficients l).2 d.c _ _).1 d.tw.cont
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [Units.val_inv_eq_inv_val]
  exact h.inv₀ fun g => (toB d.δ g).ne_zero
end UpperTheory.V.Cu.RankFourTensorSourceAtPrime
open UpperTheory.V.Cu.RankFourTensorSourceAtPrime in
theorem UpperTheory.V.Cu.tower_is_initial_of_ok :
    UpperTheory.V.Cu.AlNe → UpperTheory.V.Cu.WtsOf4 → UpperTheory.V.Cu.IrrOf4 → UpperTheory.V.Cu.AutOf4 → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
      (d : UpperTheory.V.Cu.Dat Ω l) (T : Tower d.D), d.T₀.Le T → T.Ok → OffW d.ι d.K' d.ρ (UpperTheory.V.Cu.tenB d.ρ₁ d.τ) →
      T.IsSeedAlt d.ι ((d.Q T).map (algebraMap d.c₁.O (PadicAlgCl l))) := by
  intro hne hW hI hA Ω _ _ _ l _ d T hT hok hrw
  have hi := hI Ω l d T hT hok
  obtain ⟨π, h1, h2⟩ := hA Ω l d T hT hok hi
  obtain ⟨U, j, hU, hj⟩ := d.tw.wt
  have hm := d.tau.pos
  have hk := d.big
  let φ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* (Qbar l)ˣ := (toB d.δ)⁻¹ ^ 2 * cycBar ℚ Ω l ^ j
  have hle : U ≤ φ.ker := fun g hg => by
    have := congrArg (Units.map (algebraMap d.c.O (PadicAlgCl l)).toMonoidHom) (hj _ hg)
    rw [map_pow, map_zpow] at this
    have e : toB d.δ g ^ 2 = cycBar ℚ Ω l g ^ j := this.trans (congrArg (· ^ j) (toB_chi d.c g))
    show (toB d.δ g)⁻¹ ^ 2 * cycBar ℚ Ω l g ^ j = 1
    rw [← e, inv_pow, inv_mul_cancel]
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI : Finite (_root_.Formalism.ConjugateSelfDual.G ℚ Ω ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono hle hU)
  haveI : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨hi, _, ((toB d.δ).comp (resQ T.L))⁻¹, π, -j, φ.ker.index, fun i => ?_,
    hW Ω l d T U j hU hj, ((cont_delta d).comp (cont_res T.L)).inv, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero,
    ⟨(d.k : ℤ) - 1 + d.m, by simp <;> ring⟩, fun A _ s _ => ?_, _root_.UpperTheory.V.Z.Win.Birth.mkReg' h1 (autOf4W hne Ω l d T hT hok hi hrw π h1 h2), h2⟩
  · fin_cases i
    · exact ⟨2 * (d.m : ℤ), by omega, by simp <;> ring⟩
    · exact ⟨(d.k : ℤ) - 1 - 2 * d.m, by omega, by simp <;> ring⟩
    · exact ⟨2 * (d.m : ℤ), by omega, by simp <;> ring⟩
  · have := φ.ker.pow_index_mem (resQ T.L s)
    rw [MonoidHom.mem_ker, map_pow] at this
    rw [neg_neg]
    exact this
end
end
