module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle004
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle003
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Eb.residue_dual {K : Type} [Field K] (x : DualNumber K) :
    residue (DualNumber K) x = ((residue (DualNumber K)).comp (algebraMap K (DualNumber K))) (dF K x) := by
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have e : x - algebraMap K (DualNumber K) (dF K x) = TrivSqZeroExt.inr x.snd := by
    ext <;> simp [dF, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst]
  simp

private theorem UpperTheory.V.Ws.Eb.charpoly_lift {A K H : Type} [CommRing A] [CommRing K] [Group H] {n : ℕ} (f : A →+* K)
    (r : H →* GL (Fin n) A) (κ : Fin n → H →* Aˣ) (h : W.HasFlag (W.pushRep f r) fun i => W.pushCh f (κ i))
    (z : MonoidAlgebra A H) :
    (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) z).charpoly.map f =
      ∏ i, (X - C (f (MonoidAlgebra.lift A A H ((Units.coeHom _).comp (κ i)) z))) := by
  unfold W.HasFlag W.pushRep W.pushCh at h
  obtain ⟨g, hg⟩ := h
  have key : ∀ y : MonoidAlgebra A H,
      (∀ i j : Fin n, j < i → ((g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) y) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i j = 0) ∧
      ∀ i, ((g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) y) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i = f (MonoidAlgebra.lift A A H ((Units.coeHom _).comp (κ i)) y) := by
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simp only [map_add (f := _), mul_add, add_mul, Matrix.add_apply]
      exact ⟨fun i j hij => by rw [hx.1 i j hij, hy.1 i j hij, add_zero], fun i => by rw [hx.2, hy.2]⟩
    | single s a =>
      have e : (g : Matrix (Fin n) (Fin n) K) * f.mapMatrix (MonoidAlgebra.lift A (Matrix (Fin n) (Fin n) A) H ((Units.coeHom _).comp r) (MonoidAlgebra.single s a)) * ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = f a • ((g * ((GeneralLinearGroup.map f).comp r) s * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [MonoidAlgebra.lift_single]
        have e' : f.mapMatrix (a • ((r s : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) = f a • ((GeneralLinearGroup.map f (r s) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          ext i j
          simp [GeneralLinearGroup.map]
        simp only [MonoidHom.comp_apply, Units.coeHom_apply, e', Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]
      rw [e]
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · rw [Matrix.smul_apply, (hg s).1 i j hij, smul_zero]
      · rw [Matrix.smul_apply, (hg s).2 i]
        simp [MonoidAlgebra.lift_single]
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_units_conj g, ← Matrix.coe_units_inv]
  simp only [← RingHom.mapMatrix_apply]
  rw [Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (key z).1 i j hij)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(key z).2 i]

theorem UpperTheory.V.Ws.Eb.flagDual :
    ∀ {K H : Type} [Field K] [Infinite K] [Group H] {n : ℕ} (ρ' : H →* GL (Fin n) (DualNumber K)) (κ : Fin n → H →* (DualNumber K)ˣ), (Function.Injective fun i => W.pushCh (dF K) (κ i)) →
        W.HasFlag (W.pushRep (dF K) ρ') (fun i => W.pushCh (dF K) (κ i)) → (∀ g : Fin n → H, (List.ofFn fun i => W.mat ρ' (g i) - algebraMap (DualNumber K) _ (κ i (g i) : DualNumber K)).prod = 0) → W.HasFlag ρ' κ := by
  intro K H _ _ _ n ρ' κ hinj hflag hprod
  set φ : K →+* ResidueField (DualNumber K) := (residue (DualNumber K)).comp (algebraMap K (DualNumber K)) with hφ
  have hres : residue (DualNumber K) = φ.comp (dF K) := RingHom.ext fun x => UpperTheory.V.Ws.Eb.residue_dual x
  have hcard : (n : Cardinal) ≤ Cardinal.mk (ResidueField (DualNumber K)) := by
    haveI : Infinite (ResidueField (DualNumber K)) := Infinite.of_injective φ φ.injective
    exact (Cardinal.natCast_lt_aleph0 (n := n)).le.trans (Cardinal.infinite_iff.mp inferInstance)
  have hinj' : Function.Injective fun i => ((residue (DualNumber K) : DualNumber K →* ResidueField (DualNumber K))).comp ((Units.coeHom (DualNumber K)).comp (κ i)) := by
    intro i j hij
    apply hinj
    ext s
    have hs := DFunLike.congr_fun hij s
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.coe_ofClass] at hs
    rw [hres, RingHom.comp_apply, RingHom.comp_apply] at hs
    have := φ.injective hs
    simpa [W.pushCh] using this
  have hchar : ∀ z : MonoidAlgebra (DualNumber K) H,
      Polynomial.map (residue (DualNumber K))
          ((MonoidAlgebra.lift (DualNumber K) (Matrix (Fin n) (Fin n) (DualNumber K)) H ((Units.coeHom _).comp ρ')) z).charpoly =
        ∏ i, (X - C ((residue (DualNumber K)) ((MonoidAlgebra.lift (DualNumber K) (DualNumber K) H ((Units.coeHom _).comp (κ i))) z))) := by
    intro z
    rw [hres, ← Polynomial.map_map, UpperTheory.V.Ws.Eb.charpoly_lift (dF K) ρ' κ hflag z, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.comp_apply]
    rfl
  obtain ⟨z, g, -, -, hg⟩ := AlgebraTools.lemma_L ρ' κ hcard hprod hinj' hchar
  unfold W.HasFlag
  exact ⟨g, hg⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem res_iff {K : Type} [Field K] (a b : DualNumber K) :
    residue (DualNumber K) a = residue (DualNumber K) b ↔ a.fst = b.fst := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not, TrivSqZeroExt.fst_sub, sub_eq_zero]

private theorem flag_const {K H : Type} [Field K] [Infinite K] [Group H] {n : ℕ} (ρ : H →* GL (Fin n) K)
    (ρ' : H →* GL (Fin n) (DualNumber K)) (Q : GL (Fin n) (DualNumber K))
    (hQ : ∀ g, ρ' g = Q * W.pushRep (algebraMap _ (DualNumber K)) ρ g * Q⁻¹) (ψ : Fin n → H →* (DualNumber K)ˣ)
    (hinj : Function.Injective fun i => W.pushCh (dF K) (ψ i)) (h0 : W.HasFlag ρ fun i => W.pushCh (dF K) (ψ i))
    (h1 : W.HasFlag ρ' ψ) (i : Fin n) (s : H) : (ψ i s : DualNumber K).snd = 0 := by
  obtain ⟨g, hg⟩ := h0
  obtain ⟨g', hg'⟩ := h1
  let ι : K →+* DualNumber K := algebraMap _ _
  have hinf : Infinite (ResidueField (DualNumber K)) :=
    Infinite.of_injective _ ((residue (DualNumber K)).comp ι).injective
  have e : ∀ s, GeneralLinearGroup.map ι g * Q⁻¹ * ρ' s * (GeneralLinearGroup.map ι g * Q⁻¹)⁻¹ =
      GeneralLinearGroup.map ι (g * ρ s * g⁻¹) := fun s => by
    rw [hQ, map_mul, map_mul, map_inv]
    show _ * (_ * GeneralLinearGroup.map ι (ρ s) * _) * _ = _
    group
  have := (AlgebraTools.flag_chars_unique ρ' ψ (fun i => W.pushCh ι (W.pushCh (dF K) (ψ i))) g'
    (GeneralLinearGroup.map ι g * Q⁻¹) ((Cardinal.natCast_lt_aleph0).le.trans (Cardinal.aleph0_le_mk _))
    (fun a b hab => hinj (MonoidHom.ext fun t => Units.ext ((res_iff _ _).1 (DFunLike.congr_fun hab t))))
    (fun a t => (res_iff _ _).2 rfl) hg' (fun t => by
      rw [e]
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · show ι ((g * ρ t * g⁻¹ : GL (Fin n) K) a b) = 0
        rw [(hg t).1 a b hab, map_zero]
      · show ι ((g * ρ t * g⁻¹ : GL (Fin n) K) a a) = _
        rw [(hg t).2 a]
        rfl)).1
  rw [congrFun this i]
  rfl

theorem UpperTheory.V.Ws.Eb.constOf :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x' : B.B →ₐ[c.O] DualNumber (PadicAlgCl l)) (ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)) (ρ' : F.G₀ →* GL (Fin n) (DualNumber (PadicAlgCl l))) (Q : GL (Fin n) (DualNumber (PadicAlgCl l))), B.u.D.map (x' : B.B →+* DualNumber (PadicAlgCl l)) = W.GDet.ofRep (W.mat ρ') → (∀ g, ρ' g = Q * W.pushRep (algebraMap _ (DualNumber (PadicAlgCl l))) ρ g * Q⁻¹) →
        (∀ v, Function.Injective fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i)) → (∀ v, W.HasFlag (ρ.comp (F.φ v)) fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i)) →
        (∀ v, W.HasFlag (ρ'.comp (F.φ v)) fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i)) → ∀ b, (x' b).snd = 0 := by
  intro l hl F c n r B x' ρ ρ' Q hD hQ hinj h0 h1
  obtain ⟨-, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  refine derZero c B.B x' _ (CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B) ?_
  rintro a (⟨i, g, -, -, rfl⟩ | ⟨v, i, g, rfl⟩)
  · have e1 := (AlgebraTools.Det.mapApi B.u.D (x' : B.B →+* DualNumber (PadicAlgCl l))).2.2.1 i g
    have e2 : W.GDet.ofRep (W.mat ρ') =
        (W.GDet.ofRep (W.mat ρ)).map (algebraMap _ (DualNumber (PadicAlgCl l))) := by
      rw [(AlgebraTools.Det.repApi _).2.2.2.2.2.1]
      refine (AlgebraTools.Det.repApi _).2.2.2.2.2.2.2 _ Q⁻¹ fun y => ?_
      have : Q⁻¹ * ρ' y = W.pushRep (algebraMap _ (DualNumber (PadicAlgCl l))) ρ y * Q⁻¹ := by
        rw [hQ]; group
      exact congrArg Units.val this
    rw [hD, e2, (AlgebraTools.Det.mapApi _ _).2.2.1] at e1
    exact (congrArg TrivSqZeroExt.snd e1).symm
  · exact flag_const (ρ.comp (F.φ v)) (ρ'.comp (F.φ v)) Q (fun g => hQ _)
      (fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i)) (hinj v) (h0 v) (h1 v) i g
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem lr_cont {Γ R E : Type} [TopologicalSpace Γ] [CommRing R] [NormedAddCommGroup E] (I : Ideal R) (f : Γ → R)
    (hf : AdicCont I f) (y : R →+ E) (hy : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ ε) :
    Continuous fun g => y (f g) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := hy (ε / 2) (half_pos hε)
  filter_upwards [(hf n).eventually_eq g₀] with g hg
  have h1 := hn _ (Ideal.Quotient.eq.1 hg)
  rw [map_sub] at h1
  rw [dist_eq_norm]
  exact h1.trans_lt (half_lt_self hε)

private theorem lr_cont2 {l : ℕ} [Fact l.Prime] (c : Coef l) {Γ R : Type} [TopologicalSpace Γ] [CommRing R] [Algebra c.O R]
    [IsCO c.O R] (f : Γ → R) (hf : AdicCont (maximalIdeal R) f) (x : R →ₐ[c.O] DualNumber (PadicAlgCl l)) :
    Continuous fun g => x (f g) := by
  obtain ⟨-, a, ha1, ha0, ha⟩ := (coPt c R).1 ((TrivSqZeroExt.fstHom c.O (PadicAlgCl l) (PadicAlgCl l)).comp x)
  have h1 : Continuous fun g => (x (f g)).fst := by
    refine lr_cont _ f hf
      ((TrivSqZeroExt.fstHom c.O (PadicAlgCl l) (PadicAlgCl l)).comp x).toRingHom.toAddMonoidHom fun ε hε => ?_
    obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).eventually (gt_mem_nhds hε)).exists
    exact ⟨k, fun z hz => (ha k z hz).trans hk.le⟩
  have h2 : Continuous fun g => (x (f g)).snd :=
    lr_cont _ f hf ((TrivSqZeroExt.sndHom (PadicAlgCl l) (PadicAlgCl l)).toAddMonoidHom.comp x.toRingHom.toAddMonoidHom)
      ((coPt c R).2 x).2
  exact h1.prodMk h2

theorem UpperTheory.V.Ws.Eb.liftRep :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x' : B.B →ₐ[c.O] DualNumber (PadicAlgCl l)) (ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)), 1 ≤ n → Full ρ → B.u.D.map ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) = W.GDet.ofRep (W.mat ρ) →
        ∃ (ρ' : F.G₀ →* GL (Fin n) (DualNumber (PadicAlgCl l))) (y : F.G₀ → Matrix (Fin n) (Fin n) (PadicAlgCl l)), B.u.D.map (x' : B.B →+* DualNumber (PadicAlgCl l)) = W.GDet.ofRep (W.mat ρ') ∧ W.pushRep (dF _) ρ' = ρ ∧ Full ρ' ∧ Continuous ρ ∧ y ∈ Z1 (Loc.adGL ρ) ∧ IsTan ρ y ρ' := by
  intro l _ F c n r B x' ρ hn hρ hD
  haveI : Module.Finite (PadicAlgCl l) (DualNumber (PadicAlgCl l)) :=
    inferInstanceAs (Module.Finite (PadicAlgCl l) (PadicAlgCl l × PadicAlgCl l))
  haveI : IsArtinianRing (DualNumber (PadicAlgCl l)) := IsArtinianRing.of_finite (PadicAlgCl l) _
  haveI : IsAdicComplete (maximalIdeal (DualNumber (PadicAlgCl l))) (DualNumber (PadicAlgCl l)) := inferInstance
  haveI : IsLocalHom (dF (PadicAlgCl l)) := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  obtain ⟨ρ', h1, h2, h3⟩ := detRep (dF (PadicAlgCl l)) (B.u.D.map (x' : B.B →+* DualNumber (PadicAlgCl l))) ρ hn
    (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩) hρ (((AlgebraTools.Det.mapApi B.u.D _).2.2.2.2.2.2.1 _).trans hD)
  have htr : ∀ g, (W.mat ρ' g).trace = x' (B.u.D.lam 1 (MonoidAlgebra.single g 1)) := fun g => by
    have e1 := (AlgebraTools.Det.mapApi B.u.D (x' : B.B →+* DualNumber (PadicAlgCl l))).2.2.1 1 g
    have e2 := (AlgebraTools.Det.repApi (W.mat ρ')).2.2.1 hn (MonoidAlgebra.single g 1)
    have e3 : W.GDet.repAlg (W.mat ρ') _ (MonoidAlgebra.single g 1) = W.mat ρ' g := by
      refine Matrix.ext fun i j => ?_
      simp [W.GDet.repAlg]
    rw [h1] at e1
    rw [e3] at e2
    exact e2.symm.trans e1
  have hc : Continuous ρ' := (trPlus ρ' h3).2 (by
    simp only [htr]
    exact lr_cont2 c _ (B.u.cont 1) x')
  obtain ⟨h4, y, h5, h6⟩ := tanOf ρ' hc
  rw [h2] at h4 h5 h6
  exact ⟨ρ', y, h1, h2, h3, h4, h5, h6⟩
end
