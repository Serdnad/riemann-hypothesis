module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFacts
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle005
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle006
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle075
public import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Bundle003
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.PhiGalCris
public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.PeriodRingUnits.DieudonneManinBasisModification
import GroundTheory.PAdicHodge.Bundle009
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open TensorProduct

namespace UpperTheory.Ru.crystallineComparison

section Abstract

variable {R F A C T N ι : Type*} [CommRing R] [CommRing F] [Algebra R F] [CommRing A] [Algebra R A]
  [CommRing C] [Algebra F C] [AddCommGroup T] [Module R T] [AddCommGroup N] [Module A N] [Fintype ι]

private theorem torsion_of_vec (t : A) (c : A →+* C) (ht : IsUnit (c t))
    (loc : ∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a) (ker : ∀ a : A, c a = 0 → ∃ r : ℕ, t ^ r * a = 0)
    (hz : ∀ x : R, algebraMap F C (algebraMap R F x) = c (algebraMap R A x))
    (v : ι → T) (a : ι → A) (r : ℕ)
    (h : ∑ k, ((1 : F) ⊗ₜ[R] v k) ⊗ₜ[F] (c (a k) * Ring.inverse (c t) ^ r) = 0) :
    ∃ u : ℕ, t ^ u • ∑ k, (a k ⊗ₜ[R] v k : A ⊗[R] T) = 0 := by
  letI : Algebra A C := c.toAlgebra
  have hsm : ∀ (b : A) (x : C), b • x = c b * x := fun b x => Algebra.smul_def b x
  haveI : IsLocalization (Submonoid.powers t) C :=
    { map_units := by
        rintro ⟨_, n, rfl⟩
        change IsUnit (c (t ^ n))
        rw [map_pow]
        exact ht.pow n
      surj := fun z => by
        obtain ⟨n, b, hb⟩ := loc z
        refine ⟨⟨b, ⟨t ^ n, n, rfl⟩⟩, ?_⟩
        change z * c (t ^ n) = c b
        rw [map_pow, mul_comm, hb]
      exists_of_eq := fun {x y} hxy => by
        have : c (x - y) = 0 := by
          rw [map_sub]
          exact sub_eq_zero.2 hxy
        obtain ⟨n, hn⟩ := ker _ this
        refine ⟨⟨t ^ n, n, rfl⟩, ?_⟩
        change t ^ n * x = t ^ n * y
        rw [mul_sub] at hn
        exact sub_eq_zero.1 hn }
  let P := C ⊗[A] (A ⊗[R] T)
  have hloc : IsLocalizedModule (Submonoid.powers t) (TensorProduct.mk A C (A ⊗[R] T) 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers t) C _).2 (TensorProduct.isBaseChange A (A ⊗[R] T) C)
  let B : F →+ T →+ C →+ P := AddMonoidHom.mk' (fun q => AddMonoidHom.mk' (fun w =>
      AddMonoidHom.mk' (fun x => (q • x) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] w))
        (fun x y => by rw [smul_add, add_tmul]))
      (fun w w' => by ext x; simp [tmul_add]))
      (fun q q' => by ext w x; simp [add_smul, add_tmul])
  have hB : ∀ q w x, B q w x = (q • x) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] w) := fun _ _ _ => rfl
  have hRF : ∀ (s : R) (q : F) (x : C), (s • q) • x = algebraMap R A s • (q • x) := fun s q x => by
    rw [hsm, Algebra.smul_def s q, Algebra.smul_def q x, Algebra.smul_def (algebraMap R F s * q) x, map_mul, hz, mul_assoc]
  let ψ₁ : F ⊗[R] T →+ C →+ P := TensorProduct.liftAddHom B (fun s q w => by
    ext x
    rw [hB, hB, hRF, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact congrArg _ (TensorProduct.smul_tmul s (1 : A) w))
  have hψ₁ : ∀ q w x, ψ₁ (q ⊗ₜ[R] w) x = (q • x) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] w) := fun _ _ _ => rfl
  let ψ : (F ⊗[R] T) ⊗[F] C →+ P := TensorProduct.liftAddHom ψ₁ (fun f m x => by
    induction m with
    | add m m' hm hm' => simp only [smul_add, map_add (f := _), AddMonoidHom.add_apply, hm, hm']
    | tmul q w =>
      rw [TensorProduct.smul_tmul', hψ₁, hψ₁, smul_eq_mul, mul_comm, mul_smul])
  have hψ : ∀ q w x, ψ ((q ⊗ₜ[R] w) ⊗ₜ[F] x) = (q • x) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] w) := fun _ _ _ => rfl
  have h1 : ∑ k, (c (a k) * Ring.inverse (c t) ^ r) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] v k) = 0 := by
    have := congrArg ψ h

    rw [map_sum, map_zero] at this
    simpa only [hψ, one_smul] using this
  have hinv : c t * Ring.inverse (c t) = 1 := Ring.mul_inverse_cancel _ ht
  have h2 : (TensorProduct.mk A C (A ⊗[R] T) 1) (∑ k, (a k ⊗ₜ[R] v k : A ⊗[R] T)) = 0 := by
    have e : (TensorProduct.mk A C (A ⊗[R] T) 1) (∑ k, (a k ⊗ₜ[R] v k : A ⊗[R] T)) =
        t ^ r • ∑ k, (c (a k) * Ring.inverse (c t) ^ r) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] v k) := by

      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have e1 : t ^ r • (c (a k) * Ring.inverse (c t) ^ r) = a k • (1 : C) := by
        rw [hsm, hsm, map_pow, mul_one, mul_left_comm, ← mul_pow, hinv, one_pow, mul_one]
      have e2 : (a k ⊗ₜ[R] v k : A ⊗[R] T) = a k • ((1 : A) ⊗ₜ[R] v k) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [TensorProduct.smul_tmul', e1, TensorProduct.mk_apply, e2, TensorProduct.smul_tmul]
    rw [e, h1, smul_zero]
  obtain ⟨⟨_, u, rfl⟩, hu⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers t) _).1 h2
  exact ⟨u, hu⟩

private theorem apply_tensor (h : T →+ N) (hh : ∀ (s : R) (w : T), h (s • w) = algebraMap R A s • h w)
    (v : ι → T) (a : ι → A) (s : A) (hs : s • ∑ k, (a k ⊗ₜ[R] v k : A ⊗[R] T) = 0) :
    s • ∑ k, a k • h (v k) = 0 := by
  let B : A →+ T →+ N := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun w => x • h w)
      (fun w w' => by rw [map_add (f := _), smul_add]))
      (fun x y => by ext w; simp [add_smul])
  have hB : ∀ x w, B x w = x • h w := fun _ _ => rfl
  let φ : A ⊗[R] T →+ N := TensorProduct.liftAddHom B (fun r x w => by
    rw [hB, hB, hh, Algebra.smul_def, mul_smul, smul_comm])
  have hφ : ∀ x w, φ (x ⊗ₜ[R] w) = x • h w := fun _ _ => rfl
  have hφs : ∀ (b : A) (y : A ⊗[R] T), φ (b • y) = b • φ y := fun b y => by
    induction y with
    | add y y' hy hy' => simp only [smul_add, map_add (f := _), hy, hy']
    | tmul x w => rw [TensorProduct.smul_tmul', hφ, hφ, smul_eq_mul, mul_smul]
  have := congrArg φ hs

  rw [hφs, map_sum, map_zero] at this
  simpa only [hφ] using this

end Abstract

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.E GlobalTheory.EtC GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

private theorem h_torsion {R : Type} [CommRing R] {C : Type*} [Category C] (F : C ⥤ ModuleCat.{0} R) (s : R)
    (hs : ∀ (T : C) (y : F.obj T), s • y = 0) (j : ℕ) (x : CH.H F j) : s • x = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h : s • f = 0 := Subtype.ext (funext fun t => hs _ _)
  rw [← Submodule.Quotient.mk_smul, h, Submodule.Quotient.mk_zero]

private theorem acr_torsion (A : PAlg l) (n : ℕ) (y : A.Acr n) : ((l : Acris l) ^ n) • y = 0 := by
  have h : A.mkAcr n ((l : A.Acr0) ^ n) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  rw [map_pow, map_natCast] at h
  rw [Algebra.smul_def, map_pow, map_natCast, h, zero_mul]

private theorem mh_torsion (P : PAlg l ⥤ Type) (n j : ℕ) (x : MH P n j) : ((l : Acris l) ^ n) • x = 0 :=
  h_torsion _ _ (fun _ y => acr_torsion _ n y) j x

private theorem zA_smul {N : Type*} [AddCommGroup N] [Module (Acris l) N] (n : ℕ)
    (hN : ∀ y : N, ((l : Acris l) ^ n) • y = 0) (z : ℤ_[l]) (y : N) :
    zA l z • y = (PadicInt.toZModPow n z).val • y :=
  _root_.UpperTheory.Reformulated.B.Qi53.zA_smul n hN z y

private theorem lev_smul (e : EtFam l K) (M : Model l K) (n j : ℕ) (z : ℤ_[l]) (w : M.T j) :
    e M n j ((z • w).lev n) = zA l z • e M n j (w.lev n) := by
  have hk : (z • w).lev n = (PadicInt.toZModPow n z).val • w.lev n :=
    HtL.smul_eq l n n le_rfl _ _ _ z ((show Hl l M.spc j 0 from w).1 n)
  have h2 := zA_smul n (mh_torsion M.P n j) z (e M n j (w.lev n))
  have h3 := map_nsmul (e M n j) (PadicInt.toZModPow n z).val (w.lev n)
  have h1 := congrArg (fun x => e M n j x) hk
  exact h1.trans (h3.trans h2.symm)

private def levAdd (e : EtFam l K) (M : Model l K) (n j : ℕ) : M.T j →+ M.MH n j :=
  AddMonoidHom.mk' (fun w => e M n j (w.lev n)) fun w w' => map_add (e M n j) (w.lev n) (w'.lev n)


theorem vecZero : VecZero := by
  intro l _ K B e _ M j ι _ v c r h
  have h' : ∑ k, ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (v k)) ⊗ₜ[ℚ_[l]] (B.c (c k) * Ring.inverse (B.c (tA l)) ^ r) = 0 := h
  letI : Algebra ℤ_[l] (Acris l) := (zA l).toAlgebra
  obtain ⟨u, hu⟩ := torsion_of_vec (R := ℤ_[l]) (F := ℚ_[l]) (T := M.T j) (tA l) B.c B.t_unit B.loc B.ker
    (fun x => B.z_c x) v c r h'
  refine ⟨0, u, fun n => ?_⟩
  rw [pow_zero, one_mul]
  have h2 := apply_tensor (R := ℤ_[l]) (N := M.MH n j) (levAdd e M n j) (fun z w => lev_smul e M n j z w) v c (tA l ^ u) hu
  exact h2

end UpperTheory.Ru.crystallineComparison
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def corrM (M : Model l K) (T : Corr l M.X) : Model l K := ⟨T.Z, T.p ≫ M.p⟩

def corrP (M : Model l K) (T : Corr l M.X) : E.gb (corrM M T) ⟶ E.gb M :=
  GlobalTheory.Et.geomMap (PadicAlgCl l) (corrM M T).q (Model.genMap (M := corrM M T) (N := M) T.p rfl) (Model.genMap_q (M := corrM M T) (N := M) T.p rfl)

def HkOfPush : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (M : Model l K) (T : Corr l M.X)
  (hr : T.r ≫ M.p = T.p ≫ M.p) (j : ℕ) (t : (corrM M T).V j →ₗ[ℚ_[l]] M.V j), LateralTheory.EtaleTrace.IsPush l (corrP M T) j t →
  IsHk M T hr j (t ∘ₗ Model.pullV (M := corrM M T) (N := M) T.r hr j)

end UpperTheory.Ru.crystallineComparison
end
end

section

open CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison

namespace UpperTheory.Ru.crystallineComparison.PBIota

open GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

variable {l : ℕ} [Fact l.Prime]

private theorem galCp_congr {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : (galCp σ : ℂ_[l] →+* ℂ_[l]) = galCp τ :=
  RingHom.ext fun x => congrFun (eq_galCp_of_continuous τ (galCp σ) (continuous_galCp σ)
    fun y => by rw [galCp_coe, h]) x

private theorem galMap_congr {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (galCp_congr σ τ h) _ _

private theorem galAway_congr {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galAway σ = ACris.galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers ((l : ℕ) : AInf ℂ_[l] l)) (RingHom.ext fun x => by
    rw [RingHom.comp_apply, RingHom.comp_apply, ACris.galAway_algebraMap, ACris.galAway_algebraMap,
      AInf.gal_smul_def, AInf.gal_smul_def, galMap_congr σ τ h])

private theorem galCris_congr {K L : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (σ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l) (τ : PadicAlgCl l ≃ₐ[L] PadicAlgCl l)
    (h : ∀ y, σ y = τ y) : ACris.galCris σ = ACris.galCris τ := by
  have e : ACris.galZero σ = ACris.galZero τ := RingHom.ext fun y => Subtype.ext (by
    rw [ACris.coe_galZero, ACris.coe_galZero, galAway_congr σ τ h])
  rw [ACris.galCris, ACris.galCris, e]

private theorem iC_injective : Function.Injective (iC l) :=
  (IsFractionRing.injective (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l)).comp ACris.iota_injective

private theorem iC_galA {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (g : K.fixingSubgroup)
    (a : Acris l) : iC l (galA g a) = Formalism.Per6.σD g.1 (iC l a) := by
  have e : galA g = ACris.galCris (Formalism.Per6.toBot g.1) :=
    galCris_congr _ _ fun _ => rfl
  rw [e]
  exact PositivityTheory.LocInh.GaloisCommutant.cD_galCris g.1 a

private theorem iC_zA (z : ℤ_[l]) : iC l (zA l z) = qQ l z := by
  change algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (ACris.iota ℂ_[l] l _) =
    algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (algebraMap ℚ_[l] (Formalism.Per6.BdRp l) _)
  exact congrArg _ (ACris.iota_padicInt z)

private theorem exists_lift {A C E : Type} [CommRing A] [CommRing C] [Field E] (t : A) (c : A →+* C)
    (i : A →+* E) (hu : IsUnit (c t)) (loc : ∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a)
    (ker : ∀ a : A, c a = 0 → ∃ r : ℕ, t ^ r * a = 0) (hi : Function.Injective i) (ht : i t ≠ 0) :
    ∃ ι : C →+* E, Function.Injective ι ∧ ∀ a, ι (c a) = i a := by
  letI : Algebra A C := c.toAlgebra
  have hc : ∀ a, algebraMap A C a = c a := fun _ => rfl
  haveI : IsLocalization (Submonoid.powers t) C :=
    { map_units := by
        rintro ⟨_, r, rfl⟩
        rw [hc, map_pow]
        exact hu.pow r
      surj := fun x => by
        obtain ⟨r, a, h⟩ := loc x
        refine ⟨⟨a, ⟨t ^ r, r, rfl⟩⟩, ?_⟩
        change x * algebraMap A C (t ^ r) = algebraMap A C a
        rw [hc, hc, map_pow, mul_comm, h]
      exists_of_eq := fun {x y} h => by
        rw [hc, hc] at h
        obtain ⟨r, hr⟩ := ker (x - y) (by rw [map_sub, h, sub_self])
        refine ⟨⟨t ^ r, r, rfl⟩, ?_⟩
        change t ^ r * x = t ^ r * y
        rw [mul_sub, sub_eq_zero] at hr
        exact hr }
  have hm : ∀ y : Submonoid.powers t, IsUnit (i y) := by
    rintro ⟨_, r, rfl⟩
    change IsUnit (i (t ^ r))
    rw [map_pow]
    exact (IsUnit.mk0 _ ht).pow r
  let ι : C →+* E := IsLocalization.lift (M := Submonoid.powers t) hm
  have hι : ∀ a, ι (c a) = i a := fun a => IsLocalization.lift_eq (M := Submonoid.powers t) hm a
  refine ⟨ι, (injective_iff_map_eq_zero ι).2 fun x hx => ?_, hι⟩
  obtain ⟨r, a, h⟩ := loc x
  have h1 : i a = 0 := by rw [← hι, ← h, map_mul, hx, mul_zero]
  have h2 : a = 0 := hi (by rw [h1, map_zero])
  rw [h2, map_zero] at h
  exact (hu.pow r).mul_right_eq_zero.1 h

private theorem lift_comm {A C E : Type} [CommRing A] [CommRing C] [Field E] (t : A) (c : A →+* C)
    (i : A →+* E) (loc : ∀ x : C, ∃ (r : ℕ) (a : A), c t ^ r * x = c a) (ht : i t ≠ 0)
    (ι : C →+* E) (hι : ∀ a, ι (c a) = i a) (s : C →+* C) (u : A →+* A) (d : E →+* E)
    (hs : ∀ a, s (c a) = c (u a)) (hd : ∀ a, i (u a) = d (i a)) (x : C) : ι (s x) = d (ι x) := by
  obtain ⟨r, a, h⟩ := loc x
  have h1 : d (i t) ^ r * ι (s x) = d (i a) := by
    have := congrArg (fun y => ι (s y)) h
    simp only [map_mul, map_pow, hs, hι, hd] at this
    exact this
  have h2 : i t ^ r * ι x = i a := by
    have := congrArg ι h
    simp only [map_mul, map_pow, hι] at this
    exact this
  rw [← h2, map_mul, map_pow] at h1
  exact mul_left_cancel₀ (pow_ne_zero _ ((map_ne_zero d).2 ht)) h1

private theorem q_ext {E : Type} [Field E] (f q : ℚ_[l] →+* E)
    (h : ∀ z : ℤ_[l], f (z : ℚ_[l]) = q (z : ℚ_[l])) : f = q :=
  IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (RingHom.ext h)

end UpperTheory.Ru.crystallineComparison.PBIota

open UpperTheory.Ru.crystallineComparison.PBIota in
theorem UpperTheory.Ru.crystallineComparison.pbIota :
    ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (B₀ : PB l K), ∃ ι : B₀.C →+* (per l K).B, Function.Injective ι ∧ (∀ a, ι (B₀.c a) = (per l K).i a) ∧ (∀ z, ι (algebraMap ℚ_[l] B₀.C z) = (per l K).q z) ∧ ∀ g x, ι (B₀.σ g x) = (per l K).σ g (ι x) := by
  intro l _ K B₀
  have ht0 : DeRhamPotentiallySemistable.DRPst.iC l (tA l) ≠ 0 := (period_ring_base.isUnit_image_period l).ne_zero
  obtain ⟨ι, hinj, hι⟩ := exists_lift (tA l) B₀.c (DeRhamPotentiallySemistable.DRPst.iC l) B₀.t_unit B₀.loc B₀.ker
    iC_injective ht0
  refine ⟨ι, hinj, hι, fun z => ?_, fun g x => ?_⟩
  · exact RingHom.congr_fun (q_ext (ι.comp (algebraMap ℚ_[l] B₀.C)) (DeRhamPotentiallySemistable.DRPst.qQ l) fun z =>
      (congrArg ι (B₀.z_c z)).trans ((hι _).trans (iC_zA z))) z
  · exact lift_comm (tA l) B₀.c (DeRhamPotentiallySemistable.DRPst.iC l) B₀.loc ht0 ι hι (B₀.σ g : B₀.C →+* B₀.C)
      (galA g) (Formalism.Per6.σD g.1 : Formalism.Per6.BdR l ≃+* Formalism.Per6.BdR l).toRingHom (B₀.σ_c g) (iC_galA g) x
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

private abbrev coefT (l : ℕ) [Fact l.Prime] (n : ℕ) : Test l ⥤ ModuleCat.{0} (Acris l) :=
  CH.modF (testι l ⋙ AcrA l n)

private lemma add_gen {C : Type 1} [Category.{0} C] (Pa : Parts C) {R : Type} [CommRing R]
    (F : C ⥤ ModuleCat.{0} R)
    (hF : ∀ (A : C) (S : Fam A), Pa.Cov S →
      Function.Bijective fun (x : F.obj A) (i : S.ι) => (F.map (S.f i)).hom x)
    (F' : Coef C) (c : ∀ A, F.obj A ≃+ F'.obj A)
    (hc : ∀ {A B : C} (φ : A ⟶ B) (x : F.obj A), c B ((F.map φ).hom x) = (F'.map φ).hom (c A x)) :
    Pa.Add F' := by
  intro A S hS
  have e : (fun (x : F'.obj A) (i : S.ι) => (F'.map (S.f i)).hom x) =
      (fun (v : ∀ i, F.obj (S.B i)) (i : S.ι) => c (S.B i) (v i)) ∘
        (fun (x : F.obj A) (i : S.ι) => (F.map (S.f i)).hom x) ∘ (c A).symm := by
    funext x i
    have := hc (S.f i) ((c A).symm x)
    rw [AddEquiv.apply_symm_apply] at this
    exact this.symm
  rw [e]
  exact (Equiv.piCongrRight fun i => (c (S.B i)).toEquiv).bijective.comp
    ((hF A S hS).comp (c A).symm.bijective)

private lemma coefT_add (hA : AcrAdd) (Pa : Parts (Test l))
    (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S) (n : ℕ) (A : Test l) (S : Fam A)
    (hS : Pa.Cov S) :
    Function.Bijective fun (x : (coefT l n).obj A) (i : S.ι) => ((coefT l n).map (S.f i)).hom x :=
  hA l n A S ((hPa A S).1 hS)

private lemma avg_gen (hLA : LocAvg) {C : Type 1} [Category.{0} C] (Pa : Parts C) (T : Theory C)
    {R : Type} [CommRing R] (F : C ⥤ ModuleCat.{0} R) (F' : Coef C) (hF : Pa.Add F')
    (e : ∀ (P : C ⥤ Type) (j : ℕ), CH.H (CategoryOfElements.π P ⋙ F) j ≃+ T.H P F' j)
    {Q P : C ⥤ Type} (p : Q ⟶ P) {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (hL : Pa.LocTrans p g)
    (m : CH.Mor (CategoryOfElements.π P ⋙ F) (CategoryOfElements.π Q ⋙ F) (RingHom.id R)) (j : ℕ)
    (hm : ∀ x, e Q j (m.pull j x) = T.pull p F' j (e P j x))
    (x : CH.H (CategoryOfElements.π P ⋙ F) j) (hx : m.pull j x = 0) : Fintype.card I • x = 0 := by
  have h0 : T.pull p F' j (e P j x) = 0 := by
    simpa only [hx, AddEquiv.map_zero] using (hm x).symm
  apply (e P j).injective
  change (e P j).toAddMonoidHom (Fintype.card I • x) = (e P j).toAddMonoidHom 0
  rw [map_nsmul, map_zero]
  exact hLA C Pa T F' hF Q P p I g hL j _ h0

private def pullT {Q P : PAlg l ⥤ Type} (p : Q ⟶ P) (n : ℕ) :
    CH.Mor (CategoryOfElements.π (testι l ⋙ P) ⋙ coefT l n)
      (CategoryOfElements.π (testι l ⋙ Q) ⋙ coefT l n) (RingHom.id _) := pullMor p n

private lemma locTrans_of {Q P : PAlg l ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I]
    {g : I → (Q ⟶ Q)} (h : TTrans p g) (Pa : Parts (Test l))
    (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S) :
    Pa.LocTrans (Functor.whiskerLeft (testι l) p)
      (fun i => Functor.whiskerLeft (testι l) (g i)) := by
  refine ⟨fun i => ?_, fun A => h.2.1 A, fun A y y' hy => ?_⟩
  · rw [← Functor.whiskerLeft_comp, h.1 i]
  · obtain ⟨S, hS, hm⟩ := h.2.2 A y y' hy
    exact ⟨S, (hPa A S).2 hS, hm⟩

private lemma averaging_transfer_kills (hLA : LocAvg) (hP : PartsEx) (hA : AcrAdd) (hT : TheoryEx)
    {Q P : PAlg l ⥤ Type} (p : Q ⟶ P) {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : TTrans p g)
    (n j : ℕ) (x : CH.H (CategoryOfElements.π (testι l ⋙ P) ⋙ coefT l n) j)
    (hx : (pullT p n).pull j x = 0) : Fintype.card I • x = 0 := by
  refine Exists.elim (hP l) fun Pa hPa => Exists.elim (hT (Test l)) fun T hT => ?_
  refine Exists.elim (hT (Acris l) (coefT l n)) fun F' h1 => Exists.elim h1 fun c h2 =>
    Exists.elim h2 fun e h3 => ?_
  have hF : Pa.Add F' := add_gen Pa (coefT l n) (coefT_add hA Pa hPa n) F' c h3.1
  have hG : (pullT p n).G = CategoryOfElements.map (Functor.whiskerLeft (testι l) p) := rfl
  have hτ : ∀ (T : (testι l ⋙ Q).Elements) (y : ((CategoryOfElements.π (testι l ⋙ P) ⋙ coefT l n).obj ((pullT p n).G.obj T))),
      HEq ((pullT p n).τ T y) y := fun _ _ => HEq.rfl
  have hm := h3.2 (Functor.whiskerLeft (testι l) p) (pullT p n) hG hτ j
  have hL := locTrans_of h Pa hPa
  exact avg_gen hLA Pa T (coefT l n) F' hF e (Functor.whiskerLeft (testι l) p) hL (pullT p n) j hm x hx

end UpperTheory.Ru.crystallineComparison

open CategoryTheory CategoryTheory.Limits GroundTheory.PAdicHodge CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.avgMH :
    UpperTheory.Ru.crystallineComparison.AvgMH := by
  intro l _ Q P p I _ g h n j x hx
  exact averaging_transfer_kills locAvg partsEx acrAdd theoryEx p h n j x hx
end
end
