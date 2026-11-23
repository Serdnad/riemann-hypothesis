module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ThetaCoefficientMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Bundle003
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.til_co :
    ∀ (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] (R : Type) [CommRing R] [Algebra O R] [IsCO O R], ∃ _ : IsCO O' (Til O O' R), IsLocalHom (Til.ι O O' R) ∧ Til.s O O' R ∈ maximalIdeal (Til O O' R) := by
  intro O O' _ _ _ _ _ _ _ R _ _ _
  haveI hT := UpperTheory.V.CA.cl_bc O O' R
  let f : R →+* O' ⊗[O] R := (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).toRingHom
  have hint : f.IsIntegral := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact f.isIntegralElem_zero
    | tmul o r =>
      have ho : IsIntegral O ((Algebra.TensorProduct.includeLeft : O' →ₐ[O] O' ⊗[O] R) o) :=
        (Algebra.IsIntegral.isIntegral (R := O) o).map _
      rw [Algebra.TensorProduct.includeLeft_apply] at ho
      obtain ⟨p, hp, hpe⟩ := ho
      have h1 : f.IsIntegralElem (o ⊗ₜ[O] (1 : R)) := by
        refine ⟨p.map (algebraMap O R), hp.map _, ?_⟩
        rw [Polynomial.eval₂_map]
        have hc : f.comp (algebraMap O R) = algebraMap O (O' ⊗[O] R) :=
          (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).comp_algebraMap
        rw [hc]
        exact hpe
      have he : o ⊗ₜ[O] r = (o ⊗ₜ[O] (1 : R)) * f r := by
        show _ = _ * ((1 : O') ⊗ₜ[O] r)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [he]
      exact RingHom.IsIntegralElem.mul f h1 f.isIntegralElem_map
    | add x y hx hy => exact RingHom.IsIntegralElem.add f hx hy
  have hloc : IsLocalHom f := by
    refine ((IsLocalRing.local_hom_tfae f).out 1 5).mpr ?_
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hint (maximalIdeal (O' ⊗[O] R))
    exact IsLocalRing.eq_maximalIdeal this
  haveI hco : IsCO O' (Til O O' R) := UpperTheory.V.Alg.co_mvps O' (O' ⊗[O] R) Unit
  refine ⟨hco, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    have hr' : IsUnit (PowerSeries.C ((1 : O') ⊗ₜ[O] r) : PowerSeries (O' ⊗[O] R)) := hr
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C] at hr'
    exact hloc.map_nonunit r hr'
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    show ¬ IsUnit (PowerSeries.X : PowerSeries (O' ⊗[O] R))
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem star_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [CommRing O']
    [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] (B : Type) [CommRing B] [Algebra O B] [Algebra O' B]
    (h : ∀ a : ℤ_[l], algebraMap O B (algebraMap ℤ_[l] O a) = algebraMap O' B (algebraMap ℤ_[l] O' a))
    (n : ℕ) (y : MonoidAlgebra B F.G₀) : F.star O B n y = F.star O' B n y := by
  have he : F.eps O B = F.eps O' B := by
    ext g
    simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe,
      RingHom.coe_comp, Function.comp_apply]
    exact h _
  have hop : F.starOp O B n = F.starOp O' B n := by
    ext g
    simp [GFrame.starOp, he]
  unfold GFrame.star
  rw [hop]

private theorem diag_map {H A B : Type} [Group H] [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B)
    (χ : Fin n → H →* Aˣ) :
    (GDet.ofRep (diagRep χ)).map f = GDet.ofRep (diagRep fun i => pushCh f (χ i)) := by
  rw [(UpperTheory.V.CA.d_gmap (GDet.ofRep (diagRep χ))).2.2.2 f (diagRep χ)]
  congr 1
  ext g a b
  by_cases hab : a = b
  · subst hab
    simp [diagRep]
  · simp [diagRep, hab]

private theorem push_ker {H A B : Type} [Group H] [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) (χ : H →* Aˣ) : (pushCh f χ).ker = χ.ker :=
  MonoidHom.ker_comp_of_injective _ _ (Units.map_injective hf)

theorem UpperTheory.V.Pa.BC.resid_bc :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [IsScalarTower ℤ_[l] O O'] (n : ℕ) (r : Resid F O n), (∃ r' : Resid F O' n, RBC r r') ∧ ∀ r' : Resid F O' n, RBC r r' → (∀ u, r'.Ip u = r.Ip u) ∧ r'.Dbar = r.Dbar.map (ResidueField.map (algebraMap O O')) ∧ ∀ i g, r'.chib i g = 1 ↔ r.chib i g = 1 := by
  intro l _ F O O' _ _ _ _ _ _ _ _ _ n r
  let φ : ResidueField O →+* ResidueField O' := ResidueField.map (algebraMap O O')
  have hφ : Function.Injective φ := φ.injective
  have hker : ∀ {H : Type} [Group H] (χ : H →* (ResidueField O)ˣ), (pushCh φ χ).ker = χ.ker :=
    fun χ => push_ker φ hφ χ
  have hpolar : F.IsPolar O' (GDet.ofRep (diagRep fun i => pushCh φ (r.chib i))) := by
    intro B _ _ _ _ y
    letI : Algebra (ResidueField O) B := ((algebraMap (ResidueField O') B).comp φ).toAlgebra
    letI : Algebra O B := ((algebraMap O' B).comp (algebraMap O O')).toAlgebra
    haveI : IsScalarTower O (ResidueField O) B := IsScalarTower.of_algebraMap_eq (fun a => by
      show algebraMap O' B (algebraMap O O' a) = algebraMap (ResidueField O') B (φ (algebraMap O (ResidueField O) a))
      rw [ResidueField.algebraMap_eq, ResidueField.map_residue, ← ResidueField.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply O' (ResidueField O') B])
    have hp := r.polar B y
    have hs := star_eq F O' O B (fun a => by
      show algebraMap O' B (algebraMap ℤ_[l] O' a) = algebraMap O' B (algebraMap O O' (algebraMap ℤ_[l] O a))
      rw [← IsScalarTower.algebraMap_apply ℤ_[l] O O']) n y
    rw [hs]
    have hd : ∀ x, (GDet.ofRep (diagRep fun i => pushCh φ (r.chib i))).D B x =
        (GDet.ofRep (diagRep r.chib)).D B x := by
      intro x
      rw [← diag_map φ r.chib]
      rfl
    rw [hd, hd]
    exact hp
  have hmain : ∀ r' : Resid F O' n, RBC r r' →
      (∀ u, r'.Ip u = r.Ip u) ∧ r'.Dbar = r.Dbar.map (ResidueField.map (algebraMap O O')) ∧
        ∀ i g, r'.chib i g = 1 ↔ r.chib i g = 1 := by
    intro r' ⟨hc, _, _⟩
    refine ⟨fun u => ?_, ?_, fun i g => ?_⟩
    · rw [Resid.Ip, Resid.Ip]
      congr 2
      funext i
      rw [hc i]
      exact hker _
    · have hfun : r'.chib = fun i => pushCh φ (r.chib i) := funext hc
      simp only [Resid.Dbar]
      rw [hfun, diag_map]
    · rw [hc i]
      show Units.map (φ : ResidueField O →* ResidueField O') (r.chib i g) = 1 ↔ _
      rw [← map_one (Units.map (φ : ResidueField O →* ResidueField O')),
        (Units.map_injective (f := (φ : ResidueField O →* ResidueField O')) hφ).eq_iff]
  refine ⟨⟨⟨fun i => pushCh φ (r.chib i), fun i => ?_, fun i j hij => ?_, hpolar,
    fun v i => pushCh φ (r.psib v i), fun v i => ?_, fun v i => pushCh (algebraMap O O') (r.th v i),
    fun v i g hg => ?_⟩, fun i => rfl, fun v i => rfl, fun v i => rfl⟩, hmain⟩
  · rw [hker]; exact r.chib_open i
  · apply r.chib_inj
    exact MonoidHom.ext fun g =>
      Units.map_injective (f := (φ : ResidueField O →* ResidueField O')) hφ (DFunLike.congr_fun hij g)
  · rw [hker]; exact r.psib_open v i
  · show Units.map (algebraMap O O' : O →* O') (r.th v i g) = 1
    rw [r.th_comm v i g hg, map_one]
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem gdet_ofRep_diagRep_map_eq_ofRep_pushCh {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G]
    (χ : Fin n → G →* Aˣ) (f : A →+* A') :
    (GDet.ofRep (diagRep χ)).map f = GDet.ofRep (diagRep (fun i => pushCh f (χ i))) := by
  refine GDet.ext fun B _ _ x => ?_
  simp only [GDet.map, GDet.ofRep, GDet.repAlg]
  congr 4
  apply congrArg
  refine MonoidHom.ext fun s => ?_
  ext i j
  simp [diagRep, pushCh, Matrix.diagonal_apply, RingHom.algebraMap_toAlgebra]
  split_ifs <;> simp

private theorem gdet_map_chi_mapRingHom_eq_map_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (x : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f x) = (D.chi x).map f := by
  letI : Algebra A (Polynomial A') := ((algebraMap A' (Polynomial A')).comp f).toAlgebra
  let φ : Polynomial A →ₐ[A] Polynomial A' :=
    { Polynomial.mapRingHom f with
      commutes' := fun a => by simp [RingHom.algebraMap_toAlgebra] }
  have key := D.nat (Polynomial A) (Polynomial A') φ
    (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) x)
  have e : (MonoidAlgebra.mapRingHom G (φ : Polynomial A →+* Polynomial A'))
        (MonoidAlgebra.single 1 Polynomial.X - (MonoidAlgebra.mapRingHom G Polynomial.C) x)
      = MonoidAlgebra.single 1 Polynomial.X
          - (MonoidAlgebra.mapRingHom G Polynomial.C) (MonoidAlgebra.mapRingHom G f x) := by
    rw [map_sub, MonoidAlgebra.mapRingHom_single]
    congr 1
    · simp [φ, Polynomial.mapRingHom]
    · ext g
      simp [φ, Polynomial.mapRingHom, MonoidAlgebra.mapRingHom]
  rw [e] at key
  exact key

private theorem gdet_map_lam_mapRingHom_eq_lam {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (i : ℕ) (x : MonoidAlgebra A G) :
    (D.map f).lam i (MonoidAlgebra.mapRingHom G f x) = f (D.lam i x) := by
  simp only [GDet.lam, gdet_map_chi_mapRingHom_eq_map_chi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]

private theorem adicCont_maximalIdeal_comp_of_isLocalHom {Γ R R' : Type} [TopologicalSpace Γ] [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (g : R →+* R') [IsLocalHom g] {φ : Γ → R}
    (h : AdicCont (maximalIdeal R) φ) : AdicCont (maximalIdeal R') (fun x => g (φ x)) := by
  intro N
  have hm : (maximalIdeal R).map g ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.mpr fun x hx => map_nonunit g x hx
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap g := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hm N
  have := (h N).comp (Ideal.quotientMap (maximalIdeal R' ^ N) g hle)
  convert this using 1
  funext x
  simp [Ideal.quotientMap_mk]

private theorem res_eq_zero_of_mem_maximalIdeal {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [IsCO O R] (x : R) (hx : x ∈ maximalIdeal R) : res O R x = 0 := by
  show ((RingEquiv.ofBijective _ _).symm.toRingHom.comp (residue R)) x = 0
  simp [(IsLocalRing.residue_eq_zero_iff x).mpr hx]

theorem UpperTheory.V.Pa.BC.pair_bc :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [IsScalarTower ℤ_[l] O O'] (n : ℕ) (r : Resid F O n) (r' : Resid F O' n), RBC r r' → ∀ (R R' : Type) [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O' R'] [IsCO O' R'] (g : R →+* R') [IsLocalHom g], (∀ a, g (algebraMap O R a) = algebraMap O' R' (algebraMap O O' a)) → ∀ p : Pair r R, (∀ x, res O' R' (g x) = ResidueField.map (algebraMap O O') (res O R x)) ∧ ∃ p' : Pair r' R', p.Maps g p'.D p'.ψ := by
  intro l _ F O O' _ _ _ _ _ _ _ _ _ n r r' hr R R' _ _ _ _ _ _ g _ hg p
  have hres : ∀ x, res O' R' (g x) = ResidueField.map (algebraMap O O') (res O R x) := by
    intro x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    have hx : x = algebraMap O R a + (x - algebraMap O R a) := by ring
    have h2 : g (x - algebraMap O R a) ∈ maximalIdeal R' := map_nonunit g _ ha
    rw [hx, map_add (f := _), map_add (f := _), map_add (f := _), hg, res_eq_zero_of_mem_maximalIdeal _ h2, res_eq_zero_of_mem_maximalIdeal _ ha, add_zero, add_zero,
      AlgHom.commutes, AlgHom.commutes, ResidueField.algebraMap_eq, ResidueField.algebraMap_eq,
      ResidueField.map_residue]
  have hs1 : ∀ h : F.G₀, (MonoidAlgebra.single h (1 : R') : MonoidAlgebra R' F.G₀)
      = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1) := by
    intro h
    simp [MonoidAlgebra.mapRingHom_single]
  refine ⟨hres, ⟨⟨p.D.map g, fun v i => pushCh g (p.ψ v i), ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, fun _ _ => rfl⟩⟩
  · intro i
    have key : (fun h : F.G₀ => (p.D.map g).lam i (MonoidAlgebra.single h 1))
        = fun h => g (p.D.lam i (MonoidAlgebra.single h 1)) := by
      funext h
      rw [hs1, gdet_map_lam_mapRingHom_eq_lam]
    show AdicCont _ _
    rw [key]
    exact adicCont_maximalIdeal_comp_of_isLocalHom g (p.cont i)
  · have hrg : ((res O' R' : R' →ₐ[O'] ResidueField O') : R' →+* ResidueField O').comp g
        = (ResidueField.map (algebraMap O O')).comp ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O) :=
      RingHom.ext hres
    have e1 : (p.D.map g).map ((res O' R' : R' →ₐ[O'] ResidueField O') : R' →+* ResidueField O')
        = (p.D.map ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O)).map
            (ResidueField.map (algebraMap O O')) := by
      refine GDet.ext fun B _ _ x => ?_
      simp only [GDet.map]
      congr 2
      congr 1
      refine RingHom.ext fun y => ?_
      show algebraMap (ResidueField O') B (res O' R' (g y)) = algebraMap (ResidueField O') B (ResidueField.map (algebraMap O O') (res O R y))
      rw [hres]
    rw [e1, p.red]
    show (GDet.ofRep (diagRep r.chib)).map _ = GDet.ofRep (diagRep r'.chib)
    rw [gdet_ofRep_diagRep_map_eq_ofRep_pushCh]
    congr 2
    funext i
    exact (hr.1 i).symm
  · intro v i
    refine ⟨?_, ?_, ?_⟩
    · have := adicCont_maximalIdeal_comp_of_isLocalHom g (p.psi v i).cont
      simpa [pushCh] using this
    · intro x
      have h1 := (p.psi v i).red x
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
      rw [hres, h1, hr.2.1 v i]
      simp [pushCh]
    · intro x
      have h1 := (p.psi v i).mu x
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
      rw [h1, hg, hr.2.2 v i]
      simp [pushCh]
  · intro i h
    have he : ∀ y : F.G₀, Units.map (g : R →* R') (F.eps O R y) = F.eps O' R' y := by
      intro y
      ext
      simp [GFrame.eps, pushCh, hg, ← IsScalarTower.algebraMap_apply]
    have hs : F.star O' R' n (MonoidAlgebra.single h 1)
        = MonoidAlgebra.mapRingHom F.G₀ g (F.star O R n (MonoidAlgebra.single h 1)) := by
      simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, MonoidAlgebra.mapRingHom_single, ← he]
      rw [← map_zpow]
      rfl
    rw [hs, hs1, gdet_map_lam_mapRingHom_eq_lam, gdet_map_lam_mapRingHom_eq_lam, p.P]
  · intro v gg h
    have e : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh g (p.ψ v i)) gg
        = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) gg) := by
      rw [map_mul, ← hs1]
      congr 1
      simp [GFrame.oEl, map_list_prod, List.map_ofFn, Function.comp_def, pushCh,
        MonoidAlgebra.mapRingHom_single]
    have h0 := p.Ord v gg h
    simp only [GDet.tr] at h0 ⊢
    rw [e, gdet_map_lam_mapRingHom_eq_lam, h0, map_zero]
  · intro u x hx h
    have hx' : x ∈ r.Ip u := by
      simp only [Resid.Ip, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker] at hx ⊢
      refine ⟨hx.1, fun i => ?_⟩
      have h2 := hx.2 i
      rw [hr.1 i] at h2
      ext
      have h3 := congrArg (fun u : (ResidueField O')ˣ => (u : ResidueField O')) h2
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h3
      apply (ResidueField.map (algebraMap O O')).injective
      rw [h3, Units.val_one, map_one]
    have e : MonoidAlgebra.single h (1 : R') * (MonoidAlgebra.single x 1 - 1)
        = MonoidAlgebra.mapRingHom F.G₀ g (MonoidAlgebra.single h 1 * (MonoidAlgebra.single x 1 - 1)) := by
      simp [MonoidAlgebra.mapRingHom_single]
    have h0 := p.I u x hx' h
    simp only [GDet.tr] at h0 ⊢
    rw [e, gdet_map_lam_mapRingHom_eq_lam, h0, map_zero]
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem tens_fin {Λ B S R M : Type} [CommRing Λ] [CommRing B] [CommRing S] [CommRing R] [Algebra B S]
    [AddCommGroup M] [Module B M] [Module Λ M] [Module.Finite B S] [Module.Finite Λ M]
    (lam : Λ → B) (hl : ∀ (a : Λ) (m : M), a • m = lam a • m) (θ : R →+* S)
    (hθ : ∀ a : Λ, ∃ t : R, θ t = algebraMap B S (lam a)) :
    ∃ s : Finset (S ⊗[B] M), ∀ z, ∃ c : S ⊗[B] M → R, z = ∑ g ∈ s, θ (c g) • g := by
  classical
  obtain ⟨a, ha⟩ := Module.Finite.fg_top (R := B) (M := S)
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := Λ) (M := M)
  let s : Finset (S ⊗[B] M) := Finset.image₂ (fun x y => x ⊗ₜ[B] y) a t
  refine ⟨s, ?_⟩
  have h1 : ∀ x ∈ a, ∀ y : M, x ⊗ₜ[B] y ∈ Submodule.span θ.range (s : Set (S ⊗[B] M)) := by
    intro x hx y
    have hy : y ∈ Submodule.span Λ (t : Set M) := ht ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image₂_of_mem hx hy))
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y y' _ _ h h' => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h h'
    | smul c y _ h =>
      obtain ⟨w, hw⟩ := hθ c
      rw [hl, TensorProduct.tmul_smul, ← algebraMap_smul S]
      exact Submodule.smul_mem _ (⟨algebraMap B S (lam c), w, hw⟩ : θ.range) h
  have h2 : ∀ x : S, ∀ y : M, x ⊗ₜ[B] y ∈ Submodule.span θ.range (s : Set (S ⊗[B] M)) := by
    intro x
    have hx : x ∈ Submodule.span B (a : Set S) := ha ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx => exact h1 x hx
    | zero => intro y; rw [TensorProduct.zero_tmul]; exact Submodule.zero_mem _
    | add x x' _ _ h h' => intro y; rw [TensorProduct.add_tmul]; exact Submodule.add_mem _ (h y) (h' y)
    | smul c x _ h => intro y; rw [TensorProduct.smul_tmul]; exact h _
  intro z
  have hz : z ∈ Submodule.span θ.range (s : Set (S ⊗[B] M)) := by
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul x y => exact h2 x y
    | add z z' h h' => exact Submodule.add_mem _ h h'
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hz
  choose c hc using fun g => (f g).2
  refine ⟨c, ?_⟩
  rw [← hf]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hc]
  rfl

theorem UpperTheory.V.Pa.BC.exists_finite_spanning_taylorWiles_tensor :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (σ : Type) (D : ℕ) (b : TWBase u J σ D) (G : Glob l L) (h : G.Hom G0) (q : ℕ) (ut : Fin q → Fin n → O) (N : ℕ) (A : TWRing b h ut N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ) (m : TWMaps Nq ph ta A ex), ∃ s : Finset (SpAt u (fun j => h.p₀ (ph j)) ut ⊗[B] b.M), ∀ z, ∃ c : _ → A.R, z = ∑ g ∈ s, m.θ (c g) • g := by
  intro l _ L G0 n O _ _ _ r B _ _ _ u J σ D b G h q ut N A Nq ph ta ex m
  haveI : Module.Finite B (SpAt u (fun j => h.p₀ (ph j)) ut) := (UpperTheory.V.Pa.BC.sp_fin B q n _ _).1
  haveI := b.fin
  exact tens_fin (Λ := abelian₂ O σ D) (fun a => b.lam a) b.smul_lam m.θ.toRingHom fun a =>
    ⟨A.s (MvPowerSeries.C a), by
      have := m.theta_coefficientMap_eq (MvPowerSeries.C a)
      rw [MvPowerSeries.constantCoeff_C] at this
      exact this⟩
end
