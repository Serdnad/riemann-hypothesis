module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.Bundle001
public import Formalism.RealPlaceAnalysis.Bundle003
public import GroundTheory.AutomorphicForms.HarishChandraCentre.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle001
import Formalism.RealPlaceAnalysis.Bundle005
public import GroundTheory.AutomorphicForms.Bundle012
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob

private lemma zd_comm {K : Type} [Field K] {Δ : K} {z : DX Δ} (hz : z ∈ ZD Δ) (g : DX Δ) : z * g = g * z := by
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.1 hz
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.val_mul]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ _) _).eq

private lemma conj_sup {G : Type} [Group G] (Z J : Subgroup G) (f : G → ℂ)
    (hZ : ∀ z ∈ Z, ∀ g, z * g = g * z) (hJ : ∀ u ∈ J, ∀ g, f (u⁻¹ * g * u) = f g) :
    ∀ u ∈ Z ⊔ J, ∀ g, f (u⁻¹ * g * u) = f g := by
  let S : Subgroup G :=
    { carrier := {u | ∀ g, f (u⁻¹ * g * u) = f g}
      one_mem' := by intro g; simp
      mul_mem' := by
        intro a b ha hb g
        have : (a * b)⁻¹ * g * (a * b) = b⁻¹ * (a⁻¹ * g * a) * b := by group
        rw [this, hb, ha]
      inv_mem' := by
        intro a ha g
        rw [← ha]
        congr 1
        group }
  have h : Z ⊔ J ≤ S := by
    refine sup_le (fun z hz g => ?_) (fun u hu => hJ u hu)
    rw [mul_assoc, ← hZ z hz, inv_mul_cancel_left]
  exact fun u hu => h hu

theorem UpperTheory.orbitalFiber_fixedSet_conj :
    UpperTheory.V.Z.Sym.Glob.Fib.FSConj := by
  intro F _ _ Δ D hD t ht u hu g
  unfold Dat.FS
  refine finprod_congr fun v => ?_
  have huv : u.1 v ∈ ZD _ ⊔ D.J2v v := by
    simp only [Dat.UZ, RPG.box, Subgroup.mem_iInf, Subgroup.mem_comap] at hu
    exact hu v
  show D.fSv t v ((u.1 v)⁻¹ * g.1 v * u.1 v) = D.fSv t v (g.1 v)
  refine conj_sup _ _ (D.fSv t v) (fun z hz => zd_comm hz) ?_ _ huv _
  intro k hk y
  unfold Dat.fSv
  unfold Dat.J2v at hk
  by_cases hv : v ∈ D.Sg
  · simp only [if_pos hv] at hk ⊢
    have H := (hD.sig v hv).S_inv (t v) (ht v hv)
    rw [(H k hk _).2, (H _ (inv_mem hk) _).1]
  · simp only [if_neg hv] at hk ⊢
    congr 1
    apply propext
    rw [Subgroup.mul_mem_cancel_right _ hk, Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
end

section

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix in
private theorem UpperTheory.star_diagonal_entry_eq {K : Type} [Field K] {Δ : K} (γ : DX Δ) :
    star (mt γ 0 0) = mt γ 1 1 := by
  have h : GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) (γ : GL (Fin 2) (Lsq K Δ)) =
      (wJ Δ)⁻¹ * (γ : GL (Fin 2) (Lsq K Δ)) * ((wJ Δ)⁻¹)⁻¹ := γ.2
  have h1 := congrArg (fun g : GL (Fin 2) (Lsq K Δ) => (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) h
  have hw : (((wJ Δ)⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![0, -1; 1, 0] := rfl
  have hw' : ((wJ Δ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = !![0, 1; -1, 0] := rfl
  simp only [inv_inv, Units.val_mul, hw, hw'] at h1
  simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply] using h1

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix in
theorem UpperTheory.orbitalFiber_hasTraceLaw :
    UpperTheory.V.Z.Sym.Glob.Fib.HasTrLaw := by
  intro K _ Δ γ
  have hmem : γ ∈ SU Δ ↔ (mt γ).det = 1 := by
    rw [SU, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hmem]
    constructor
    · intro hd
      refine ⟨(mt γ).trace.re, hd, ?_⟩
      have := UpperTheory.star_diagonal_entry_eq γ
      ext
      · simp
      · rw [Matrix.trace_fin_two, ← this]
        simp
    · rintro ⟨s, hs, _⟩
      exact hs
  · intro s s' hs hs'
    have := congrArg QuadraticAlgebra.re (hs.2.symm.trans hs'.2)
    simpa using this
  · intro h s
    have e : mt (h * γ * h⁻¹) = ((h : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * mt γ *
        (((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) := rfl
    unfold HasTr
    rw [e, Matrix.det_units_conj, Matrix.trace_units_conj]
end

section

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc Matrix

private theorem scal_mem {O L : Type} [CommRing O] [CommRing L] [Algebra O L] (u : Lˣ)
    (d : (integralClosure O L)ˣ)
    (h : u ^ 2 * Units.map ((integralClosure O L).val : integralClosure O L →* L) d = 1) :
    ∃ w : (integralClosure O L)ˣ, Units.map ((integralClosure O L).val : integralClosure O L →* L) w = u := by
  have h1 : u ^ 2 = Units.map ((integralClosure O L).val : integralClosure O L →* L) d⁻¹ := by
    rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
  have h2 : u⁻¹ ^ 2 = Units.map ((integralClosure O L).val : integralClosure O L →* L) d := by
    rw [inv_pow, h1, map_inv, inv_inv]
  have i1 : IsIntegral O (u : L) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [← Units.val_pow_eq_pow_val, h1]
    exact ((d⁻¹ : (integralClosure O L)ˣ) : integralClosure O L).2
  have i2 : IsIntegral O ((u⁻¹ : Lˣ) : L) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    rw [← Units.val_pow_eq_pow_val, h2]
    exact (d : integralClosure O L).2
  exact ⟨⟨⟨u, i1⟩, ⟨(u⁻¹ : Lˣ), i2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, Units.ext rfl⟩

theorem UpperTheory.orbitalFiber_det_eq_one :
    UpperTheory.V.Z.Sym.Glob.Fib.DetOne := by
  intro O K _ _ _ Δ g hg hs
  have hn : (ZD Δ).Normal := by
    refine ⟨fun n hn x => ?_⟩
    have : x * n * x⁻¹ = n := by
      obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.1 hn
      rw [mul_inv_eq_iff_eq_mul]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hz]
      apply Units.ext
      exact ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm).eq
    rwa [this]
  obtain ⟨s, hsz, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  refine mul_mem ?_ hk
  obtain ⟨z, hz⟩ := Subgroup.mem_subgroupOf.1 hsz
  obtain ⟨k₀, hk₀⟩ := Subgroup.mem_subgroupOf.1 hk
  have hd : GeneralLinearGroup.det ((s : GL (Fin 2) (Lsq K Δ)) * (k : GL (Fin 2) (Lsq K Δ))) = 1 := hs
  rw [map_mul, ← hz, ← hk₀] at hd
  obtain ⟨w, hw⟩ := scal_mem (O := O) (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ) z)
    (GeneralLinearGroup.det k₀) (by
      rw [← hd]
      congr 1
      · apply Units.ext
        simp [pow_two])
  refine Subgroup.mem_subgroupOf.2 ⟨GeneralLinearGroup.scalar (Fin 2) w, ?_⟩
  rw [← hz, MonoidHom.comp_apply, ← hw]
  apply Units.ext
  ext i j : 1
  by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply]
end

section

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob Matrix

private theorem hasTr_conj {K : Type} [Field K] {Δ : K} (γ h : DX Δ) (s : K) (hs : HasTr γ s) :
    HasTr (h⁻¹ * γ * h) s := by
  have e : Glob.mt (h⁻¹ * γ * h) = ((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) * Glob.mt γ * Glob.mt h := by
    rfl
  have e1 : Glob.mt h * (((h : GL (Fin 2) (Lsq K Δ))⁻¹ : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = 1 :=
    Units.mul_inv _
  refine ⟨?_, ?_⟩
  · rw [e, det_mul_comm, ← mul_assoc, e1, one_mul, hs.1]
  · rw [e, trace_mul_comm, ← mul_assoc, e1, one_mul, hs.2]

private theorem hasTr_map {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ : K} (γ : DX Δ) (γ' : DX (f Δ)) (s : K)
    (h : Glob.mt γ' = (Glob.mt γ).map (lmap f Δ)) (hs : HasTr γ s) : HasTr γ' (f s) := by
  refine ⟨?_, ?_⟩
  · rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hs.1, map_one]
  · rw [h, ← AddMonoidHom.map_trace, hs.2]
    ext <;> simp [lmap]

private theorem ne_zero_of_finprod {I : Type} (f : I → ℂ) (hf : (Function.mulSupport f).Finite) (h : ∏ᶠ i, f i ≠ 0) (i : I) :
    f i ≠ 0 := by
  intro h0
  apply h
  rw [finprod_eq_prod _ hf]
  refine Finset.prod_eq_zero (i := i) ?_ h0
  simp [h0]

theorem UpperTheory.orbitalFiber_fixedSet_support :
    UpperTheory.V.Z.Sym.Glob.Fib.FSSupp := by
  intro F _ _ Δ D hD ι hι t ht γ s g hs hne v hv
  have hconj : HasTr ((g⁻¹ * ι γ * g).1 v) (cv v s) :=
    hasTr_conj ((ι γ).1 v) (g.1 v) _ (hasTr_map (cv v) γ _ s (hι γ v) hs)
  generalize g⁻¹ * ι γ * g = x at hconj hne
  have hfin : (Function.mulSupport fun w => D.fSv t w (x.1 w)).Finite := by
    have h1 : {w | ¬ x.1 w ∈ KD (cv w Δ) (Ov w)}.Finite := Filter.eventually_cofinite.1 x.2
    refine (h1.union D.Sg.finite_toSet).subset fun w hw => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
    apply hw
    simp only [Dat.fSv, if_neg hc.2, Glob.one, if_pos hc.1]
  have h := ne_zero_of_finprod _ hfin hne v
  simp only [Dat.fSv, if_pos hv] at h
  exact (hD.sig v hv).S_supp _ (ht v hv) _ _ hconj h
end

section

open GroundTheory.Automorphic.HarishChandra in
private theorem qdet_mem_center (n : ℕ) (u : ℂ) :
    Formalism.REAL.qdet (fun i j : Fin n => e (i, j)) u ∈ Subalgebra.center ℂ (U n) := by
  have hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) := by
    intro i j k l
    exact e_mul_sub_mul (i, j) (k, l)
  refine mem_center_of_commute_e fun a => ?_
  exact (Formalism.REAL.qDetCentral (U n) n _ hgl u a.1 a.2).symm

open GroundTheory.Automorphic.HarishChandra in
private theorem hc_qdet (n : ℕ) (u : ℂ) :
    harishChandraHom (⟨_, qdet_mem_center n (u + ((n : ℂ) - 1) / 2)⟩ : Subalgebra.center ℂ (U n)) =
      ∏ k : Fin n, (MvPolynomial.C u + MvPolynomial.X k : MvPolynomial (Fin n) ℂ) := by
  rw [harishChandraHom_apply]
  dsimp only
  rw [UpperTheory.harishChandraProj_quantumDet_eq_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold GroundTheory.Automorphic.HarishChandra.translate
  rw [map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
    add_comm (MvPolynomial.X k), ← add_assoc, ← map_add]
  congr 2
  simp only [rhoVec, Pi.neg_apply]
  ring

theorem UpperTheory.center_envelopingGL_le_adjoin_quantumDet :
    ∀ n : ℕ, Subalgebra.center ℂ (GroundTheory.Automorphic.HarishChandra.U n) ≤ Algebra.adjoin ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet (fun i j : Fin n => GroundTheory.Automorphic.HarishChandra.e (i, j)) u) := by
  intro n z hz
  open GroundTheory.Automorphic.HarishChandra in
  let A : Subalgebra ℂ (Subalgebra.center ℂ (U n)) :=
    Algebra.adjoin ℂ (Set.range fun u : ℂ => ⟨_, qdet_mem_center n u⟩)
  have hle : MvPolynomial.symmetricSubalgebra (Fin n) ℂ ≤
      A.map GroundTheory.Automorphic.HarishChandra.harishChandraHom := by
    refine (UpperTheory.symmetricSubalgebra_le_adjoin_range_prod_C_add_X_complex n).trans (Algebra.adjoin_le ?_)
    rintro _ ⟨u, rfl⟩
    exact ⟨_, Algebra.subset_adjoin ⟨_, rfl⟩, hc_qdet n u⟩
  obtain ⟨a, ha, hae⟩ :=
    hle (GroundTheory.Automorphic.HarishChandra.harishChandraHom_mem_symmetricSubalgebra ⟨z, hz⟩)
  have haz : a = ⟨z, hz⟩ := GroundTheory.Automorphic.HarishChandra.harishChandraHom_injective hae
  have hval : A.map (Subalgebra.center ℂ (GroundTheory.Automorphic.HarishChandra.U n)).val =
      Algebra.adjoin ℂ (Set.range fun u : ℂ => Formalism.REAL.qdet
        (fun i j : Fin n => GroundTheory.Automorphic.HarishChandra.e (i, j)) u) := by
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  rw [← hval]
  exact ⟨a, ha, by rw [haz]; rfl⟩
end
