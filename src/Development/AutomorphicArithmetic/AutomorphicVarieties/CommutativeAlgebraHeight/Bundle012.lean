module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Coprod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
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
import Mathlib.RingTheory.TwoSidedIdeal.Instances
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem co_coprod_pres (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] :
    ∃ W : WPres O Unit R, ∀ s, W.z s ∈ maximalIdeal R := by
  obtain ⟨n, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (maximalIdeal R))
  have hm : ∀ s, z s ∈ maximalIdeal R := fun s => hz ▸ Submodule.subset_span ⟨s, rfl⟩
  haveI : IsCO O (MvPowerSeries (Fin n) O) := co_mvps O O (Fin n)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := co_ev O O R (Fin n) (Algebra.ofId _ _) z hm
  refine ⟨⟨Fin n, fun _ => (), F, ?_, ?_⟩, fun s => ?_⟩
  · refine co_surj O _ R _ (le_trans ?_ le_sup_left)
    rw [← hz, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rw [← hF s]
    refine Ideal.mem_map_of_mem _ fun hu => ?_
    simpa using MvPowerSeries.isUnit_constantCoeff _ hu
  · intro g hg j
    have : wcomp O (fun _ : Fin n => ()) j g = g := by
      ext a
      rw [coeff_wcomp, if_pos (Subsingleton.elim _ _)]
    rwa [this]
  · show F (MvPowerSeries.X s) ∈ _
    rw [hF]
    exact hm s

theorem UpperTheory.V.CA.co_coprod :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (T : Type) [Finite T] (B : T → Type) [∀ t, CommRing (B t)] [∀ t, Algebra O (B t)] [∀ t, IsCO O (B t)], ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (j : ∀ t, B t →ₐ[O] R), ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : ∀ t, B t →ₐ[O] R'), ∃! g : R →ₐ[O] R', ∀ t, g.comp (j t) = f t := by
  intro O _ _ _ _ T _ B _ _ _
  haveI := Fintype.ofFinite T
  choose WB hWB using fun t => co_coprod_pres O (B t)
  obtain ⟨R, i1, i2, i3, i, _, _, h, -⟩ := UpperTheory.V.Alg.coprod O Unit T B WB hWB
  exact ⟨R, i1, i2, i3, i, h⟩
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

private theorem dker_poly_eq (S : Type) [CommRing S] [Algebra A S] (p q : S[X] ⊗[A] E)
    (H : ∀ (T : Type) [CommRing T] [Algebra A T] (f : S[X] →ₐ[A] T), IsNilpotent (f X) →
      D.D T (Algebra.TensorProduct.map f (AlgHom.id A E) p) =
        D.D T (Algebra.TensorProduct.map f (AlgHom.id A E) q)) :
    D.D S[X] p = D.D S[X] q := by
  ext k
  have h := H _ (Ideal.Quotient.mkₐ A (Ideal.span {(X : S[X]) ^ (k + 1)})) ⟨k + 1, by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)⟩
  rw [D.nat, D.nat] at h
  have h2 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h)
  have h3 := X_pow_dvd_iff.1 h2 k (Nat.lt_succ_self k)
  rwa [coeff_sub, sub_eq_zero] at h3

private theorem dker_unit (T : Type) [CommRing T] [Algebra A T] (t : T) (ht : IsNilpotent t) (w : T ⊗[A] E) :
    IsUnit (1 + (t ⊗ₜ[A] (1 : E)) * w) := by
  apply IsNilpotent.isUnit_one_add
  obtain ⟨k, hk⟩ := ht
  have : (t ⊗ₜ[A] (1 : E)) * w = t • w := by rw [Algebra.smul_def]; rfl
  exact ⟨k, by rw [this, _root_.smul_pow, hk, zero_smul]⟩

private theorem dker_cancel (S : Type) [CommRing S] [Algebra A S] (w : S ⊗[A] E) :
    Det.cancel A E S S[X] (1 + X ⊗ₜ w) = 1 + ((X : S[X]) ⊗ₜ[A] (1 : E)) *
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) w := by
  rw [map_add (f := _), map_one]
  congr 1

private theorem dker_top (S : Type) [CommRing S] [Algebra A S] (w : S ⊗[A] E) :
    (D.D S[X] (1 + ((X : S[X]) ⊗ₜ[A] (1 : E)) *
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) w)).coeff n = D.D S w := by
  obtain ⟨h1, h2, -⟩ := d_bc D S
  obtain ⟨-, -, h3, h4, -⟩ := d_chi (D.baseChange S) w
  rw [← dker_cancel, ← h1, h3, ← h2, ← h4, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  simp

private theorem dker_of_kills {x : E} (hx : D.Kills x) : x ∈ D.ker := by
  rw [Det.mem_ker]
  intro S _ _ y u v
  rw [← dker_top, ← dker_top D S y]
  apply congrArg (fun p : S[X] => p.coeff n)
  apply dker_poly_eq
  intro T _ _ f hf
  simp only [map_add (f := _), map_mul, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) y) = y'
  generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) u) = u'
  generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) v) = v'
  obtain ⟨c, hc⟩ := dker_unit T (f X) hf y'
  have e : 1 + (f X ⊗ₜ[A] (1 : E)) * (y' + u' * (1 ⊗ₜ x) * v') =
      (c : T ⊗[A] E) * (1 + ((↑c⁻¹ : T ⊗[A] E) * (f X ⊗ₜ[A] (1 : E)) * u' * (1 ⊗ₜ x)) * v') := by
    rw [mul_add, mul_add, ← add_assoc, ← hc]
    simp only [← mul_assoc, Units.mul_inv, one_mul, mul_one]
  rw [e, map_mul, d_comm, ← mul_assoc, hx, mul_one, hc]

private theorem dker_kills_of {x : E}
    (hx : ∀ (S : Type) [CommRing S] [Algebra A S] (s : S) (y : S ⊗[A] E), D.D S (y + s ⊗ₜ x) = D.D S y) :
    D.Kills x := by
  intro S _ _ h
  have key : D.D S[X] (1 + (1 + ((X : S[X]) ⊗ₜ[A] (1 : E)) *
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) h) * (1 ⊗ₜ x)) =
      D.D S[X] 1 := by
    apply dker_poly_eq
    intro T _ _ f hf
    simp only [map_add (f := _), map_mul, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    generalize Algebra.TensorProduct.map f (AlgHom.id A E) (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) h) = h'
    obtain ⟨c, hc⟩ := dker_unit T (f X) hf h'
    have e : 1 + (c : T ⊗[A] E) * (1 ⊗ₜ x) = (c : T ⊗[A] E) * ((↑c⁻¹ : T ⊗[A] E) + 1 ⊗ₜ x) := by
      rw [mul_add, Units.mul_inv]
    rw [← hc, e, map_mul, hx, ← map_mul, Units.mul_inv, map_one]
  let ev : S[X] →ₐ[A] S := (Polynomial.aeval (R := S) (1 : S)).restrictScalars A
  have hev : Algebra.TensorProduct.map ev (AlgHom.id A E)
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S S[X]) (AlgHom.id A E) h) = h := by
    clear key
    induction h with
    | tmul b z => simp [ev]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hX : ev X = 1 := by simp [ev]
  have k2 := congrArg ev key
  rw [← D.nat, map_one, map_one] at k2
  simp only [map_add (f := _), map_mul, map_one, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hev, hX] at k2
  rw [← Algebra.TensorProduct.one_def, one_mul, add_mul, one_mul, add_comm (_ ⊗ₜ x), ← add_assoc, hx] at k2
  exact k2

end

theorem UpperTheory.V.CA.d_ker :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E), (x ∈ D.ker ↔ D.Kills x) ∧ (x ∈ D.ker ↔ ∀ (S : Type) [CommRing S] [Algebra A S] (s : S) (y : S ⊗[A] E), D.D S (y + s ⊗ₜ x) = D.D S y) ∧ (x ∈ D.ker → ∀ h i, 1 ≤ i → i ≤ n → D.lam i (h * x) = 0) := by
  intro n A E _ _ _ D x
  refine ⟨⟨fun hx S _ _ h => ?_, dker_of_kills D⟩,
    ⟨fun hx S _ _ s y => ?_, fun hx => dker_of_kills D (dker_kills_of D hx)⟩, fun hx h i h1 hi => ?_⟩
  · simpa using D.mem_ker.1 hx S 1 h 1
  · simpa using D.mem_ker.1 hx S y (s ⊗ₜ 1) 1
  · obtain ⟨-, -, h3, -⟩ := d_chi D (h * x)
    have h4 : D.D A[X] (1 + X ⊗ₜ (h * x)) = 1 := by
      simpa using D.mem_ker.1 hx A[X] 1 (X ⊗ₜ h) 1
    have h5 := congrArg (fun p => p.coeff i) (h3.symm.trans h4)
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_one] at h5
    simpa [Nat.lt_succ_of_le hi, show i ≠ 0 by omega] using h5
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.k_mem :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E), Polynomial.aeval x (D.chi x) ∈ D.CH := by
  intro n A E _ _ _ D x
  have key : ∀ w ∈ Submodule.span A ((fun z : E => (1 : A) ⊗ₜ[A] z) '' (D.CH : Set E)),
      Algebra.TensorProduct.lid A E w ∈ D.CH := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      simpa using hz
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul a y _ hy => rw [map_smul, Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hy
  have h1 := (d_chS D A).1 (1 ⊗ₜ x)
  have h2 : D.chiS A (1 ⊗ₜ x) = D.chi x := by simp [Det.chiS, Det.chi]
  rw [h2] at h1
  have h3 := key _ h1
  rw [← Polynomial.aeval_algHom_apply] at h3
  simpa using h3
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_unit :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), D.IsCH → (∀ x, IsUnit x ↔ IsUnit (D.val x)) ∧ Algebra.IsIntegral A E := by
  intro n A E _ _ _ D hD
  have h0 : ∀ x : E, Polynomial.aeval x (D.chi x) = 0 := ((d_chS D A).2.2 hD).2
  refine ⟨fun x => ⟨fun h => h.map D.val, fun h => ?_⟩, ⟨fun x => ?_⟩⟩
  · have h1 : D.lam n x = D.val x := (d_chi D x).2.2.2.1
    rw [← h1, Det.lam, Nat.sub_self] at h
    have hc : IsUnit ((D.chi x).coeff 0) := isUnit_of_mul_isUnit_right h
    have h2 := h0 x
    rw [← Polynomial.X_mul_divX_add (D.chi x), map_add (f := _), map_mul, Polynomial.aeval_X,
      Polynomial.aeval_C] at h2
    have h3 : IsUnit (x * Polynomial.aeval x (D.chi x).divX) := by
      rw [eq_neg_of_add_eq_zero_left h2]
      exact (hc.map (algebraMap A E)).neg
    have h4 : Commute x (Polynomial.aeval x (D.chi x).divX) := by
      have := (Commute.all (X : A[X]) (D.chi x).divX).map (Polynomial.aeval x)
      rwa [Polynomial.aeval_X] at this
    exact (h4.isUnit_mul_iff.1 h3).1
  · exact ⟨D.chi x, (d_chi D x).2.2.2.2.1, h0 x⟩
end

section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private def toMat {G R : Type} [Group G] [CommRing R] (ψ : G →* Rˣ) : G →* Matrix Unit Unit R where
  toFun g := Matrix.of fun _ _ => (ψ g : R)
  map_one' := by ext a b; simp
  map_mul' g h := by ext a b; simp [Matrix.mul_apply]

private noncomputable def ofMat {G R : Type} [Group G] [CommRing R] (ρ : G →* Matrix Unit Unit R) : G →* Rˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ρ g () ()
      map_one' := by simp
      map_mul' := fun g h => by simp [Matrix.mul_apply] }

private theorem lc_of_open {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f h

private theorem eq_one_of_pow {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (x : k) (m : ℕ)
    (h : x ^ l ^ m = 1) : x = 1 := by
  have h2 : (x - 1) ^ l ^ m = 0 := by rw [sub_pow_char_pow, h]; simp
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero m (Fact.out : l.Prime).ne_zero) |>.1 h2)

private theorem psib_th {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (v : F.Vl) (i : Fin n) (g : F.mu v) :
    ((r.psib v i g : (ResidueField O)ˣ) : ResidueField O) = residue O (r.th v i g) := by
  obtain ⟨m, hm⟩ := (CommGroup.primaryComponent.isPGroup (G := TopologicalAbelianization (F.Gv v)) (p := l))
    ⟨QuotientGroup.mk' _ (g : F.Gv v), g.2⟩
  have h1 : (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure ((g : F.Gv v) ^ l ^ m)) = 1 := by
    rw [map_pow]; exact congrArg Subtype.val hm
  have h2 : (g : F.Gv v) ^ l ^ m ∈ (commutator (F.Gv v)).topologicalClosure := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : (commutator (F.Gv v)).topologicalClosure ≤ (r.psib v i).ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _)
      (Subgroup.isClosed_of_isOpen _ (r.psib_open v i))
  have h4 : r.psib v i g ^ l ^ m = 1 := by rw [← map_pow]; exact h3 h2
  have h5 : r.th v i g ^ l ^ m = 1 := by rw [← map_pow]; exact r.th_comm v i _ h2
  rw [eq_one_of_pow l ((r.psib v i g : (ResidueField O)ˣ) : ResidueField O) m
      (by rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]),
    eq_one_of_pow l (residue O (r.th v i g)) m
      (by rw [← map_pow, ← Units.val_pow_eq_pow_val, h5, Units.val_one, map_one])]

theorem UpperTheory.V.CA.universalDeformationRing_localCharacters :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (v : F.Vl) (i : Fin n), PhiCond (F.Gv v) l → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (ψ : F.Gv v →* Rˣ), r.IsPsi v i ψ ∧ ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (ψ' : F.Gv v →* R'ˣ), r.IsPsi v i ψ' → ∃! f : R →ₐ[O] R', pushCh (f : R →+* R') ψ = ψ' := by
  intro l _ F O _ _ _ _ _ _ _ n r v i hΦ
  have hlc : IsLocallyConstant (r.psib v i) := lc_of_open _ (r.psib_open v i)
  have hlc' : IsLocallyConstant (toMat (r.psib v i)) :=
    hlc.comp fun x => (Matrix.of fun _ _ => (x : ResidueField O) : Matrix Unit Unit (ResidueField O))
  obtain ⟨R₀, _, _, _, u, hu⟩ := univ_lift l O (F.Gv v) Unit (toMat (r.psib v i)) hΦ hlc'
  let P : Cond O (toMat (r.psib v i)) := fun R _ _ _ s =>
    ∀ g : F.mu v, s.hom g () () = algebraMap O R (r.th v i g)
  have hP : P.IsClosed := fun R _ _ _ s => by
    refine ⟨Ideal.span (Set.range fun g : F.mu v => s.hom g () () - algebraMap O R (r.th v i g)),
      fun R' _ _ _ f => ⟨fun h x hx => ?_, fun h g => ?_⟩⟩
    · have : Ideal.span (Set.range fun g : F.mu v => s.hom g () () - algebraMap O R (r.th v i g)) ≤
          RingHom.ker f := by
        rw [Ideal.span_le]
        rintro _ ⟨g, rfl⟩
        show f _ = 0
        rw [map_sub, AlgHom.commutes, sub_eq_zero]
        exact h g
      exact this hx
    · have := h _ (Ideal.subset_span ⟨g, rfl⟩)
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  haveI := (co_res O).1
  have hres : ∀ x : ResidueField O, res O (ResidueField O) x = x := fun x => by
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact (res O (ResidueField O)).commutes a
  let r₁ : Lift O (toMat (r.psib v i)) (ResidueField O) :=
    { hom := toMat (r.psib v i)
      cont := fun a b N => hlc.comp fun x => Ideal.Quotient.mk _ (x : ResidueField O)
      red := fun g a b => hres _ }
  obtain ⟨R, _, _, _, p, -, hR⟩ := univ_cond O (F.Gv v) Unit _ R₀ u _ P hu hP
    ⟨ResidueField O, inferInstance, inferInstance, inferInstance, r₁, trivial, fun g => psib_th r v i g⟩
  refine ⟨R, inferInstance, inferInstance, inferInstance, ofMat (u.map p).hom,
    ⟨(u.map p).cont () (), fun g => (u.map p).red g () (), ((hR R).1 (AlgHom.id O R)).2⟩, fun R' _ _ _ ψ' h' => ?_⟩
  let s : Lift O (toMat (r.psib v i)) R' :=
    { hom := toMat ψ'
      cont := fun a b => h'.cont
      red := fun g a b => h'.red g }
  obtain ⟨f, hf, huniq⟩ := (hR R').2 s ⟨trivial, h'.mu⟩
  refine ⟨f, ?_, fun f' hf' => huniq f' ?_⟩
  · ext g
    exact congrArg (fun t : Lift O (toMat (r.psib v i)) R' => t.hom g () ()) hf
  · ext g a b
    exact congrArg (fun t : F.Gv v →* R'ˣ => ((t g : R'ˣ) : R')) hf'
end
