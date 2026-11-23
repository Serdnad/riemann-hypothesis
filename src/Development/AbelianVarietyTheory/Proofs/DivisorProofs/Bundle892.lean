module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle686
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.HopfAlgebra.Quotient
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle848
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle863
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle509
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle864
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle866
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle865
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

@[expose] public section

section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbFam.TwistSize

theorem intVec_mem_std {F : Type} [Field F] [NumberField F] (z : Fin 2 → ℤ) :
    (fun j ↦ ((z j : ℤ) : F)) ∈ stdLat F := by
  rw [stdLat, Submodule.mem_pi]
  intro j _
  exact Submodule.mem_one.2 ⟨(z j : 𝓞 F), by simp⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N n : ℕ) (L : Lat F) (α : GL (Fin 2) (ZMod N)) (ρ₀ : ℝ), L ≤ stdLat F → (∀ x ∈ stdLat F, (n : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → ![0, (n : F)] ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)) ∧ ∀ v ∈ twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N)), ∀ i : Emb F, Sz l lam ρ₀ ((i (v 0) : ℝ) : ℂ) := by
  intro l _ lam F _ _ _ N n L α ρ₀ hLs hnL hL hN
  have hR := GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops l lam
  have hZ := GlobalTheory.T.algebraicValuationAtLeast_basic_properties l lam
  let A : Matrix (Fin 2) (Fin 2) ℤ := (α : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)
  have hAα : A.map (Int.cast : ℤ → ZMod N) = (α : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
    ext i j; simp [A, ZMod.intCast_cast, ZMod.cast_id']
  have hI := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A · hLs)
  rw [← hAα]
  refine ⟨?_, ?_⟩
  · let B : Matrix (Fin 2) (Fin 2) ℤ :=
      ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)
    have h1 : ((α⁻¹ : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) * (α : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hmod : ∀ i j, (((B * A) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod N) = 0 := by
      intro i j
      have h2 := congrFun (congrFun h1 i) j
      rw [Matrix.mul_apply] at h2
      rw [Int.cast_sub, Matrix.mul_apply, Int.cast_sum, Matrix.one_apply]
      rw [Matrix.one_apply] at h2
      simp only [Int.cast_mul, B, A, Matrix.map_apply, ZMod.intCast_cast, ZMod.cast_id', id_eq]
      rw [h2]; split_ifs <;> simp
    have hdv : ∀ i j, (N : ℤ) ∣ (B * A) i j - (1 : Matrix (Fin 2) (Fin 2) ℤ) i j :=
      fun i j ↦ (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (hmod i j)
    choose D hD using hdv
    have hy : (fun j ↦ (n : F) * (B 1 j : F)) ∈ L := by
      have := hnL _ (intVec_mem_std (fun j ↦ B 1 j))
      convert this using 1
      ext j
      simp [Nat.cast_smul_eq_nsmul]
    have hw : (fun j ↦ -((n : F) * (D 1 j : F))) ∈ stdLat F := by
      have := Submodule.smul_mem (stdLat F) (-(n : 𝓞 F)) (intVec_mem_std (fun j ↦ D 1 j))
      convert this using 1
      ext j
      simp [Nat.cast_smul_eq_nsmul]
    refine (hI _).2 ⟨_, hy, _, hw, ?_⟩
    have hBA : ∀ j, (B 1 0 : F) * (A 0 j : F) + (B 1 1 : F) * (A 1 j : F) = (if (1 : Fin 2) = j then 1 else 0) + (N : F) * (D 1 j : F) := by
      intro j
      have := congrArg (Int.cast : ℤ → F) (hD 1 j)
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at this
      split_ifs at this ⊢ <;> push_cast at this ⊢ <;> linear_combination this
    ext j
    fin_cases j
    · have := hBA 0
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at this ⊢
      linear_combination -(n : F) * this
    · have := hBA 1
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at this ⊢
      linear_combination -(n : F) * this
  · intro v hv i
    obtain ⟨y, hy, w, hw, rfl⟩ := (hI v).1 hv
    have hw0 : w 0 ∈ (1 : Submodule (𝓞 F) F) := by
      rw [stdLat, Submodule.mem_pi] at hw; exact hw 0 (Set.mem_univ _)
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 hw0
    have hint : Sz l lam 0 ((i (w 0) : ℝ) : ℂ) := by
      refine hZ.1 1 _ (Nat.Prime.not_dvd_one (Fact.out)) ?_
      rw [Nat.cast_one, one_mul, ← hr]
      exact map_isIntegral_int ((Complex.ofRealHom.comp i).comp (algebraMap (𝓞 F) F)) (RingOfIntegers.isIntegral r)
    have heq : ((i ((Matrix.vecMul y (A.map (Int.cast : ℤ → F)) + (N : F) • w) 0) : ℝ) : ℂ) =
        ((i (y 0) : ℝ) : ℂ) * ((A 0 0 : ℤ) : ℂ) + ((i (y 1) : ℝ) : ℂ) * ((A 1 0 : ℤ) : ℂ) + (N : ℂ) * ((i (w 0) : ℝ) : ℂ) := by
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [heq]
    have p1 := hR.2.2.1 ρ₀ 0 _ _ (hL y hy 0 i) (hR.2.2.2.2.1 (A 0 0))
    have p2 := hR.2.2.1 ρ₀ 0 _ _ (hL y hy 1 i) (hR.2.2.2.2.1 (A 1 0))
    have p3 := hR.2.2.1 ρ₀ 0 _ _ hN hint
    rw [add_zero] at p1 p2 p3
    exact (hR.2.1 _ _ _ (hR.2.1 _ _ _ p1 p2).1 p3).1

end GlobalTheory.HilbFam.TwistSize
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.bijective_liftSemi_of_semilinear_hom : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (B B' : Type) [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] (α : B →+* B') (h : SemiHom (algebraMap R R') α) (f : B →ₛₗ[algebraMap R R'] B'), (∀ b, f b = α b) → Function.Bijective (liftSemi f) → Function.Bijective (liftSemi h.m1) := by
  first | exact @GlobalTheory.kaehler_liftSemi_bijective | exact GlobalTheory.kaehler_liftSemi_bijective | (intros; apply GlobalTheory.kaehler_liftSemi_bijective <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.pullbackForm_vanishes_tangents_of_lieBasis : ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B], Smooth B.hom → ∀ (n : ℕ) (y : Fin n → (epsR R ⟶ B)), IsLieBasis y → ∀ f : Form (B.hom ≫ 𝟙 (Sp R)), (∀ i, tanVal (y i) f = 0) → ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (B' : Over (Sp R')) [GrpObj B'] [IsCommMonObj B'] (φ : B'.left ⟶ B.left), IsGrpPullback B' B (spMap σ) φ → ∀ (m : IsMor (dp0 R) (B.hom ≫ 𝟙 (Sp R)) (dp0 R') (B'.hom ≫ 𝟙 (Sp R')) σ φ) (v : epsR R' ⟶ B'), IsTangent v → tanVal v (m.pullForm f) = 0 := by
  first | exact @GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis | exact GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis | (intros; apply GlobalTheory.LieDual.tanVal_pullForm_eq_zero_of_lieBasis <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (a' : OAct O A'), (∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left) → ∀ (z : O) {f : HdR A} {w : epsR R ⟶ A}, IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z) := by
  first | exact @GlobalTheory.KSExist.isKSValue_act | exact GlobalTheory.KSExist.isKSValue_act | (intros; apply GlobalTheory.KSExist.isKSValue_act <;> assumption)
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

noncomputable section

namespace GlobalTheory.HopfQuot

variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A] [IsCocomm k A]
  [Module.Finite k A] {C : Type} [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C]
  (π : A →ₐc[k] C)

instance isHopfIdeal_dual : (kerIdeal (CartierDual.map π)).IsHopfIdeal k := isHopfIdeal_kerIdeal _

abbrev proj : CartierDual k A →ₐc[k] CartierDual k A ⧸ kerIdeal (CartierDual.map π) :=
  Bialgebra.Quotient.mkBialgHom _

instance isCocomm_quot : IsCocomm k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)) :=
  isCocomm_of_surjective (proj π) Ideal.Quotient.mk_surjective

def quotMap : CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)) →ₐc[k] A :=
  ((CartierDual.bidual k A).symm : _ →ₐc[k] A).comp (CartierDual.map (proj π))

theorem apply_quotMap (y : CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)))
    (φ : CartierDual k A) : φ (quotMap π y) = y (proj π φ) := by
  simp [quotMap]

theorem proj_map (ψ : CartierDual k C) :
    proj π (CartierDual.map π ψ) = algebraMap k _ (counit (R := k) ψ) := by
  have hmem : CartierDual.map π ψ - algebraMap k _ (counit (R := k) ψ) ∈
      kerIdeal (CartierDual.map π) := by
    have h : CartierDual.map π ψ - algebraMap k _ (counit (R := k) ψ) =
        CartierDual.map π (ψ - algebraMap k _ (counit (R := k) ψ)) := by
      rw [map_sub, AlgHomClass.commutes]
    rw [h]
    exact Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])
  rw [← sub_eq_zero, ← AlgHomClass.commutes (proj π), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.2 hmem

theorem quotMap_trivial (y : CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π))) :
    π (quotMap π y) = algebraMap k C (counit (R := k) y) := by
  refine CartierDual.eq_of_forall_apply (R := k) fun ψ => ?_
  have h1 : ψ (π (quotMap π y)) = (CartierDual.map π ψ) (quotMap π y) := rfl
  rw [h1, apply_quotMap, proj_map, CartierDual.counit_apply, CartierDual.counit_apply,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, map_smul]
  simp [mul_comm]

theorem mem_range_quotMap {a : A} (ha : ∀ x ∈ kerIdeal (CartierDual.map π), x a = 0) :
    a ∈ Set.range (quotMap π) := by
  have hann : (CartierDual.bidual k A a).ofConv ∈
      (LinearMap.ker (proj π : CartierDual k A →ₐ[k] CartierDual k A ⧸ kerIdeal (CartierDual.map π)).toLinearMap).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    have hx' : x ∈ kerIdeal (CartierDual.map π) :=
      Ideal.Quotient.eq_zero_iff_mem.1 (LinearMap.mem_ker.1 hx)
    exact ha x hx'
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
  obtain ⟨y, hy⟩ := hann
  refine ⟨WithConv.toConv y, ?_⟩
  refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
  rw [apply_quotMap]
  exact LinearMap.congr_fun hy φ

theorem mul_map_apply {D : Type} [CommRing D] [Bialgebra k D] (f : D →ₐc[k] A)
    (hf : kerIdeal f ≤ RingHom.ker π) (d : D) (r : CartierDual k A) (ψ : CartierDual k C) :
    (r * CartierDual.map π ψ) (f d) = r (f d) * ψ 1 := by
  have hπf := (kerIdeal_le_ker_iff f (π : A →ₐ[k] C)).1 hf
  have key : ∀ t : D ⊗[k] D, CartierDual.pair k A A (r ⊗ₜ CartierDual.map π ψ)
      (TensorProduct.map (f : D →ₗ[k] A) (f : D →ₗ[k] A) t) =
      r (f (TensorProduct.rid k D (LinearMap.lTensor D (counit (R := k) (A := D)) t))) * ψ 1 := by
    intro t
    induction t with
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_mul]
    | tmul x y =>
      rw [TensorProduct.map_tmul, CartierDual.pair_tmul_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, CartierDual.map_apply]
      have h1 : π (f y) = algebraMap k C (counit (R := k) y) := hπf y
      erw [h1]
      rw [map_smul, map_smul, Algebra.algebraMap_eq_smul_one, map_smul]
      simp only [smul_eq_mul]
      have hfx : (f : D →ₗ[k] A) x = f x := rfl
      rw [hfx]
      ring
  rw [CartierDual.mul_apply]
  have hc : comul (R := k) (f d) = TensorProduct.map (f : D →ₗ[k] A) (f : D →ₗ[k] A) (comul d) :=
    (LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) d).symm
  rw [hc, key, Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

theorem ideal_apply_eq_zero {D : Type} [CommRing D] [Bialgebra k D] (f : D →ₐc[k] A)
    (hf : kerIdeal f ≤ RingHom.ker π) (d : D) :
    ∀ x ∈ kerIdeal (CartierDual.map π), x (f d) = 0 := by
  intro x hx
  suffices h : ∀ r : CartierDual k A, (r * x) (f d) = 0 by simpa using h 1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, rfl⟩ := hx
    intro r
    have hψ' : ψ 1 = 0 := hψ
    erw [mul_map_apply π f hf d r ψ]
    rw [hψ', mul_zero]
  | zero => intro r; simp
  | add x y _ _ hx hy => intro r; simp [mul_add, hx r, hy r]
  | smul s x _ hx => intro r; rw [smul_eq_mul, ← mul_assoc]; exact hx (r * s)

theorem ideal_eq_of_le_of_finrank_eq {R : Type} [CommRing R] [Algebra k R] [Module.Finite k R]
    {I J : Ideal R} (hIJ : I ≤ J)
    (h : Module.finrank k (R ⧸ I) = Module.finrank k (R ⧸ J)) : I = J := by
  have h1 := Submodule.finrank_quotient_add_finrank (I.restrictScalars k)
  have h2 := Submodule.finrank_quotient_add_finrank (J.restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k I).finrank_eq] at h1
  rw [(Submodule.Quotient.restrictScalarsEquiv k J).finrank_eq] at h2
  have hle : I.restrictScalars k ≤ J.restrictScalars k := hIJ
  exact Submodule.restrictScalars_injective k R R
    (Submodule.eq_of_le_of_finrank_eq hle (by omega))

theorem finrank_cartierDual (M : Type) [AddCommGroup M] [Module k M] [FiniteDimensional k M] :
    Module.finrank k (CartierDual k M) = Module.finrank k M :=
  (CartierDual.toDual k M).finrank_eq.trans Subspace.dual_finrank_eq

theorem quotMap_injective : Function.Injective (quotMap π) := by
  intro x y hxy
  have h := congrArg (CartierDual.bidual k A) hxy
  simp only [quotMap, BialgHom.comp_apply] at h
  erw [BialgEquiv.apply_symm_apply, BialgEquiv.apply_symm_apply] at h
  exact CartierDual.map_injective_of_surjective (f := proj π) Ideal.Quotient.mk_surjective h

theorem exists_quotient : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A]
    [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
    [Module.Finite k C] (π : A →ₐc[k] C), Function.Surjective π → ∃ (B : Type) (_ : CommRing B)
    (_ : HopfAlgebra k B) (_ : IsCocomm k B) (_ : Module.Finite k B) (j : B →ₐc[k] A),
    Function.Injective j ∧ kerIdeal j = RingHom.ker π ∧ ∀ (D : Type) [CommRing D]
    [Bialgebra k D] (f : D →ₐc[k] A), kerIdeal f ≤ RingHom.ker π → ∀ d, f d ∈ Set.range j := by
  intro k _ A _ _ _ _ C _ _ _ _ π hπ
  have hinj := quotMap_injective π
  refine ⟨CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)), inferInstance,
    inferInstance, inferInstance, inferInstance, quotMap π, hinj, ?_, ?_⟩
  · have hle : kerIdeal (quotMap π) ≤ RingHom.ker π :=
      (kerIdeal_le_ker_iff _ (π : A →ₐ[k] C)).2 (quotMap_trivial π)
    refine ideal_eq_of_le_of_finrank_eq (k := k) hle ?_
    have hA := GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k A _ (quotMap π)
    have hD := GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k (CartierDual k A) (CartierDual k C) (CartierDual.map π)
    rw [LinearMap.finrank_range_of_inj (f := ((quotMap π : CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)) →ₐ[k] A)).toLinearMap)
      (by exact hinj),
      finrank_cartierDual] at hA
    rw [LinearMap.finrank_range_of_inj (f := ((CartierDual.map π : CartierDual k C →ₐ[k] CartierDual k A)).toLinearMap)
      (by exact CartierDual.map_injective_of_surjective hπ), finrank_cartierDual,
      finrank_cartierDual] at hD
    have hC : Module.finrank k (A ⧸ RingHom.ker π) = Module.finrank k C :=
      (Ideal.quotientKerAlgEquivOfSurjective (f := (π : A →ₐ[k] C)) hπ).toLinearEquiv.finrank_eq
    haveI : Nontrivial A := RingHom.domain_nontrivial (counitAlgHom k A : A →+* k)
    have hpos : 0 < Module.finrank k A := Module.finrank_pos
    rw [hC]
    have hQ : 0 < Module.finrank k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)) := by
      rcases Nat.eq_zero_or_pos (Module.finrank k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)))
        with h0 | h0
      · rw [h0, mul_zero] at hD; omega
      · exact h0
    exact Nat.eq_of_mul_eq_mul_left hQ (by rw [← hA, hD, mul_comm])
  · intro D _ _ f hf d
    exact mem_range_quotMap π (ideal_apply_eq_zero π f hf d)

end GlobalTheory.HopfQuot
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TwPairUniq

theorem main : ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
    ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h := by
  intro q _ i j
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  obtain ⟨hI, -, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q i
  obtain ⟨hJ, hJflat, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q j
  have hT : IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) :=
    GlobalTheory.T.isTateTwistResolution_tensor_flat q i j (i + j) rfl _ _ hI hJ hJflat τ hτ
  obtain ⟨huniv, -, hext⟩ := GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ
  obtain ⟨-, -, hK⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q (i + j)
  obtain ⟨⟨u, hu⟩, huniq⟩ := hK _ hT
  refine ⟨?_, ?_⟩
  · obtain ⟨ν, hν⟩ := hext u
    show IsTwPair (pick IsTwPair)
    refine pick_spec ⟨ν, fun U ζ => ?_⟩
    exact (hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)).symm.trans (hu U ζ)
  · intro k hk μ ν hμ hν E n m w h
    subst hk
    obtain ⟨uμ, huμ, -⟩ := huniv μ (𝟙 _) (𝟙 _)
    obtain ⟨uν, huν, -⟩ := huniv ν (𝟙 _) (𝟙 _)
    have hom := huniq uμ uν (fun U ζ =>
      (huμ U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)).trans ((hμ U ζ).trans ((hν U ζ).symm.trans
        (huν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)).symm)))
    obtain ⟨hid, -, -, -, hhtp⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)
    have key : ∀ (π : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j)))) (v : T ⟶ res _ (tw q (i + j))),
        τ.Compat π (𝟙 _) (𝟙 _) v → ∀ a b, π.cup E h a b = cpush _ v w (τ.cup E h a b) := by
      intro π v hc a b
      rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ π (𝟙 _) (𝟙 _) v hc E h a b, (hid _ _ n a).2, (hid _ _ m b).2]
    refine AddMonoidHom.ext fun a => AddMonoidHom.ext fun b => ?_
    rw [key μ uμ huμ, key ν uν huν, (hhtp uμ uν hom _ w).2]

end GlobalTheory.EtC.TwPairUniq
end

section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_idempotent_nilpotent_complement_of_perfect : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), ∃ e : G ⟶ G, e ≫ e = e ∧ (∀ (n : ℕ) (a : G.A n), IsNilpotent (a - e.app n a)) ∧ ∀ (n : ℕ) (a : G.A n), IsNilpotent (e.app n a) → e.app n a = 0 := by
  first | exact @GlobalTheory.PDivGroup.exists_perfect_idempotent | exact GlobalTheory.PDivGroup.exists_perfect_idempotent | (intros; apply GlobalTheory.PDivGroup.exists_perfect_idempotent <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    G.height ≤ Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) := by
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdimD : Module.finrank K (G.dual.A 1) = p ^ G.dual.height := by
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum K) := inferInstance
    have e := G.dual.rank_eq 1 q
    rw [Module.rankAtStalk_eq_finrank_of_free] at e
    simpa using e
  have hhD : G.dual.height = G.height := by simp
  have hord := finrank_eq_ker_mul_range K (G.dual.A 1) _ ((relFrob h G.dual).app 1)
  have hD : Module.finrank K (G.dual.A 1 ⧸ kerIdeal ((relFrob h G.dual).app 1)) ≤
      p ^ Module.finrank K (Cot K (G.dual.A 1)) := by
    rw [← GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius p K h G.dual 1]
    exact GlobalTheory.T.finrank_frobenius_kernel_hopf_le_pow_cotangent p K (G.dual.A 1)
  have hA : Module.finrank K (G.A 1 ⧸ kerIdeal ((relFrob h G).app 1)) ≤
      p ^ Module.finrank K (Cot K (G.A 1)) := by
    rw [← GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius p K h G 1]
    exact GlobalTheory.T.finrank_frobenius_kernel_hopf_le_pow_cotangent p K (G.A 1)
  have hker : (kerIdeal ((relFrob h G).app 1)).restrictScalars K ≤
      LinearMap.ker ((verschiebung h G).app 1 :
        G.A 1 →ₐ[K] (frobTwist h G).A 1).toLinearMap := fun a ha =>
    GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul p K G (frobTwist h G) (relFrob h G) (verschiebung h G)
      (verschiebung_comp_relFrob h G) a ha
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p K h G
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((relFrob h G).app 1)).restrictScalars K)
  rw [(Submodule.Quotient.restrictScalarsEquiv K (kerIdeal ((relFrob h G).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have hr : Module.finrank K (LinearMap.range ((relFrob h G.dual).app 1 :
        (frobTwist h G.dual).A 1 →ₐ[K] G.dual.A 1).toLinearMap) ≤
      p ^ Module.finrank K (Cot K (G.A 1)) := by omega
  have key : p ^ G.height ≤
      p ^ (Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1))) := by
    rw [pow_add, mul_comm, ← hhD, ← hdimD, hord]
    exact Nat.mul_le_mul hD hr
  exact (Nat.pow_le_pow_iff_right hp2).1 key
end
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.cartierDual_primePow_conv_pairing : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (n r : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n), (χ ^ p ^ r) (a ^ p ^ r) = χ (mulBy R (G.A n) (p ^ r) a) ^ p ^ r := by
  first | exact @GlobalTheory.Katz.cartier_primePow_pairing | exact GlobalTheory.Katz.cartier_primePow_pairing | (intros; apply GlobalTheory.Katz.cartier_primePow_pairing <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.finrank_fockJointHarmonics_highestWeight_of_shape : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), JointShape p q r s μ μ' → Module.finrank ℂ ↥(hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓ Submodule.span ℂ (jointHarm p q r s)) = 1 := by
  first | exact @GlobalTheory.JointHarm.finrank_joint_highest_of_shape | exact GlobalTheory.JointHarm.finrank_joint_highest_of_shape | (intros; apply GlobalTheory.JointHarm.finrank_joint_highest_of_shape <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fockHarmonic_homogeneous_of_KType : ∀ (p q r s : ℕ), (∀ (μ : Ix p q → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct1 p q r s) μ P → P ∈ harm1 p q r s → ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧ (∀ (μ : Ix r s → ℚ) (P : Pol p q r s), P ≠ 0 → OfType (fockAct2 p q r s) μ P → P ∈ harm2 p q r s → ∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ ∧ P ∈ homog (Ix p q × Ix r s) d) := by
  first | exact @GlobalTheory.FockAlg.harmonic_homog_of_type | exact GlobalTheory.FockAlg.harmonic_homog_of_type | (intros; apply GlobalTheory.FockAlg.harmonic_homog_of_type <;> assumption)
end

section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

theorem _root_.GlobalTheory.T.fockJointHarmonics_highestWeight_eq_bot_of_not_shape : ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), ¬ JointShape p q r s μ μ' → hwSub (fockAct1 p q r s) μ ⊓ hwSub (fockAct2 p q r s) μ' ⊓ Submodule.span ℂ (jointHarm p q r s) = ⊥ := by
  first | exact @GlobalTheory.FockAlg.jointHarm_hw_eq_bot | exact GlobalTheory.FockAlg.jointHarm_hw_eq_bot | (intros; apply GlobalTheory.FockAlg.jointHarm_hw_eq_bot <;> assumption)
end
