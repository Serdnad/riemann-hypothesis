module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle974
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle842
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle886
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormModerateGrowthCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle575
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.UnionHInv

variable {A : Type} [CommRing A] {ι : Type} [Preorder ι] (S : ι → Subalgebra ℤ A) (hS : Monotone S)

noncomputable def diag : ι ⥤ CommRingCat.{0} where
  obj i := CommRingCat.of (S i)
  map {i j} h := CommRingCat.ofHom (Subalgebra.inclusion (hS (leOfHom h))).toRingHom
  map_id i := by ext x; rfl
  map_comp f g := by ext x; rfl

noncomputable def cocone : Cocone (diag S hS) where
  pt := CommRingCat.of A
  ι := { app := fun i => CommRingCat.ofHom (S i).val.toRingHom
         naturality := fun i j h => by ext x; rfl }

theorem cocone_isColimit [IsDirected ι (· ≤ ·)] [Nonempty ι] (hcov : ∀ a, ∃ i, a ∈ S i) :
    Nonempty (IsColimit (cocone S hS)) := by
  haveI : ReflectsColimitsOfShape ι (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isColimitOfReflects (forget CommRingCat.{0}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro x
    change A at x
    obtain ⟨i, hi⟩ := hcov x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  · intro i j xi xj h
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    refine ⟨k, homOfLE hik, homOfLE hjk, ?_⟩
    apply Subtype.ext
    exact h

end GlobalTheory.UnionHInv


open GlobalTheory.UnionHInv in
theorem GlobalTheory.EtC.hInv_of_directed_union : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (S : ι → Subalgebra ℤ A), Monotone S → (∀ a, ∃ i, a ∈ S i) → (∀ i, IsUnit (q : S i)) → (∀ i, HInv q (S i)) → HInv q A := by
  intro q _ A _ ι _ _ _ S hS hcov hu hH
  obtain ⟨hc⟩ := cocone_isColimit S hS hcov
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_filtered_colimit q ι (diag S hS) (cocone S hS) hc hu hH
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup

theorem omegaLevel_bijective_of_pow_eq_zero : ∀ (p : ℕ)  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (G : PDivGroup p R) (n : ℕ), N ≤ n → Function.Bijective (G.omegaLevel n) := by
  intro p R _ N hN G n hn
  refine ⟨fun w w' h => ?_, G.omegaLevel_surjective n⟩
  rw [← sub_eq_zero]
  have h0 : (w - w').1 n = 0 := by
    simp only [omegaLevel_apply] at h
    change w.1 n - w'.1 n = 0
    rw [h, sub_self]
  obtain ⟨v, hv⟩ := (G.omega_val_eq_zero_iff n (w - w')).1 h0
  rw [hv, ← Nat.add_sub_cancel' hn, pow_add, hN, zero_mul, zero_smul]

end GlobalTheory.PDivGroup
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem exists_injective_mulBy_pow_eq_comp_resOne (n : ℕ) : ∃ q : G.A 1 →ₐc[R] G.A (n + 1),
    Function.Injective q ∧ ∀ a, mulBy R _ (p ^ n) a = q (G.resOne n a) := by
  induction n with
  | zero =>
    refine ⟨BialgHom.id R _, Function.injective_id, fun a => ?_⟩
    simp only [pow_zero, mulBy, pow_one, ofConv_toConv, BialgHom.coe_id, id_eq, resOne_zero]
  | succ n ih =>
    obtain ⟨q, hq, hq'⟩ := ih
    refine ⟨(G.mulP (n + 1)).comp q, (Test.mulP_injective G (n + 1)).comp hq, fun a => ?_⟩
    rw [pow_succ', ← mulBy_mulBy, ← mulP_res, map_mulBy, hq', BialgHom.comp_apply,
      resOne_succ]

theorem mulBy_pow_zero_eq_id (n : ℕ) : mulBy R (G.A n) (p ^ 0) = BialgHom.id R _ := by
  rw [pow_zero, mulBy, pow_one]

theorem exists_cob_eq_mulBy_eq (c : G.cocycles) (B : G.funs)
    (hB : ∀ n, cobOne R _ (B.1 n) = pullbackTwo (mulBy R (G.A n) p) (c.1 n)) (h1 : B.1 1 = 0) :
    ∃ e : G.funs, G.cob e = c ∧ ∀ n, mulBy R _ p (e.1 n) = B.1 n := by
  have hlev : ∀ n, cobOne R _ (B.1 (n + 1)) = pullbackTwo (G.mulP n) (c.1 n) := by
    intro n
    rw [hB, ← mulP_comp_res, pullTwo_comp, (c.2 n).2]
  have hinv : ∀ n, G.transl n (B.1 (n + 1)) = B.1 (n + 1) ⊗ₜ 1 := fun n =>
    G.transl_eq_of_cobOne_eq_pullTwo n _ _ (hlev n) (by rw [resOne_funs, h1])
  choose e he using fun n => G.exists_mulP_eq_of_transl_eq n (B.1 (n + 1)) (hinv n)
  have hres : ∀ n, G.res n (e (n + 1)) = e n := by
    intro n
    apply Test.mulP_injective G n
    rw [mulP_res, he n, ← B.2 (n + 1), ← he (n + 1), res_mulP]
  refine ⟨⟨e, hres⟩, Subtype.ext (funext fun n => ?_), fun n => ?_⟩
  · change cobOne R _ (e n) = c.1 n
    apply G.pullbackTwo_mulP_injective n
    rw [pullTwo_cobOne, he n, hlev n]
  · change mulBy R _ p (e n) = B.1 n
    rw [← res_mulP, he n, B.2 n]

theorem exists_cob_eq_mulBy_pow_eq [Fact p.Prime] (N : ℕ) : ∀ (c : G.cocycles) (B : G.funs),
    (∀ n, cobOne R _ (B.1 n) = pullbackTwo (mulBy R (G.A n) (p ^ N)) (c.1 n)) → B.1 N = 0 →
      ∃ e : G.funs, G.cob e = c ∧ ∀ n, mulBy R _ (p ^ N) (e.1 n) = B.1 n := by
  induction N with
  | zero =>
    intro c B hB _
    refine ⟨B, Subtype.ext (funext fun n => ?_), fun n => ?_⟩
    · change cobOne R _ (B.1 n) = c.1 n
      rw [hB n, mulBy_pow_zero_eq_id, pullTwo_id]
    · rw [mulBy_pow_zero_eq_id]
      rfl
  | succ N ih =>
    intro c B hB hN
    let c' : G.cocycles := cocyclesMap ((p : ℤ_[p]) • 𝟙 G) c
    have hc' : ∀ n, c'.1 n = pullbackTwo (mulBy R (G.A n) p) (c.1 n) := fun n => by
      change pullbackTwo (Hom.app ((p : ℤ_[p]) • 𝟙 G) n) (c.1 n) = _
      rw [natCast_smul_id_app]
    have hB' : ∀ n, cobOne R _ (B.1 n) = pullbackTwo (mulBy R (G.A n) (p ^ N)) (c'.1 n) := fun n => by
      rw [hB n, hc' n, ← pullTwo_comp, pow_succ,
        show (mulBy R (G.A n) (p ^ N)).comp (mulBy R _ p) = mulBy R _ (p ^ N * p) from
          BialgHom.ext fun a => mulBy_mulBy _ _ a]
    obtain ⟨e', he', hm'⟩ := ih c' B hB' ((B.2 N).symm.trans (by rw [hN, map_zero]))
    have h1 : e'.1 1 = 0 := by
      obtain ⟨q, hq, hq'⟩ := G.exists_injective_mulBy_pow_eq_comp_resOne N
      apply hq
      rw [map_zero, ← G.resOne_funs e' N, ← hq', hm', hN]
    have hA : ∀ n, cobOne R _ (e'.1 n) = pullbackTwo (mulBy R (G.A n) p) (c.1 n) := fun n =>
      (congrArg (fun d : G.cocycles => d.1 n) he').trans (hc' n)
    obtain ⟨e, he, hm⟩ := G.exists_cob_eq_mulBy_eq c e' hA h1
    refine ⟨e, he, fun n => ?_⟩
    rw [pow_succ, ← mulBy_mulBy, hm, hm']

end PDivGroup

theorem cocycle_mem_range_cob_of_pullback_mulBy_pow :
    ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (G : PDivGroup p R) (N : ℕ) (c : G.cocycles)
      (B : ∀ n, G.A n), (∀ n, G.res n (B (n + 1)) = B n) →
      (∀ n, cobOne R (G.A n) (B n) = pullbackTwo (mulBy R (G.A n) (p ^ N)) (c.1 n)) → B N = 0 →
        c ∈ LinearMap.range G.cob := by
  intro p _ R _ G N c B hB hc hN
  obtain ⟨e, he, -⟩ := G.exists_cob_eq_mulBy_pow_eq N c ⟨B, hB⟩ hc hN
  exact ⟨e, he⟩

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixUniq

theorem mat_unique : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c c' : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c' → c = c' := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A' B' _ _ φA' φB' Φ' c c' hT h₁ h₂
  obtain ⟨hAab, -, hL, hM, -, -, -, -, -, hbA, -⟩ := hH
  obtain ⟨ψA, ψB, α, hψA, hψB, hα, hrig, hmat⟩ := h₁
  obtain ⟨ψA₂, ψB₂, α₂, hψA₂, hψB₂, hα₂, hrig₂, hmat₂⟩ := h₂
  obtain rfl : ψA₂ = ψA := psi_unique _ _ (hψA₂.trans hψA.symm)
  obtain rfl : ψB₂ = ψB := psi_unique _ _ (hψB₂.trans hψB.symm)
  obtain ⟨v, hv⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.exists_ratio_gen
    (isoLB_cover (L := L) (M := M) hL hM k Φ' ψA₂ ψB₂) hα hα₂
  have v1 : v = 1 := GlobalTheory.T.normalised_isoPowerBundle_ratio_unit_eq_one Rg A B L M k eA eB hAab hL hM R t A' B' φA' φB' Φ' ψA₂ ψB₂ α α₂ v hT hψA hψB hv hrig hrig₂
  have hαe : ∀ p, α.s p = α₂.s p := fun p => by rw [hv p, v1, map_one, _root_.one_mul]
  funext i j
  have hd := GlobalTheory.T.pullback_sections_group_scheme Rg A L k mA bA hbA R t A' φA' ψA₂ hT.1 hψA₂ (fun i => c i j - c' i j) (fun jL x hx => by
    obtain ⟨iM, hiM⟩ : ∃ iM, ((((Φ'.left ≫ ψB₂) ≫ (snd (topS Rg) B).left)).base x) ∈ M.U iM :=
      TopologicalSpace.Opens.mem_iSup.1 (by rw [hM.cover]; trivial)
    refine ⟨(isoLB (L := L) (M := M) k Φ' ψA₂ ψB₂).U (fun _ => iM, jL), inf_le_right,
      ⟨Set.mem_iInter.2 fun _ => hiM, hx⟩, ?_⟩
    have e := (hmat j (fun _ => iM, jL)).symm.trans (hmat₂ j (fun _ => iM, jL))
    have e1 := congrArg Units.val (hαe (fun _ => iM, jL))
    erw [e1] at e
    have e2 := (α₂.s (fun _ => iM, jL)).isUnit.mul_left_cancel e
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 e2)
  exact sub_eq_zero.1 (congrFun hd i)

end GlobalTheory.HomFixUniq
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent

theorem _root_.GlobalTheory.T.finiteFlat_unitCocycle_locally_coboundary : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
    (V : Y.Opens) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
    (∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c) →
    ∀ y ∈ V, ∃ V' : Y.Opens, V' ≤ V ∧ y ∈ V' ∧ ∃ u : Γ(X, f ⁻¹ᵁ V')ˣ,
      ∀ z : ↥(pullback f f), f (pullback.fst f f z) ∈ V' →
        gm (pullback.fst f f) z _ u * gm (𝟙 _) z _ c = gm (pullback.snd f f) z _ u := by
  first | exact @GlobalTheory.LBDescent.coboundary_locally_of_cocycle | exact GlobalTheory.LBDescent.coboundary_locally_of_cocycle | (intros; apply GlobalTheory.LBDescent.coboundary_locally_of_cocycle <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.la_tor0_stdL_eq_blkLat : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ), TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D (n * 2)) (StandardLatticesGL3.stdL D (n' * 2)) = (blkLat (ι := Fin n' × Fin n) (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))).comap (phi B n n' : TaylorLogMetric.VC D (n * 2) (n' * 2) →ₗ[ℂ] (Ix D n n' → ℂ)).toAddMonoidHom := by
  first | exact @GlobalTheory.BaseVacuum.baseLattice_eq_comap_blockwise_lattice | exact GlobalTheory.BaseVacuum.baseLattice_eq_comap_blockwise_lattice | (intros; apply GlobalTheory.BaseVacuum.baseLattice_eq_comap_blockwise_lattice <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.blockVacuumCoordinateEquiv_isometry : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (z z' : TaylorLogMetric.VC D (n * 2) (n' * 2)), TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) z z' = stdH B.L (Ix D n n') (phi B n n' z) (phi B n n' z') := by
  first | exact @GlobalTheory.BaseVacuum.phi_isom | exact GlobalTheory.BaseVacuum.phi_isom | (intros; apply GlobalTheory.BaseVacuum.phi_isom <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.blockVacuum_latticeBasis_coordinate_eq_coordinateEquiv : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ) (j : Fin (TaylorLogMetric.fF D * (n * 2) * (n' * 2))) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), StandardLatticesGL3.coordB D (TaylorLogMetric.tor0 D cc δ) (bas B n n') j z = phi B n n' z (ixE D n n' j) := by
  first | exact @GlobalTheory.BaseVacuum.coordB_bas_eq_phi | exact GlobalTheory.BaseVacuum.coordB_bas_eq_phi | (intros; apply GlobalTheory.BaseVacuum.coordB_bas_eq_phi <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

theorem _root_.GlobalTheory.T.thetaVacuum_eq_kappa_pow_mul_block_kernels : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), B.StdOK → ∀ (n n' : ℕ) (z : TaylorLogMetric.VC D (n * 2) (n' * 2)), B.thZero (n * 2) (n' * 2) z = B.kappa ^ (n' * n) * ∏ k : Fin n' × Fin n, Formalism.L2.KerInert.kerB B (blk D k z) := by
  first | exact @GlobalTheory.BaseVacuum.thZero_eq_kappa_pow_mul_prod_kerB | exact GlobalTheory.BaseVacuum.thZero_eq_kappa_pow_mul_prod_kerB | (intros; apply GlobalTheory.BaseVacuum.thZero_eq_kappa_pow_mul_prod_kerB <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.eq_on_doubleCoset_of_eq_on_archimedeanSlice : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (V : Subgroup (GL (Fin (m + 1)) (Af E))) (q : GA E (m + 1)), q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → GeneralLinearGroup.map (pInf E) q = 1 → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ V, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ u ∈ V, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), p ∈ GlobalTheory.JSW.MirPatch.cell V q → W p = b p := by
  first | exact @GlobalTheory.JSW.MirPatch.eq_on_cell_of_eq_on_slice | exact GlobalTheory.JSW.MirPatch.eq_on_cell_of_eq_on_slice | (intros; apply GlobalTheory.JSW.MirPatch.eq_on_cell_of_eq_on_slice <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.archimedeanKernelSpan_cuspForm_right_invariant_open : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E a u) = F g := by
  first | exact @GlobalTheory.JSW.MirSemi.locSpan_openInv | exact GlobalTheory.JSW.MirSemi.locSpan_openInv | (intros; apply GlobalTheory.JSW.MirSemi.locSpan_openInv <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.cusp_form_moderate_growth_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, Continuous F ∧ ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E), ‖F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate | exact GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate | (intros; apply GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate <;> assumption)
end
