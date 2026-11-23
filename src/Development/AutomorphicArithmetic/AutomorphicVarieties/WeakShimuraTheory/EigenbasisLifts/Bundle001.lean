module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle004
public import Mathlib.RingTheory.Ideal.Height
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsAlgebraicPointOfGroupDeterminant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Bundle001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private def dblMat {K H : Type} [Field K] [TopologicalSpace K] [Group H] [TopologicalSpace H] {n : ℕ}
    (ρ : H →* GL (Fin n) K) (y : H → Matrix (Fin n) (Fin n) K)
    (hy : ∀ g h, y (g * h) = y g + Loc.adGL ρ g (y h)) : H →* Matrix (Fin (n + n)) (Fin (n + n)) K where
  toFun g := Matrix.reindexAlgEquiv K K finSumFinEquiv
    (Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K) (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K))
  map_one' := by
    have h1 : y 1 = 0 := by
      have := hy 1 1
      simpa using this
    simp only [map_one, Units.val_one, h1, Matrix.zero_mul, Matrix.fromBlocks_one]
  map_mul' g h := by
    rw [← map_mul, Matrix.fromBlocks_multiply, hy]
    congr 2
    · simp
    · simp only [Loc.adGL, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Units.val_mul,
        Matrix.add_mul, Matrix.mul_assoc, Units.inv_mul_cancel_left]
      exact add_comm _ _
    · simp
    · simp

theorem UpperTheory.V.Ws.Eb.dblRep :
    ∀ {K H : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {n : ℕ} (ρ : H →* GL (Fin n) K), Continuous ρ → ∀ y ∈ Z1 (Loc.adGL ρ),
        ∃ ρ₂ : H →* GL (Fin (n + n)) K, Continuous ρ₂ ∧ (∀ g, (W.mat ρ₂ g).charpoly = (W.mat ρ g).charpoly ^ 2) ∧ ∀ g, ρ₂ g = 1 → y g = 0 := by
  intro K H _ _ _ _ _ _ n ρ hρ y hy
  obtain ⟨hyc, hyco⟩ := hy
  let D := dblMat ρ y hyco
  have hρv : Continuous (fun g => (ρ g : Matrix (Fin n) (Fin n) K)) := Units.continuous_val.comp hρ
  have hblk : Continuous (fun g => Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K)
      (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K)) :=
    Continuous.matrix_fromBlocks hρv (hyc.matrix_mul hρv) continuous_const hρv
  have hDc : Continuous (fun g => D g) := by
    have e : (fun g => D g) = fun g => (Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K)
        (y g * (ρ g : Matrix (Fin n) (Fin n) K)) 0 (ρ g : Matrix (Fin n) (Fin n) K)).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm := by
      funext g
      rfl
    rw [e]
    exact hblk.matrix_submatrix _ _
  refine ⟨D.toHomUnits, ?_, ?_, ?_⟩
  · refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · exact hDc
    · have e : (fun g => ((D.toHomUnits g)⁻¹ : GL (Fin (n + n)) K).val) = fun g => D g⁻¹ := by
        funext g
        rw [← map_inv, MonoidHom.coe_toHomUnits]
      rw [e]
      exact hDc.comp continuous_inv
  · intro g
    show (D g).charpoly = ((ρ g : Matrix (Fin n) (Fin n) K)).charpoly ^ 2
    simp only [D, dblMat, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindexAlgEquiv_apply,
      Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁, pow_two]
  · intro g hg
    have h1 : D g = 1 := by
      rw [← MonoidHom.coe_toHomUnits D g, hg, Units.val_one]
    have h2 : Matrix.fromBlocks (ρ g : Matrix (Fin n) (Fin n) K) (y g * (ρ g : Matrix (Fin n) (Fin n) K))
        0 (ρ g : Matrix (Fin n) (Fin n) K) = Matrix.fromBlocks 1 0 0 1 := by
      rw [Matrix.fromBlocks_one]
      apply (Matrix.reindexAlgEquiv K K finSumFinEquiv).injective
      rw [map_one]
      exact h1
    obtain ⟨-, hB, -, -⟩ := Matrix.fromBlocks_inj.mp h2
    calc y g = y g * (ρ g : Matrix (Fin n) (Fin n) K) * ((ρ g)⁻¹ : GL (Fin n) K) := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      _ = 0 := by rw [hB, Matrix.zero_mul]
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem exists_coboundary_on_h_of_vanish_on_finiteIndex {K : Type*} [Field K] [CharZero K] {Γ : Type*} [Group Γ] {M : Type*}
    [AddCommGroup M] [Module K M] (R : Representation K Γ M) (z : Γ → M)
    (hco : ∀ g h, z (g * h) = z g + R g (z h)) (H N : Subgroup Γ) [N.FiniteIndex]
    (hN : ∀ g ∈ H, g ∈ N → z g = 0) :
    ∃ X, ∀ g ∈ H, z g = R g X - X := by
  classical
  have hQ : Finite (H ⧸ N.subgroupOf H) := inferInstance
  letI : Fintype (H ⧸ N.subgroupOf H) := Fintype.ofFinite _
  have hzout : ∀ (g : H) (q : H ⧸ N.subgroupOf H),
      z (((g • q).out : H) : Γ) = z g + R g (z ((q.out : H) : Γ)) := by
    intro g q
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (N.subgroupOf H) (g * q.out)
    have hq : g • q = (QuotientGroup.mk (g * q.out) : H ⧸ N.subgroupOf H) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hk]
    have hk0 : z ((k : H) : Γ) = 0 := hN _ (k : H).2 (Subgroup.mem_subgroupOf.mp k.2)
    simp only [Subgroup.coe_mul, hco, hk0, map_zero, add_zero]
  have hm : ((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨-(((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K)⁻¹ •
      ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)), fun g hg => ?_⟩
  have hsum : ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ) =
      ((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K) • z g +
        R g (∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)) := by
    calc ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)
        = ∑ q : H ⧸ N.subgroupOf H, z (((((⟨g, hg⟩ : H) • q)).out : H) : Γ) :=
          (Fintype.sum_equiv (MulAction.toPerm (⟨g, hg⟩ : H)) _ _ (fun q => rfl)).symm
      _ = ∑ q : H ⧸ N.subgroupOf H, (z g + R g (z ((q.out : H) : Γ))) :=
          Finset.sum_congr rfl (fun q _ => hzout ⟨g, hg⟩ q)
      _ = _ := by

          rw [Finset.sum_add_distrib, map_sum, Finset.sum_const, Finset.card_univ,
          Nat.cast_smul_eq_nsmul]
  have hR : R g (∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ)) =
      ∑ q : H ⧸ N.subgroupOf H, z ((q.out : H) : Γ) -
        ((Fintype.card (H ⧸ N.subgroupOf H) : ℕ) : K) • z g := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsum.symm
  rw [map_neg, map_smul, hR, smul_sub, smul_smul, inv_mul_cancel₀ hm, one_smul]
  abel

theorem UpperTheory.V.Ws.Eb.bkAw :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L]
      [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev),
      V.S' = s.S → ∀ {c : Coef l} {n : ℕ} (r : W.Resid (W.HidaSetting.Lev.frame V) c.O n)
      (R : Representation (PadicAlgCl l) (W.HidaSetting.Lev.frame V).Γ
        (Matrix (Fin n) (Fin n) (PadicAlgCl l))),
      ∀ z ∈ Z1 R, (∀ u, ∀ g ∈ r.Ip u, z g = 0) →
        (∀ g ∈ (W.HidaSetting.Lev.frame V).I0, z g = 0) →
        ∀ w : HeightOneSpectrum (𝓞 (W.Lp L)), ((l : ℕ) : 𝓞 (W.Lp L)) ∉ w.asIdeal →
          ∃ X, ∀ g ∈ Ine (F := W.Lp L) (s.A w),
            z (toGS Ω V.S' g) = R (toGS Ω V.S' g) X - X := by
  intro l _ L Ω _ _ _ _ _ _ s V hS c n r R z hz hIp hI0 w hw
  classical
  have hco : ∀ g h, z (g * h) = z g + R g (z h) := hz.2
  have hz1 : z 1 = 0 := by simpa using hco 1 1
  by_cases hwS : w ∈ V.S'
  swap
  · refine ⟨0, fun g hg => ?_⟩
    have hg1 : toGS Ω V.S' g = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.le_topologicalClosure _
        (Subgroup.subset_normalClosure
          (Set.mem_iUnion₂.mpr ⟨w, hwS, Set.mem_iUnion₂.mpr ⟨s.A w, s.hA w, hg⟩⟩)))
    rw [map_zero, sub_zero]
    exact (congrArg z hg1).trans hz1
  have hlift : ∀ g ∈ Ine (F := W.Lp L) (s.A w), ∃ h ∈ Ine (F := L) (s.A w),
      ((V.pr h : V.η.ker) : GS Ω V.S') = toGS Ω V.S' g := by
    intro g hg
    obtain ⟨h, rfl⟩ := s.unr (s.A w) w (s.hA w) hg
    exact ⟨h, hg, rfl⟩
  rw [hS] at hwS
  rcases hwS with hl | hSt | h0
  · exact absurd hl hw
  · let N : Subgroup V.frame.Γ := (⨅ i, (r.chib i).ker).map V.frame.η.ker.subtype
    let H : Subgroup V.frame.Γ := (V.frame.Iu ⟨w, hSt⟩).map V.frame.η.ker.subtype
    haveI : N.FiniteIndex := by
      have h1 : Finite (V.frame.G₀ ⧸ (⨅ i, (r.chib i).ker)) :=
        Subgroup.quotient_finite_of_isOpen' V.frame.η.ker _ V.frame.η_open (by
          rw [Subgroup.coe_iInf]
          exact isOpen_iInter_of_finite (fun i => r.chib_open i))
      have h2 : Finite (V.frame.Γ ⧸ V.frame.η.ker) :=
        Subgroup.quotient_finite_of_isOpen _ V.frame.η_open
      exact ⟨by
        rw [Subgroup.index_map_subtype]
        exact mul_ne_zero Subgroup.index_ne_zero_of_finite Subgroup.index_ne_zero_of_finite⟩
    have hN : ∀ g ∈ H, g ∈ N → z g = 0 := by
      intro g hgH hgN
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hgH
      obtain ⟨b, hb, hab⟩ := Subgroup.mem_map.mp hgN
      have hba : b = a := Subtype.ext hab
      subst hba
      exact hIp ⟨w, hSt⟩ b ⟨ha, hb⟩
    obtain ⟨X, hX⟩ := exists_coboundary_on_h_of_vanish_on_finiteIndex R z hco H N hN
    refine ⟨X, fun g hg => ?_⟩
    obtain ⟨h, hh, hgh⟩ := hlift g hg
    rw [← hgh]
    exact hX _ ⟨V.pr h, ⟨h, hh, rfl⟩, rfl⟩
  · subst h0
    refine ⟨0, fun g hg => ?_⟩
    obtain ⟨h, hh, hgh⟩ := hlift g hg
    rw [← hgh, map_zero, sub_zero]
    exact hI0 _ ⟨h, hh, rfl⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem im_small {l : ℕ} [hl : Fact l.Prime] (C : ℝ) : ∃ N : ℕ, ‖((l : PadicAlgCl l)) ^ N‖ * C ≤ 1 := by
  have h1 : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1).mul_const C
  rw [zero_mul] at h2
  obtain ⟨N, hN⟩ := (h2.eventually_le_const zero_lt_one).exists
  exact ⟨N, by rwa [norm_pow]⟩

private theorem im_model {l : ℕ} [hl : Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {n : ℕ}
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (c : Coef l) (hc : ∀ x, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1)
    (r : G →* GL (Fin n) (PadicAlgCl l)) (hr : ∀ i j, Continuous fun g => (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j)
    (hE : ∀ g i j, (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j ∈ E) :
    ∃ (Q : GL (Fin n) (PadicAlgCl l)) (r₀ : G →* GL (Fin n) c.O),
      ∀ g, r g * Q = Q * W.pushRep (algebraMap c.O (PadicAlgCl l)) r₀ g := by
  have hl0 : (l : PadicAlgCl l) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  letI : Algebra c.O E := (c.O.val.toRingHom.codRestrict E fun x => ((hc _).1 x.2).1).toAlgebra
  have ha : ∀ x : c.O, ((algebraMap c.O E x : E) : PadicAlgCl l) = x := fun _ => rfl
  haveI : FaithfulSMul c.O E := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
    Subtype.ext (congrArg (fun z : E => (z : PadicAlgCl l)) h)
  haveI : IsFractionRing c.O E := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    obtain ⟨N, hN⟩ := im_small (l := l) ‖(z : PadicAlgCl l)‖
    refine ⟨⟨(l : PadicAlgCl l) ^ N * z, (hc _).2 ⟨mul_mem (pow_mem (natCast_mem _ _) _) z.2, by rwa [norm_mul]⟩⟩,
      (l : c.O) ^ N, Subtype.ext ?_⟩
    push_cast
    rw [ha]
    field_simp
  let m : G →* Matrix (Fin n) (Fin n) E :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, hE g i j⟩
      map_one' := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.one_apply, h]
      map_mul' := fun g h => by
        ext i j
        simp [Matrix.mul_apply] }
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g i j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ ≤ C := by
    have h1 : Continuous fun g => ∑ i, ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖ :=
      continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hr i j).norm
    obtain ⟨C, hC⟩ := (isCompact_range h1).bddAbove
    refine ⟨C, fun g i j => le_trans ?_ (hC ⟨g, rfl⟩)⟩
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖)
      (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖(r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ j)
  obtain ⟨N, hN⟩ := im_small (l := l) C
  obtain ⟨Q, r₀, hQ⟩ := UpperTheory.V.Pa.Det.latInt (A := c.O) (F := E) m.toHomUnits ((l : c.O) ^ N)
    (pow_ne_zero _ fun h => hl0 (by simpa using congrArg Subtype.val h)) fun g i j => by
      refine ⟨⟨(l : PadicAlgCl l) ^ N * (r g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j, (hc _).2
        ⟨mul_mem (pow_mem (natCast_mem _ _) _) (hE g i j), ?_⟩⟩, Subtype.ext ?_⟩
      · rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (hC g i j) (norm_nonneg _)).trans hN
      · rw [ha]
        push_cast
        rfl
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl l)) Q, r₀, fun g => ?_⟩
  have h := congrArg (Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl l))) (hQ g)
  rw [map_mul, map_mul] at h
  convert h using 2 <;> (ext i j; rfl)

private theorem im_cont {l : ℕ} [hl : Fact l.Prime] {G : Type} [TopologicalSpace G]
    (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (c : Coef l) (hc : ∀ x, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1)
    (f : G → c.O) (hf : Continuous fun g => (f g : PadicAlgCl l)) (N : ℕ) :
    IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal c.O ^ N) (f g) := by
  obtain ⟨-, -, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  have hl0 : (l : PadicAlgCl l) ^ N ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have h1 : ∀ᶠ y in nhds x, ‖(f y : PadicAlgCl l) - f x‖ < ‖(l : PadicAlgCl l) ^ N‖ :=
    ((hf.sub continuous_const).norm.tendsto x).eventually_lt_const (by simpa using norm_pos_iff.2 hl0)
  filter_upwards [h1] with y hy
  rw [Ideal.Quotient.eq]
  have h2 : ((f y : PadicAlgCl l) - f x) / (l : PadicAlgCl l) ^ N ∈ c.O := (hc _).2
    ⟨div_mem (sub_mem ((hc _).1 (f y).2).1 ((hc _).1 (f x).2).1) (pow_mem (natCast_mem _ _) _), by
      rw [norm_div]
      exact div_le_one_of_le₀ hy.le (norm_nonneg _)⟩
  have h3 : f y - f x = (l : c.O) ^ N * ⟨_, h2⟩ := Subtype.ext (by push_cast; field_simp)
  rw [h3]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm N)

private theorem im_field {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x ∈ c.O, x ∈ E ∧ ‖x‖ ≤ 1 := by
  obtain ⟨s, hs⟩ : (Subalgebra.toSubmodule c.O).FG := Module.Finite.iff_fg.1 c.fin
  refine ⟨IntermediateField.adjoin ℚ_[l] (s : Set (PadicAlgCl l)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun x hx => ⟨?_, ?_⟩⟩
  · have hx' : x ∈ Submodule.span ℤ_[l] (s : Set (PadicAlgCl l)) := by rw [hs]; exact hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      rw [← algebraMap_smul ℚ_[l] a y]
      exact IntermediateField.smul_mem _ hy
  · have hi : IsIntegral ℤ_[l] x := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val
    have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
    rw [h0, spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral x))]
    intro n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _

theorem UpperTheory.V.Ws.Eb.intModel :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H] {n : ℕ} (ρ : H →* GL (Fin n) (PadicAlgCl l)), Continuous ρ →
        ∃ (c' : Coef l) (Q : GL (Fin n) (PadicAlgCl l)) (ρ₀ : H →* GL (Fin n) c'.O), c.O ≤ c'.O ∧ (∀ g, ρ g * Q = Q * W.pushRep (algebraMap c'.O (PadicAlgCl l)) ρ₀ g) ∧ ∀ i j, Alg.AdicCont (maximalIdeal c'.O) fun g => W.mat ρ₀ g i j := by
  intro l _ c H _ _ _ _ _ n ρ hρ
  have hr : ∀ i j, Continuous fun g => (ρ g : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j := fun i j =>
    (Units.continuous_val.comp hρ).matrix_elem i j
  obtain ⟨E₁, f₁, m₁⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l H n ρ hr
  obtain ⟨E₂, f₂, m₂⟩ := im_field c
  obtain ⟨c', hc⟩ := UpperTheory.V.X.So.coefOf l (E₁ ⊔ E₂)
  obtain ⟨Q, r₀, hQ⟩ := im_model (E₁ ⊔ E₂) c' hc ρ hr fun g i j => (le_sup_left : E₁ ≤ _) (m₁ g i j)
  have hQ' : ∀ g, W.pushRep (algebraMap c'.O (PadicAlgCl l)) r₀ g = Q⁻¹ * ρ g * Q := fun g => by
    rw [mul_assoc, hQ, inv_mul_cancel_left]
  refine ⟨c', Q, r₀, fun x hx => (hc x).2 ⟨(le_sup_right : E₂ ≤ _) (m₂ x hx).1, (m₂ x hx).2⟩, hQ, fun i j N => ?_⟩
  refine im_cont (E₁ ⊔ E₂) c' hc _ ?_ N
  have e : (fun g => ((W.mat r₀ g i j : c'.O) : PadicAlgCl l)) =
      fun g => ((Q⁻¹ * ρ g * Q : GL (Fin n) (PadicAlgCl l)) : Matrix (Fin n) (Fin n) (PadicAlgCl l)) i j := by
    funext g
    rw [← hQ']
    rfl
  rw [e]
  exact (Units.continuous_val.comp ((continuous_const.mul hρ).mul continuous_const)).matrix_elem i j
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem dim_le_of_int (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] :
    ringKrullDim A ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) fun _ _ h =>
    Ideal.IsIntegral.comap_lt_comap (R := R) h

theorem UpperTheory.V.Ws.Eb.htLow :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (T : Type) [CommRing T] [IsDomain T] [Algebra c.O T] [IsCO c.O T] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] T), Function.Injective f → (f : MvPowerSeries (Fin N) c.O →+* T).Finite → ∀ x : T →ₐ[c.O] PadicAlgCl l, (N : ℕ∞) ≤ (RingHom.ker x).height := by
  intro l _ c N T _ _ _ _ f hinj hfin x
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l])).2 inferInstance
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ_[l]) (UpperTheory.V.Base.dvrFacts l c.O).1
  haveI : FaithfulSMul c.O (PadicAlgCl l) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI := UpperTheory.V.W.exists_algebraicPoint_of_groupDeterminant c.O T (PadicAlgCl l) x
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  have h1 := UpperTheory.V.Alg.co_caten c.O T (RingHom.ker x)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have h2 := (UpperTheory.V.AlgebraTools.mvPowerSeries_cotInd c.O ϖ hϖ (Fin N)).2.1
  have h3 : ringKrullDim T = ringKrullDim (MvPowerSeries (Fin N) c.O) := by
    letI : Algebra (MvPowerSeries (Fin N) c.O) T := (f : MvPowerSeries (Fin N) c.O →+* T).toAlgebra
    haveI : Module.Finite (MvPowerSeries (Fin N) c.O) T := hfin
    exact ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj
  have h4 : ringKrullDim (T ⧸ RingHom.ker x) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange x).toRingEquiv,
      ← IsDiscreteValuationRing.ringKrullDim_eq_one c.O]
    exact dim_le_of_int c.O x.range
  rw [h3, h2, Fintype.card_fin] at h1
  have h5 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ ((RingHom.ker x).height : WithBot ℕ∞) + 1 := by
    rw [← h1]; exact add_le_add le_rfl h4
  have h6 : (N : ℕ∞) + 1 ≤ (RingHom.ker x).height + 1 := by exact_mod_cast h5
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h6
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem pushCh_comp_alg {H O A B C : Type} [Group H] [CommRing O] [CommRing A] [CommRing B] [CommRing C]
    [Algebra O A] [Algebra O B] [Algebra O C] (f : A →ₐ[O] B) (g : B →ₐ[O] C) (χ : H →* Aˣ) :
    W.pushCh ((g.comp f : A →ₐ[O] C) : A →+* C) χ = W.pushCh (g : B →+* C) (W.pushCh (f : A →+* B) χ) := by
  ext s
  rfl

private theorem pushCh_id_alg {H O A : Type} [Group H] [CommRing O] [CommRing A] [Algebra O A] (χ : H →* Aˣ) :
    W.pushCh ((AlgHom.id O A : A →ₐ[O] A) : A →+* A) χ = χ := by
  ext s
  rfl

theorem UpperTheory.V.Ws.Eb.lamIso :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : W.Resid F O n} (Λ Λ' : W.LamObj r), Nonempty (Λ.Λ ≃ₐ[O] Λ'.Λ) := by
  intro l _ F O _ _ _ n r Λ Λ'
  obtain ⟨f, hf, -⟩ := Λ.univ Λ'.Λ Λ'.κ Λ'.inert
  obtain ⟨g, hg, -⟩ := Λ'.univ Λ.Λ Λ.κ Λ.inert
  refine ⟨AlgEquiv.ofAlgHom f g ?_ ?_⟩
  · exact (Λ'.univ Λ'.Λ Λ'.κ Λ'.inert).unique
      (fun v i => by rw [pushCh_comp_alg, hg, hf]) (fun v i => pushCh_id_alg _)
  · exact (Λ.univ Λ.Λ Λ.κ Λ.inert).unique
      (fun v i => by rw [pushCh_comp_alg, hf, hg]) (fun v i => pushCh_id_alg _)
end
