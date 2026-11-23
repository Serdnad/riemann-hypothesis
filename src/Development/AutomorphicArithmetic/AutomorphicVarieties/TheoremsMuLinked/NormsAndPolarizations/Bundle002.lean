module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SelfTwistEigenvalues.Bundle001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle026
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem inc_local {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) : IsLocalHom (inc h) := by
  have hint : (inc h).IsIntegral := by
    have h0 : (algebraMap ℤ_[l] c'.O).IsIntegral := fun x => Algebra.IsIntegral.isIntegral x
    have e : (inc h).comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c'.O := by
      ext a; rfl
    rw [← e] at h0
    exact RingHom.IsIntegral.tower_top _ _ h0
  exact RingHom.IsIntegral.isLocalHom hint (Subalgebra.inclusion_injective h)

private theorem pushCh_ker {H A B : Type} [Group H] [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Injective f)
    (χ : H →* Aˣ) : (pushCh f χ).ker = χ.ker := by
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro hg
    apply Units.ext
    apply hf
    have := congrArg Units.val hg
    simpa using this
  · intro hg
    rw [hg, map_one]

private theorem polar_push {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) {O O' k k' : Type} [CommRing O] [CommRing O']
    [CommRing k] [CommRing k'] [Algebra ℤ_[l] O] [Algebra ℤ_[l] O'] [Algebra O k] [Algebra O' k']
    (i : O →+* O') (f : k →+* k') (hi : ∀ a, i (algebraMap ℤ_[l] O a) = algebraMap ℤ_[l] O' a)
    (hf : ∀ a, f (algebraMap O k a) = algebraMap O' k' (i a)) (χ : Fin n → F.G₀ →* kˣ)
    (hp : F.IsPolar O (GDet.ofRep (diagRep χ))) :
    F.IsPolar O' (GDet.ofRep (diagRep fun j => pushCh f (χ j))) := by
  intro B _ _ _ _ y
  letI : Algebra k B := ((algebraMap k' B).comp f).toAlgebra
  letI : Algebra O B := ((algebraMap O' B).comp i).toAlgebra
  haveI : IsScalarTower O k B := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap O' B (i a) = algebraMap k' B (f (algebraMap O k a))
    rw [hf, ← IsScalarTower.algebraMap_apply]
  have he : F.eps O' B = F.eps O B := by
    unfold GFrame.eps
    congr 1
    ext a
    change algebraMap O' B (algebraMap ℤ_[l] O' a) = algebraMap O' B (i (algebraMap ℤ_[l] O a))
    rw [hi]
  have hs : F.star O' B n y = F.star O B n y := by
    unfold GFrame.star GFrame.starOp
    simp only [he]
  have hr : GDet.repAlg (diagRep fun j => pushCh f (χ j)) B = GDet.repAlg (diagRep χ) B := by
    unfold GDet.repAlg
    congr 1
    ext g a b
    by_cases hab : a = b
    · subst hab
      simp [diagRep]
      rfl
    · simp [diagRep, hab]
  have := hp B y
  change (GDet.repAlg (diagRep χ) B _).det = (GDet.repAlg (diagRep χ) B _).det at this
  change (GDet.repAlg (diagRep fun j => pushCh f (χ j)) B _).det = (GDet.repAlg (diagRep fun j => pushCh f (χ j)) B _).det
  rw [hr, hs]
  exact this

theorem UpperTheory.V.Th.Nm.residPush :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c c' : Coef l) (h : c.O ≤ c'.O) (r : Resid F c.O n), ∃ r' : Resid F c'.O n, RPush h r r' ∧ (∀ u, r'.Ip u = r.Ip u) ∧ (r.V0ok → r'.V0ok) := by
  intro l _ n F c c' h r
  haveI := inc_local h
  let f : ResidueField c.O →+* ResidueField c'.O := ResidueField.map (inc h)
  have hfi : Function.Injective f := f.injective
  have hf : ∀ a, f (residue c.O a) = residue c'.O (inc h a) := fun a => ResidueField.map_residue _ a
  refine ⟨{ chib := fun i => pushCh f (r.chib i)
            chib_open := fun i => by rw [pushCh_ker f hfi]; exact r.chib_open i
            chib_inj := fun i j hij => r.chib_inj ?_
            polar := polar_push F (inc h) f (fun _ => rfl) hf r.chib r.polar
            psib := fun v i => pushCh f (r.psib v i)
            psib_open := fun v i => by rw [pushCh_ker f hfi]; exact r.psib_open v i
            th := fun v i => pushCh (inc h) (r.th v i)
            th_comm := fun v i g hg => by
              rw [MonoidHom.comp_apply, r.th_comm v i g hg, map_one] },
    ⟨f, hf, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, fun u => ?_, fun hv => ⟨fun i => ?_, fun g hg i j => ?_, ?_⟩⟩
  · ext g
    apply hfi
    have := congrArg Units.val (DFunLike.congr_fun hij g)
    simpa using this
  · simp only [Resid.Ip, pushCh_ker f hfi]
  · rw [pushCh_ker f hfi]; exact hv.1 i
  · change Units.map _ (r.chib i g) = Units.map _ (r.chib j g)
    rw [hv.2.1 g hg i j]
  · obtain ⟨g, hg, hne⟩ := hv.2.2
    refine ⟨g, hg, fun e => hne ?_⟩
    apply Units.ext
    apply hfi
    have := congrArg Units.val e
    rw [Units.val_one, map_one]
    exact (hf _).trans this
end

section

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Th.Nm.roots_norm_le {l : ℕ} [Fact l.Prime] {n : ℕ}
    (Z : Matrix (Fin n) (Fin n) (Qbar l)) (hZ : IntM Z) (a : Qbar l) (ha : Z.charpoly.IsRoot a) :
    ‖a‖ ≤ 1 := by
  classical
  have hdet : (Matrix.scalar (Fin n) a - Z).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact ha
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra hc
    apply hv0
    funext j
    exact absurd ⟨j, Finset.mem_univ j⟩ hc
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖v j‖) hne
  have hvi : v i ≠ 0 := by
    intro h0
    apply hv0
    funext j
    have hj := hi j (Finset.mem_univ j)
    rw [h0, norm_zero] at hj
    exact norm_le_zero_iff.1 hj
  have heq : a * v i = ∑ j, Z i j * v j := by
    have hvi' := congrFun hv i
    simp only [Matrix.sub_mulVec, Pi.sub_apply, Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.zero_apply,
      sub_eq_zero] at hvi'
    rw [hvi']
    rfl
  have hle : ‖a‖ * ‖v i‖ ≤ 1 * ‖v i‖ := by
    rw [← norm_mul, heq, one_mul]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro j _
    rw [norm_mul]
    exact (mul_le_mul (hZ i j) (hi j (Finset.mem_univ j)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  exact le_of_mul_le_mul_right hle (norm_pos_iff.2 hvi)

theorem UpperTheory.V.Th.Nm.roots :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (Z : Matrix (Fin n) (Fin n) (Qbar l)), IntM Z → Z.charpoly.Separable → ∃ al : Fin n → Qbar l, Function.Injective al ∧ (∀ i, ‖al i‖ ≤ 1) ∧ Z.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) := by
  intro l _ n Z hZ hsep
  classical
  set p := Z.charpoly with hp
  set s := p.roots.toFinset with hs
  have hnd : p.roots.Nodup := Polynomial.nodup_roots hsep
  have hval : s.val = p.roots := by
    rw [hs, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd]
  have hcard : s.card = n := by
    rw [← Finset.card_val, hval, IsAlgClosed.card_roots_eq_natDegree, hp, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  let e : Fin n ≃ s := (finCongr hcard.symm).trans s.equivFin.symm
  refine ⟨fun i => (e i : Qbar l), ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    have hmem : (e i : Qbar l) ∈ p.roots := by
      rw [← hval]
      exact (e i).2
    exact roots_norm_le Z hZ _ (Polynomial.isRoot_of_mem_roots hmem)
  · rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic (Matrix.charpoly_monic Z), ← hval,
      ← Finset.prod_eq_multiset_prod, ← Finset.prod_coe_sort s]
    exact (Equiv.prod_comp e (fun x : s => Polynomial.X - Polynomial.C (x : Qbar l))).symm
end

section

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem ri_small {l : ℕ} [hl : Fact l.Prime] (C : ℝ) : ∃ N : ℕ, ‖((l : PadicAlgCl l)) ^ N‖ * C ≤ 1 := by
  have h1 : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h1).mul_const C
  rw [zero_mul] at h2
  obtain ⟨N, hN⟩ := (h2.eventually_le_const zero_lt_one).exists
  exact ⟨N, by rwa [norm_pow]⟩

private theorem ri_entries {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] {m : ℕ} (s : G →* Matrix (Fin m) (Fin m) (PadicAlgCl l))
    (z : G → Matrix (Fin m) (Fin m) (PadicAlgCl l))
    (hs : Continuous s) (hz : Continuous z) (hc : ∀ g h, z (g * h) = z g + s g * z h * s g⁻¹) :
    ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ (∀ g i j, s g i j ∈ E) ∧
      ∀ g i j, z g i j ∈ E := by
  have h1 : z 1 = 0 := by
    have h := hc 1 1
    rw [mul_one, inv_one, map_one, Matrix.one_mul, Matrix.mul_one] at h
    exact left_eq_add.1 h
  let b : G →* Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (PadicAlgCl l) :=
    { toFun := fun g => Matrix.fromBlocks (s g) (z g * s g) 0 (s g)
      map_one' := by
        rw [map_one, h1, Matrix.zero_mul, Matrix.fromBlocks_one]
      map_mul' := fun g h => by
        have e : s g⁻¹ * (s g * s h) = s h := by rw [← map_mul, ← map_mul, inv_mul_cancel_left]
        rw [Matrix.fromBlocks_multiply, map_mul, hc]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.add_mul, Matrix.mul_assoc, e]
        rw [add_comm] }
  have hb : Continuous b :=
    Continuous.matrix_fromBlocks hs (hz.matrix_mul hs) continuous_const hs
  let r : G →* Matrix (Fin (m + m)) (Fin (m + m)) (PadicAlgCl l) :=
    (Matrix.reindexAlgEquiv (PadicAlgCl l) (PadicAlgCl l) finSumFinEquiv).toRingEquiv.toMonoidHom.comp b
  have hr : ∀ g i j, r g i j = b g (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) := fun _ _ _ => rfl
  obtain ⟨E, fE, mE⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l G (m + m) r.toHomUnits
    fun i j => hb.matrix_elem (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  have hA : ∀ g i j, s g i j ∈ E := fun g i j => by
    have h : r g (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ∈ E := mE g _ _
    rw [hr, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
    exact h
  have hB : ∀ g i j, (z g * s g) i j ∈ E := fun g i j => by
    have h : r g (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) ∈ E := mE g _ _
    rw [hr, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h
    exact h
  refine ⟨E, fE, hA, fun g i j => ?_⟩
  have e : z g = z g * s g * s g⁻¹ := by
    rw [Matrix.mul_assoc, ← map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  rw [e, Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hB g i k) (hA _ k j)

theorem UpperTheory.V.Th.Nm.repIn :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)), Continuous ρ → (∀ g, IntM (mat ρ g)) → Continuous z → (∀ g g', z (g * g') = z g + mat ρ g * z g' * mat ρ g⁻¹) → ∃ (c' : Coef l) (a : Qbar l), c.O ≤ c'.O ∧ a ≠ 0 ∧ (∀ g, InO c' (mat ρ g)) ∧ ∀ g, InO c' (a • z g) := by
  intro l hl n F c ρ z hρ hi hz hc
  haveI : CompactSpace F.G₀ := isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  haveI : T2Space F.G₀ := inferInstance
  obtain ⟨E, fE, m₁, m₂⟩ := ri_entries (l := l) ((Units.coeHom _).comp ρ) z (Units.continuous_val.comp hρ) hz hc
  obtain ⟨d, hd⟩ := UpperTheory.V.X.So.coefOf l E
  obtain ⟨c', h1, h2⟩ := (UpperTheory.V.HV.coefSup l).1 c d
  have hn : Continuous fun g => ∑ i, ∑ j, ‖z g i j‖ :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hz.matrix_elem i j).norm
  obtain ⟨C, hC⟩ := (isCompact_range hn).bddAbove
  obtain ⟨N, hN⟩ := ri_small (l := l) C
  refine ⟨c', (l : PadicAlgCl l) ^ N, h1, pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero),
    fun g i j => h2 ((hd _).2 ⟨m₁ g i j, hi g i j⟩), fun g i j => h2 ((hd _).2 ⟨?_, ?_⟩)⟩
  · rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (pow_mem (natCast_mem _ _) _) (m₂ g i j)
  · rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
    have hb : ‖z g i j‖ ≤ C :=
      ((Finset.single_le_sum (f := fun j => ‖z g i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i => ∑ j, ‖z g i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))).trans (hC ⟨g, rfl⟩)
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans hN
end

section

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

theorem UpperTheory.V.Th.Nm.conjAll :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P Q P' : GL (Fin n) (Qbar l)), (P' : Matrix (Fin n) (Fin n) (Qbar l)) = (Q : Matrix (Fin n) (Fin n) (Qbar l))ᵀ * P * Q → (Continuous ρ → Continuous (cj Q ρ)) ∧ (Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → Submodule.span (Qbar l) (Set.range (mat (cj Q ρ))) = ⊤) ∧ (F.IsForm c.O n ρ P → F.IsForm c.O n (cj Q ρ) P') ∧ GDet.ofRep (mat (cj Q ρ)) = GDet.ofRep (mat ρ) ∧ (∀ g, (mat (cj Q ρ) g).charpoly = (mat ρ g).charpoly) ∧ (∀ S, DetQ F c.O ρ P S → DetQ F c.O (cj Q ρ) P' S) ∧ ∀ I ψ z, IsOrdCoc F ρ P I ψ z → IsOrdCoc F (cj Q ρ) P' I ψ fun g => ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * z g * Q := by
  intro l _ n F c ρ P Q P' hP
  have hm : ∀ g, mat (cj Q ρ) g = ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * mat ρ g * Q := by
    intro g
    change ((cj Q ρ g : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = _
    rw [cj_apply, Units.val_mul, Units.val_mul]; rfl
  have hch : ∀ g, (mat (cj Q ρ) g).charpoly = (mat ρ g).charpoly := by
    intro g
    have := Matrix.charpoly_units_conj Q⁻¹ (mat ρ g)
    rw [hm, ← this, ← Matrix.coe_units_inv, inv_inv]
  have hinv : ∀ w : GL (Fin n) (Qbar l), (((Q⁻¹ * w)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * Q := by
    intro w; rw [_root_.mul_inv_rev, inv_inv, Units.val_mul]
  have hmul : ∀ w : GL (Fin n) (Qbar l), ((Q⁻¹ * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * w := fun w => Units.val_mul _ _
  have hD : GDet.ofRep (mat (cj Q ρ)) = GDet.ofRep (mat ρ) :=
    (UpperTheory.V.AlgebraTools.Det.repApi (mat ρ)).2.2.2.2.2.2.2 _ Q fun g => by
      rw [hm, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  have h1 : (Q : Matrix (Fin n) (Fin n) (Qbar l)) * ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = 1 :=
    Units.mul_inv Q
  have h2 : ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * (Q : Matrix (Fin n) (Fin n) (Qbar l)) = 1 :=
    Units.inv_mul Q
  generalize hqi : ((Q⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) = qi at *
  generalize hq : (Q : Matrix (Fin n) (Fin n) (Qbar l)) = q at *
  have a1 : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), q * (qi * X) = X := fun X => by rw [← mul_assoc, h1, one_mul]
  have a2 : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), qi * (q * X) = X := fun X => by rw [← mul_assoc, h2, one_mul]
  have t1 : ∀ X : Matrix (Fin n) (Fin n) (Qbar l), qiᵀ * (qᵀ * X) = X := fun X => by
    rw [← mul_assoc, ← transpose_mul, h1, transpose_one, one_mul]
  refine ⟨fun h => ?_, fun h => ?_, fun h g => ?_, hD, hch, fun S h z hz hc hp ht => ?_, fun I ψ z h => ?_⟩
  · have : (cj Q ρ : F.G₀ → _) = fun g => Q⁻¹ * ρ g * Q := funext (cj_apply Q ρ)
    rw [this]
    exact (continuous_const.mul h).mul continuous_const
  · have key : ∀ Z ∈ Submodule.span (Qbar l) (Set.range (mat ρ)),
        qi * Z * q ∈ Submodule.span (Qbar l) (Set.range (mat (cj Q ρ))) := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem x hx => obtain ⟨g, rfl⟩ := hx; exact Submodule.subset_span ⟨g, hm g⟩
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
      | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
    refine eq_top_iff.2 fun Z _ => ?_
    have := key (q * Z * qi) (h ▸ Submodule.mem_top)
    simpa only [mul_assoc, a2, h2, mul_one] using this
  · have := congrArg (fun X => qᵀ * X * q) (h g)
    simp only [mul_smul_comm, smul_mul_assoc] at this
    rw [hm, hm, hP, ← this]
    simp only [transpose_mul, mul_assoc, a1, t1]
  · obtain ⟨Y, hY⟩ := h (fun g => q * z g * qi) ((continuous_const.mul hz).mul continuous_const)
      (fun g g' => by
        simp only [hc g g', hm, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, a1, h1, mul_one])
      (fun g => by
        have := congrArg (fun X => qiᵀ * X * qi) (hp g)
        simpa only [hP, transpose_mul, mul_assoc, t1, h1, mul_one] using this)
      (fun σ hσ k => by
        have := ht σ hσ k
        rw [← map_pow, hm, map_pow, ← mul_assoc, trace_mul_comm] at this
        simpa only [mul_assoc] using this)
    refine ⟨qi * Y * q, fun g => ?_⟩
    have := congrArg (fun X => qi * X * q) (hY g)
    simpa only [hm, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, a1, a2, h2, mul_one] using this
  · refine ⟨(continuous_const.mul h.cont).mul continuous_const, fun g g' => ?_, fun g => ?_, fun u g hg => ?_, fun v => ?_⟩
    · simp only [h.coc g g', hm, mul_add, add_mul, mul_assoc, a1]
    · have := congrArg (fun X => qᵀ * X * q) (h.pol g)
      simpa only [hP, transpose_mul, mul_assoc, t1, a1, mul_neg, neg_mul] using this
    · simp [h.ine u g hg]
    · obtain ⟨w, Y, hw⟩ := h.ord v
      refine ⟨Q⁻¹ * w, qi * Y * q, fun g => ?_⟩
      have e1 : (Q⁻¹ * w)⁻¹ * cj Q ρ (F.φ v g) * (Q⁻¹ * w) = w⁻¹ * ρ (F.φ v g) * w := by
        rw [cj_apply]; group
      have e2 : (((Q⁻¹ * w)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
          (qi * z (F.φ v g) * q - dY F (mat (cj Q ρ)) (qi * Y * q) (F.φ v g)) *
          ((Q⁻¹ * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
          ((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
          (z (F.φ v g) - dY F (mat ρ) Y (F.φ v g)) * (w : Matrix (Fin n) (Fin n) (Qbar l)) := by
        simp only [hinv, hmul, dY, hm, mul_sub, sub_mul, mul_assoc, a1]
      rw [e1, e2]
      exact hw g
end

section

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem ordInt_diag {K : Type} [Field K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hA (show id j < id i from h), zero_mul]
    · rw [hB (show id i < id j from h), mul_zero]
  · simp

private theorem ordInt_conj {K : Type} [Field K] {n : ℕ} (b : GL (Fin n) K) {M : Matrix (Fin n) (Fin n) K}
    (hb : (b : Matrix (Fin n) (Fin n) K).BlockTriangular id) (hM : M.BlockTriangular id) :
    ((b : Matrix (Fin n) (Fin n) K) * M * ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).BlockTriangular id ∧
      ∀ i, ((b : Matrix (Fin n) (Fin n) K) * M * ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) i i = M i i := by
  have hi : ((b⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    letI := b.invertible
    exact Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨(hb.mul hM).mul hi, fun i => ?_⟩
  have h1 := ordInt_diag hb hi i
  rw [Units.mul_inv, Matrix.one_apply_eq] at h1
  rw [ordInt_diag (hb.mul hM) hi, ordInt_diag hb hM, mul_right_comm, ← h1, one_mul]

private def ordInt_V (l : ℕ) [Fact l.Prime] : ValuationSubring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : Qbar l)‖ ≤ 1; simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : Qbar l)‖ ≤ 1; simp
  neg_mem' := fun {a} ha => by show ‖-a‖ ≤ 1; rwa [norm_neg]
  mem_or_inv_mem' := fun a => by
    rcases le_total ‖a‖ 1 with h | h
    · exact Or.inl h
    · right
      show ‖a⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ h

theorem UpperTheory.V.Th.Nm.ordInt :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (v : F.Vl) (ψ : Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (w : GL (Fin n) (Qbar l)) (Y : Matrix (Fin n) (Fin n) (Qbar l)), OrdAt F ρ v ψ z w Y → ∃ w' : GL (Fin n) (Qbar l), IntM (w' : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((w'⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ OrdAt F ρ v ψ z w' Y := by
  intro l _ n F ρ v ψ z w Y h
  obtain ⟨k, hk⟩ := UpperTheory.V.Pr.T.iwasawaVal (ordInt_V l) n (w : Matrix (Fin n) (Fin n) (Qbar l))
  let k' : GL (Fin n) (Qbar l) := GeneralLinearGroup.map (ordInt_V l).subtype k
  have hb : ((k' * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).BlockTriangular id := hk
  refine ⟨k'⁻¹, fun i j => ?_, fun i j => ?_, fun g => ?_⟩
  · have : k'⁻¹ = GeneralLinearGroup.map (ordInt_V l).subtype k⁻¹ := (map_inv _ _).symm
    rw [this]
    exact ((k⁻¹ : GL (Fin n) (ordInt_V l)) i j).2
  · rw [inv_inv]
    exact (k i j).2
  · obtain ⟨h1, h2, h3, h4⟩ := h g
    have e : ∀ M : Matrix (Fin n) (Fin n) (Qbar l),
        ((k'⁻¹⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * M * (k'⁻¹ : GL (Fin n) (Qbar l)) =
        ((k' * w : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) *
          (((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * M * (w : Matrix (Fin n) (Fin n) (Qbar l))) *
          (((k' * w)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
      intro M
      rw [inv_inv, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
      simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
    have c1 := ordInt_conj (k' * w) hb
      (M := ((w⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * (ρ (F.φ v g) : Matrix (Fin n) (Fin n) (Qbar l)) *
        (w : Matrix (Fin n) (Fin n) (Qbar l))) (fun i j hij => h1 i j hij)
    have c2 := ordInt_conj (k' * w) hb (fun i j hij => h3 i j hij)
    rw [← e] at c1 c2
    refine ⟨fun i j hij => c1.1 hij, fun i => (c1.2 i).trans (h2 i), fun i j hij => c2.1 hij,
      fun hg i => (c2.2 i).trans (h4 hg i)⟩
end

section

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Th.Nm.smith_gen {K : Type*} [NormedField K] [IsUltrametricDist K] {n : ℕ}
    (P : GL (Fin n) K) : ∃ (U V : GL (Fin n) K) (d : Fin n → K),
      (∀ i j, ‖(U : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖((U⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖(V : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i j, ‖((V⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j‖ ≤ 1) ∧
      (∀ i, d i ≠ 0) ∧ (P : Matrix (Fin n) (Fin n) K) = U * diagonal d * V :=
  _root_.UpperTheory.Reformulated.B.StringRepresentationDecomposition.smith_gen P

theorem UpperTheory.V.Th.Nm.smith :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (P : GL (Fin n) (Qbar l)), ∃ (U V : GL (Fin n) (Qbar l)) (d : Fin n → Qbar l), IntM (U : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((U⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM (V : Matrix (Fin n) (Fin n) (Qbar l)) ∧ IntM ((V⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) ∧ (∀ i, d i ≠ 0) ∧ (P : Matrix (Fin n) (Fin n) (Qbar l)) = U * diagonal d * V := by
  intro l _ n P
  exact smith_gen P
end
