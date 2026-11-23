module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle016
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle062
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

local instance (priority := 2000) ratFieldIsTorsionFreeForSymplecticGSp4Bundle017 (Ω : Type) [Field Ω] [Algebra ℚ Ω] :
    Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem lev_basis {ι k : Type} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ} (X : ι → Matrix (Fin n) (Fin n) k)
    (hc : ∀ a b, Commute (X a) (X b)) (hf : ∀ a, IsOfFinOrder (X a)) :
    ∃ (P : GL (Fin n) k) (d : ι → Fin n → k), ∀ a, X a * P = P * Matrix.diagonal (d a) := by
  classical
  let f : ι → Module.End k (Fin n → k) := fun a => Matrix.toLinAlgEquiv' (X a)
  have hss : ∀ a, (f a).IsFinitelySemisimple := fun a => by
    obtain ⟨m, hm, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 (hf a)
    refine (Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (Polynomial.separable_X_pow_sub_C (1 : k) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero).squarefree ?_).isFinitelySemisimple
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, f]
    rw [← map_pow, h1, map_one, sub_self]
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun a b _ => (hc a b).map _) fun a => Module.End.iSup_maxGenEigenspace_eq_top _
  simp only [fun a => (hss a).maxGenEigenspace_eq_eigenspace] at htop
  let S : Set (Fin n → k) := {v | ∃ d : ι → k, ∀ a, (X a).mulVec v = d a • v}
  have hS : Submodule.span k S = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun d v hv => Submodule.subset_span ⟨d, fun a => ?_⟩
    exact Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv a)
  obtain ⟨t, ht, hsp, hli⟩ := exists_linearIndependent k S
  let b₀ : Module.Basis t k (Fin n → k) := Module.Basis.mk hli (by rw [Subtype.range_coe, hsp, hS])
  let b := b₀.reindex (b₀.indexEquiv (Pi.basisFun k (Fin n)))
  have hb : ∀ i, b i ∈ S := fun i => by
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    exact ht (Subtype.coe_prop _)
  choose d hd using hb
  haveI := (Pi.basisFun k (Fin n)).invertibleToMatrix b
  refine ⟨unitOfInvertible ((Pi.basisFun k (Fin n)).toMatrix b), fun a i => d i a, fun a => ?_⟩
  ext i j
  have := congrFun (hd j a) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  change (X a * (Pi.basisFun k (Fin n)).toMatrix b) i j =
    ((Pi.basisFun k (Fin n)).toMatrix b * Matrix.diagonal (d · a)) i j
  rw [Matrix.mul_diagonal]
  simpa only [Matrix.mul_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr, mul_comm] using this

private theorem lev_diag {Γ A k : Type} [Group Γ] [CommGroup A] [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (H : Subgroup Γ) (φ : Γ →* A) (hφ : ∀ s, IsOfFinOrder (φ s))
    (hr : ∀ s ∈ H, φ s = 1 → r s = 1) :
    ∃ χ : Fin n → Γ →* kˣ, (∀ i s, φ s = 1 → χ i s = 1) ∧ Af.IsDiagOn r H χ := by
  obtain ⟨P, d, hP⟩ := lev_basis (fun s : H => (r s : Matrix (Fin n) (Fin n) k)) (fun a b => by
      have h := hr ((a : Γ) * b * ((b : Γ) * a)⁻¹) (mul_mem (mul_mem a.2 b.2) (inv_mem (mul_mem b.2 a.2))) (by
        rw [map_mul, map_inv, map_mul, map_mul, mul_comm (φ a), mul_inv_cancel])
      rw [map_mul, map_inv, mul_inv_eq_one, map_mul, map_mul] at h
      exact congrArg Units.val h) fun a => by
    obtain ⟨m, hm, h1⟩ := isOfFinOrder_iff_pow_eq_one.1 (hφ a)
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hr _ (pow_mem a.2 m) (by rw [map_pow, h1]), Units.val_one]
  have hd : ∀ s : H, ((P⁻¹ * r s * P : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.diagonal (d s) := fun s => by
    rw [Units.val_mul, Units.val_mul, mul_assoc, hP, Units.inv_mul_cancel_left]
  let κ : Fin n → H →* kˣ := fun i => MonoidHom.toHomUnits
    { toFun := fun s => d s i
      map_one' := by simpa using (congrFun (congrFun (hd 1) i) i).symm
      map_mul' := fun s t => by
        have h : (P⁻¹ * r (s * t : H) * P : GL (Fin n) k) = (P⁻¹ * r s * P) * (P⁻¹ * r t * P) := by
          rw [Subgroup.coe_mul, map_mul]
          group
        have h1 := hd (s * t)
        rw [h, Units.val_mul, hd, hd, Matrix.diagonal_mul_diagonal] at h1
        simpa using (congrFun (congrFun h1 i) i).symm }
  have hsurj := (φ.comp H.subtype).rangeRestrict_surjective
  have hker : ∀ i, (φ.comp H.subtype).rangeRestrict.ker ≤ (κ i).ker := fun i s hs => by
    have h1 := hd s
    rw [hr s s.2 (congrArg Subtype.val hs), mul_one, inv_mul_cancel] at h1
    apply Units.ext
    show d s i = 1
    simpa using (congrFun (congrFun h1 i) i).symm
  choose χ hχ using fun i => GlobalTheory.PrimaryCharacter.exists_extend_of_injective (φ.comp H.subtype).range.subtype
    (Subgroup.subtype_injective _) ((φ.comp H.subtype).rangeRestrict.liftOfSurjective hsurj ⟨κ i, hker i⟩)
  refine ⟨fun i => (χ i).comp φ, fun i s hs => by rw [MonoidHom.comp_apply, hs, map_one], P⁻¹, fun s hs => ?_⟩
  rw [inv_inv, hd ⟨s, hs⟩]
  congr 1
  funext i
  have h := hχ i ((φ.comp H.subtype).rangeRestrict ⟨s, hs⟩)
  rw [MonoidHom.liftOfRightInverse_comp_apply] at h
  exact (congrArg Units.val h).symm

private theorem lev_place {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {p : ℕ} (hp : p.Prime)
    {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    IsPlaceOver A w := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨p1, p2, p3, -⟩ := places ℚ Ω p A
  obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hA
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp)
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have e : v = w := HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((p3 v hv).1 hA))).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))
  exact e ▸ hv

open Matrix in
private theorem lev_dual {k : Type} [Field k] : ∃ P : GL (Fin 4) k, ∀ (ν : k) (X : M4 k), IsGSp ν X →
    Xᵀ * (P : M4 k) * X = ν • (P : M4 k) := by
  let J : M4 k := !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]
  have hJ : J * -J = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_four]
  refine ⟨⟨J, -J, hJ, by rw [neg_mul, ← mul_neg, hJ]⟩, fun ν X h => ?_⟩
  have h1 : Xᵀ * J = J * adj X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev]
  show Xᵀ * J * X = ν • J
  rw [h1, mul_assoc, h, Matrix.mul_smul, mul_one]

theorem UpperTheory.V.GradeZeroInterpolatingElement.level :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ N : ℕ, 1 ≤ N → Af.KillsMu N D.ψ → Af.KillsMu N D.ξ → Af.KillsMu N D.om → ∀ r, D.EPt r → Af.Level l N ![(D.e : ℤ) + 1, D.e, 1, 0] r.toHomUnits ∧ ∃ θ, Af.IsCycWt l ((D.e : ℤ) + 1) θ ∧ Af.DualTw r.toHomUnits θ ∧ ∀ g, (θ g : PadicAlgCl l) = ((D.th g : c.O) : PadicAlgCl l) := by
  intro Ω _ _ _ l hl c D hD N hN hψ hξ hom r hr
  obtain ⟨hmult, hunr, -, -, hP, -⟩ := ptIn D hD _ r hr
  have hcont := (eptInt D hD r hr).1
  let m : c.Oˣ →* (PadicAlgCl l)ˣ := Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom
  have hcyc : ∀ s : G ℚ Ω, GlobalTheory.GalOfCusp.cycBar ℚ Ω l s = m (chiO ℚ Ω l c.O s) := fun s => Units.ext rfl
  let χ₀ : Fin 4 → G ℚ Ω →* c.Oˣ := ![D.om⁻¹ * D.ξ * D.ψ, D.ψ, D.om⁻¹ * D.ξ, 1]
  have hχ₀ : ∀ i s, D.ψ s = 1 → D.ξ s = 1 → D.om s = 1 → χ₀ i s = 1 := fun i s h1 h2 h3 => by
    fin_cases i <;> simp [χ₀, h1, h2, h3]
  have hps : ∀ i s, D.ps i s = chiO ℚ Ω l c.O s ^ (![(D.e : ℤ) + 1, D.e, 1, 0] i) * χ₀ i s := fun i s => by
    fin_cases i <;> simp [χ₀, Raw.ps, Raw.th, Raw.al, Raw.Psi, Chr.Psi, zpow_add_one, mul_comm, mul_left_comm, mul_assoc]
  have hK : ∀ i, Af.KillsMu N (m.comp (χ₀ i)) := fun i s hs => by
    rw [MonoidHom.comp_apply, hχ₀ i s (hψ s hs) (hξ s hs) (hom s hs), map_one]
  refine ⟨⟨?_, fun w hw => ?_, fun w hw => ?_⟩, m.comp D.th, ⟨N, m.comp (χ₀ 0), hN, hK 0, ?_⟩, ?_, fun _ => rfl⟩
  · exact Units.continuous_iff.2 ⟨hcont, hcont.comp continuous_inv⟩
  · let φ := D.ψ.prod (D.ξ.prod D.om)
    have hφ : ∀ s, IsOfFinOrder (φ s) := fun s => by
      haveI : Finite (G ℚ Ω ⧸ D.ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hD.psi_open
      haveI : Finite (G ℚ Ω ⧸ D.ξ.ker) := Subgroup.quotient_finite_of_isOpen _ hD.xi_open
      refine IsOfFinOrder.prod_mk ?_ (IsOfFinOrder.prod_mk ?_ ?_)
      · exact (QuotientGroup.kerLift D.ψ).isOfFinOrder (isOfFinOrder_of_finite (s : G ℚ Ω ⧸ D.ψ.ker))
      · exact (QuotientGroup.kerLift D.ξ).isOfFinOrder (isOfFinOrder_of_finite (s : G ℚ Ω ⧸ D.ξ.ker))
      · exact isOfFinOrder_iff_pow_eq_one.2 ⟨l - 1, Nat.sub_pos_of_lt hl.out.one_lt, DFunLike.congr_fun hD.om_pow s⟩
    obtain ⟨A, hA, h⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∀ s ∈ Ine (F := ℚ) A, φ s = 1 → r s = 1 := by
      obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
      by_cases hT : Raw.Away D.T B
      · refine ⟨B, hB, fun s hs h1 => hunr B hT s hs ?_⟩
        have h2 : cycZ ℚ Ω l s = 1 := (places ℚ Ω l B).2.2.2 (hT l (Finset.mem_insert_self _ _)) hs
        have h3 : ∀ i, D.ps i s = 1 := fun i => by
          rw [hps, hχ₀ i s (congrArg Prod.fst h1) (congrArg (·.2.1) h1) (congrArg (·.2.2) h1), chiO, MonoidHom.comp_apply, h2,
            map_one, one_zpow, mul_one]
        have h4 : D.r0 s = 1 := by
          show Matrix.diagonal (fun i => (D.ps i s : c.O)) = 1
          simp only [h3, Units.val_one, Matrix.diagonal_one]
        show (residue c.O).mapMatrix (D.r0 s) = 1
        rw [h4, map_one]
      · have hExists : ∃ p ∈ D.T, B.valuation (p : Ω) < 1 := by
          by_contra! hn
          exact hT (fun p hp => not_lt_of_ge (hn p hp))
        obtain ⟨p, hp, hB'⟩ := hExists
        have hpw : (p : 𝓞 ℚ) ∈ w.asIdeal := (hB _).1 (by simpa only [map_natCast] using hB')
        have hpb : p ∈ D.Sb := (Finset.mem_insert.1 hp).resolve_left fun e => hw (e ▸ hpw)
        have hpp := ((facts D hD).1 p hpb).1
        exact ⟨D.pl p, lev_place hpp (hD.pl_over p hpp) hpw, fun s hs h1 =>
          (hP p hpb).2 ⟨s, hs.1⟩ ⟨hs, congrArg Prod.fst h1⟩⟩
    obtain ⟨χ, h1, h2⟩ := lev_diag r.toHomUnits (Ine (F := ℚ) A) φ hφ fun s hs e => Units.ext (h s hs e)
    exact ⟨A, hA, χ, fun i s hs => h1 i s (Prod.ext (hψ s hs) (Prod.ext (hξ s hs) (hom s hs))), h2⟩
  · obtain ⟨R, i1, i2, i3, ρ, y, hpt, rfl⟩ := hr
    obtain ⟨h, κ, hF, h1, -, -, -, h2⟩ := UpperTheory.V.Loc.spPtL D hD
      ((mapRep (y : R →+* PadicAlgCl l) ρ.hom).comp (D.Gp l).subtype)
      ⟨R, i1, i2, i3, D.loc ρ l, y, hpt.atL, rfl⟩
    refine ⟨D.pl l, lev_place hl.out (hD.pl_over l hl.out) hw, fun i => m.comp (χ₀ i), κ, hK, ⟨h⁻¹, fun s => ?_⟩,
      fun i s hs => ?_, Or.inl fun i j hij => ?_⟩
    · rw [inv_inv]
      exact hF s
    · have e : κ i s = m (D.ps i s) := Units.ext (h1 i s hs)
      rw [e, hps, map_mul, map_zpow, hcyc]
      rfl
    · by_cases e : i = j
      · subst e
        have h3 := DFunLike.congr_fun hij D.s0
        rw [MonoidHom.mul_apply, left_eq_mul] at h3
        have h4 : cycZ ℚ Ω l D.s0 = 1 := by
          refine Units.ext (Subtype.val_injective ((algebraMap ℚ_[l] (PadicAlgCl l)).injective ?_))
          exact (congrArg Units.val h3).trans (map_one _).symm
        exact hD.decompSigma_ord (h4 ▸ IsOfFinOrder.one)
      · obtain ⟨g, -, hg⟩ := h2 i j e ⊤ isOpen_univ
          ⟨⟨D.sg l, ((facts D hD).2.1 l (Finset.mem_insert_self _ _)).1⟩, trivial, rfl⟩
        exact hg (congrArg Units.val (DFunLike.congr_fun hij g))
  · ext s : 1
    have e : D.th s = _ := hps 0 s
    rw [MonoidHom.comp_apply, e, map_mul, map_zpow, ← hcyc]
    rfl
  · obtain ⟨P, hP⟩ := lev_dual (k := PadicAlgCl l)
    exact ⟨P, fun s => hP _ _ (hmult s)⟩
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem block_of_comm {K : Type} [NormedField K] [IsUltrametricDist K] (M X : M4 K) (d : Fin 4 → K)
    (hM : ∀ i j, ‖M i j - Matrix.diagonal d i j‖ < 1) (hd : ∀ i j, lamW i ≠ lamW j → ‖d i - d j‖ = 1)
    (hb : IsBlock M) (hX : IsBlock (X * M - M * X)) : IsBlock X := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 4 × Fin 4))
    (fun p => ‖M p.1 p.2 - Matrix.diagonal d p.1 p.2‖) Finset.univ_nonempty
  obtain ⟨⟨i, j⟩, hq, hm⟩ := Finset.exists_max_image
    (Finset.univ.filter fun q : Fin 4 × Fin 4 => lamW q.1 ≠ lamW q.2) (fun q => ‖X q.1 q.2‖) ⟨(0, 1), by decide⟩
  have hij : lamW i ≠ lamW j := (Finset.mem_filter.1 hq).2
  have hm' : ∀ a b, lamW a ≠ lamW b → ‖X a b‖ ≤ ‖X i j‖ := fun a b h =>
    hm (a, b) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  set ρ := ‖M p.1 p.2 - Matrix.diagonal d p.1 p.2‖ with hρ
  have hρ1 : ρ < 1 := hM _ _
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  obtain ⟨N, hN⟩ : ∃ N, N = M - Matrix.diagonal d := ⟨_, rfl⟩
  have hNρ : ∀ a b, ‖N a b‖ ≤ ρ := fun a b => by
    rw [hN]; exact hp (a, b) (Finset.mem_univ _)
  have hNb : IsBlock N := fun a b h => by
    have : a ≠ b := fun e => h (by rw [e])
    rw [hN, Matrix.sub_apply, hb a b h, Matrix.diagonal_apply_ne _ this, sub_zero]
  have hMN : M = N + Matrix.diagonal d := by rw [hN, sub_add_cancel]
  have h0 := hX i j hij
  rw [hMN, mul_add, add_mul] at h0
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] at h0
  have h1 : X i j * (d i - d j) = (X * N) i j + -(N * X) i j := by linear_combination -h0
  have hx0 := norm_nonneg (X i j)
  have h2 : ‖(X * N) i j‖ ≤ ‖X i j‖ * ρ := by
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    by_cases hk : lamW k = lamW j
    · rw [norm_mul]
      exact mul_le_mul (hm' i k (by rw [hk]; exact hij)) (hNρ _ _) (norm_nonneg _) hx0
    · rw [hNb k j hk, mul_zero, norm_zero]; positivity
  have h3 : ‖-(N * X) i j‖ ≤ ‖X i j‖ * ρ := by
    rw [norm_neg, Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    by_cases hk : lamW i = lamW k
    · rw [norm_mul, mul_comm]
      exact mul_le_mul (hm' k j (by rw [← hk]; exact hij)) (hNρ _ _) (norm_nonneg _) hx0
    · rw [hNb i k hk, zero_mul, norm_zero]; positivity
  have h4 : ‖X i j‖ ≤ ‖X i j‖ * ρ := by
    calc ‖X i j‖ = ‖X i j * (d i - d j)‖ := by rw [norm_mul, hd i j hij, mul_one]
      _ ≤ _ := by rw [h1]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 h3)
  have h5 : ‖X i j‖ ≤ 0 := by nlinarith
  intro a b h
  exact norm_le_zero_iff.1 ((hm' a b h).trans h5)

private theorem diag_of_comm {K : Type} [Field K] (X h : M4 K) (hX : X ∈ sp4 K) (hb : IsBlock X)
    (h02 : h 0 2 = 0) (h20 : h 2 0 = 0) (hne : h 0 0 ≠ h 2 2)
    (c02 : (X * h - h * X) 0 2 = 0) (c20 : (X * h - h * X) 2 0 = 0) :
    ∃ a b : K, ∀ (Y : M4 K) i j, (X * Y - Y * X) i j = (a * ((wt i j).1 : K) + b * ((wt i j).2 : K)) * Y i j := by
  have hs : ∀ i j, (sgn i * sgn j) • X j.rev i.rev = -X i j := fun i j => congrFun (congrFun hX i) j
  have z01 := hb 0 1 (by decide)
  have z03 := hb 0 3 (by decide)
  have z10 := hb 1 0 (by decide)
  have z12 := hb 1 2 (by decide)
  have z21 := hb 2 1 (by decide)
  have z23 := hb 2 3 (by decide)
  have z30 := hb 3 0 (by decide)
  have z32 := hb 3 2 (by decide)
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_four, z01, z03, z10, z12, z21, z23, z30, z32, h02, h20] at c02 c20
  have z02 : X 0 2 = 0 := by
    have : X 0 2 * (h 0 0 - h 2 2) = 0 := by linear_combination -c02
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have z20 : X 2 0 = 0 := by
    have : X 2 0 * (h 0 0 - h 2 2) = 0 := by linear_combination c20
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)
  have z13 : X 1 3 = 0 := by simpa [sgn, Fin.rev, z02] using hs 0 2
  have z31 : X 3 1 = 0 := by simpa [sgn, Fin.rev, z20] using hs 2 0
  have z33 : X 3 3 = -X 0 0 := by simpa [sgn, Fin.rev] using hs 0 0
  have z22 : X 2 2 = -X 1 1 := by simpa [sgn, Fin.rev] using hs 1 1
  refine ⟨X 0 0 - X 1 1, X 0 0 + X 1 1, fun Y i j => ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, z01, z03, z10, z12, z21, z23, z30, z32, z02, z20, z13, z31, z33, z22, wt, lamW, muW] <;> ring

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem norm_le_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) : ‖algebraMap c.O (PadicAlgCl l) x‖ ≤ 1 := by
  have : Module.Finite ℤ_[l] c.O := c.fin
  exact norm_le_one_of_int l _ ((IsIntegral.of_finite ℤ_[l] x).map c.O.val)

private theorem norm_eq_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) (hx : residue c.O x ≠ 0) :
    ‖algebraMap c.O (PadicAlgCl l) x‖ = 1 := by
  obtain ⟨u, rfl⟩ := (residue_ne_zero_iff_isUnit x).1 hx
  have h1 : ‖algebraMap c.O (PadicAlgCl l) u‖ * ‖algebraMap c.O (PadicAlgCl l) (u⁻¹ : c.Oˣ)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  have h2 := norm_le_one c u
  have h3 := norm_le_one c (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg (algebraMap c.O (PadicAlgCl l) u)
  nlinarith

theorem UpperTheory.V.GradeZeroInterpolatingElement.rigidDiag :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r, D.EPt r → D.RigidAt r → ∀ r' : G ℚ Ω →* M4 (DualNumber (PadicAlgCl l)), D.PtIn _ r' → (∀ g i j, (r' g i j).fst = r g i j) → ∃ a b : PadicAlgCl l, ∀ g i j, (r' g i j).snd = (a * ((wt i j).1 : PadicAlgCl l) + b * ((wt i j).2 : PadicAlgCl l)) * r g i j := by
  intro Ω _ _ _ l _ c D hD r hr hrig r' hr' hfst
  obtain ⟨X, hX, hsnd⟩ := hrig r' hr' hfst
  obtain ⟨-, hcl, -⟩ := eptInt D hD r hr
  obtain ⟨-, -, ⟨hb, h02, h20⟩, -⟩ := ptIn D hD _ r hr
  obtain ⟨-, -, ⟨hb', h02', h20'⟩, -⟩ := ptIn D hD _ r' hr'
  obtain ⟨-, hsg, -, -, -, -, -, -, -, hph, -⟩ := facts D hD
  have hr0 : ∀ g, D.r0E g = Matrix.diagonal fun i => algebraMap c.O (PadicAlgCl l) (D.ps i g) := fun g => by
    ext i j
    show algebraMap c.O (PadicAlgCl l) (Matrix.diagonal (fun i => (D.ps i g : c.O)) i j) = _
    by_cases h : i = j
    · subst h; simp only [Matrix.diagonal_apply_eq]
    · simp only [Matrix.diagonal_apply_ne _ h, map_zero]
  have hbar : ∀ i, Raw.bar (D.ps i) D.ph = Raw.bar (D.ps i) (D.sg l) := fun i => by
    have := congrFun (congrFun hph i) i
    change residue c.O (Matrix.diagonal (fun i => (D.ps i D.ph : c.O)) i i) =
      residue c.O (Matrix.diagonal (fun i => (D.ps i (D.sg l) : c.O)) i i) at this
    simpa only [Matrix.diagonal_apply_eq] using this
  have hXb : IsBlock X := by
    refine block_of_comm (r D.ph) X (fun i => algebraMap c.O (PadicAlgCl l) (D.ps i D.ph))
      (fun i j => by rw [← hr0]; exact hcl _ i j) (fun i j h => ?_) hb fun i j h => ?_
    · rw [← map_sub]
      refine norm_eq_one c _ ?_
      rw [map_sub, sub_ne_zero]
      have := (hsg l (Finset.mem_insert_self _ _)).2.2 i j h
      rwa [← hbar, ← hbar] at this
    · rw [← hsnd, hb' i j h]; rfl
  have hh : ∀ i j, (D.hEl r' i j).snd = (X * D.hEl r - D.hEl r * X) i j := fun i j => by
    have e : X * D.hEl r - D.hEl r * X = (X * r D.g0 - r D.g0 * X) +
        algebraMap c.O (PadicAlgCl l) (D.th D.g0) • (X * r D.g0⁻¹ - r D.g0⁻¹ * X) := by
      simp only [Raw.hEl, mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      abel
    rw [e, Matrix.add_apply, Matrix.smul_apply, ← hsnd, ← hsnd, Raw.hEl, Matrix.add_apply, Matrix.smul_apply,
      TrivSqZeroExt.snd_add, smul_eq_mul, smul_eq_mul, ← Algebra.smul_def, ← Algebra.smul_def]
    rfl
  have hne : D.hEl r 0 0 ≠ D.hEl r 2 2 := by
    intro he
    have hi : ∀ i, ‖D.hEl r i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0 + D.th D.g0 * D.ps i D.g0⁻¹)‖ < 1 := fun i => by
      have a1 := hcl D.g0 i i
      have a2 := hcl D.g0⁻¹ i i
      rw [hr0, Matrix.diagonal_apply_eq] at a1 a2
      have e : D.hEl r i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0 + D.th D.g0 * D.ps i D.g0⁻¹) =
          (r D.g0 i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0)) + algebraMap c.O (PadicAlgCl l) (D.th D.g0) *
            (r D.g0⁻¹ i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0⁻¹)) := by
        rw [Raw.hEl, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt a1 ?_)
      rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one c _) (norm_nonneg _) a2
    have e : ((D.al D.g0 : c.O) - 1) * ((D.Psi D.g0 : c.O) - 1) =
        (D.ps 0 D.g0 + D.th D.g0 * D.ps 0 D.g0⁻¹) - (D.ps 2 D.g0 + D.th D.g0 * D.ps 2 D.g0⁻¹) := by
      have p0 : D.ps 0 = D.th := rfl
      have p2 : D.ps 2 = D.al := rfl
      have t : (D.th D.g0 : c.O) = D.al D.g0 * D.Psi D.g0 := rfl
      have u1 : (D.th D.g0 : c.O) * D.th D.g0⁻¹ = 1 := by rw [map_inv, Units.mul_inv]
      have u2 : (D.al D.g0 : c.O) * D.al D.g0⁻¹ = 1 := by rw [map_inv, Units.mul_inv]
      rw [p0, p2, u1, t]
      linear_combination (D.Psi D.g0 : c.O) * u2
    have n1 : ‖algebraMap c.O (PadicAlgCl l) (((D.al D.g0 : c.O) - 1) * ((D.Psi D.g0 : c.O) - 1))‖ = 1 := by
      refine norm_eq_one c _ ?_
      rw [map_mul, map_sub, map_sub, map_one]
      exact mul_ne_zero (sub_ne_zero.2 hD.genElt_alpha) (sub_ne_zero.2 hD.genElt_Psi)
    rw [e, map_sub] at n1
    have a1 := hi 0
    have a2 := hi 2
    rw [← he] at a2
    rw [← norm_neg] at a1
    have a3 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt a1 a2)
    rw [neg_sub, sub_add_sub_cancel, n1] at a3
    exact lt_irrefl _ a3
  obtain ⟨a, b, hab⟩ := diag_of_comm X (D.hEl r) hX hXb h02 h20 hne (by rw [← hh, h02']; rfl) (by rw [← hh, h20']; rfl)
  exact ⟨a, b, fun g i j => by rw [hsnd, hab]⟩
end
